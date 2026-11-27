import RealFPGridNative.Basic

/-! # RealFP.Grid: the C batch checker and split certificates (Mathlib-free, precompiled)

`checkGrid fe upper c d l0 hex env` is, by definition, `checkC3` on `decodeGrid d l0 hex env`
(`checkGrid_eq`, `rfl`). Natively it is `@[implemented_by checkGridImpl]`: the expression is
compiled once to a flat tape and the whole tree walk (decode + interval evaluation of every leaf
+ goal test) runs in C (`c/grid_tape.c`, extern `rfg_check`, multithreaded with pthreads),
calling realfp's own directed-rounding kernels `iv64_dir_*`. Expressions with other nodes
(transcendental functions, `abs`, …) or arguments outside the C path's range fall back to the
compiled Lean specification (correct, about 100× slower).

Trust: under `native_decide`, `rfg_check` is trusted to compute the specification.

Split certificates: a big certificate is a small top tree (`Top`, explicit split points) whose
leaves are sub-checks (`Job`); `Top.sound` / `Top.soundP` glue `native_decide` proofs of the
sub-checks into `checkC2` on the whole box. `TopC` does the same one level up (leaves are any
certificates), for proofs spread over many files. -/

open Interval64 Interval64.KF

namespace RealFP.Grid

/-- Tape opcodes: 0 var, 1 const, 2 add, 3 sub, 4 mul, 5 neg, 6 pow, 7 div, 8 sqrt. -/
abbrev TapeSt := Array UInt32 × Array Float

def emit (op a b : Nat) : StateT TapeSt Option Nat := do
  let (code, ks) ← get
  if a < 2 ^ 32 ∧ b < 2 ^ 32 then
    set (code.push op.toUInt32 |>.push a.toUInt32 |>.push b.toUInt32, ks)
    return code.size / 3
  else failure

def tapeAux : FExpr → StateT TapeSt Option Nat
  | .var i => emit 0 i 0
  | .const I => do
      let (code, ks) ← get
      set (code, ks.push I.lo |>.push I.hi)
      emit 1 (ks.size / 2) 0
  | .add a b => do let x ← tapeAux a; let y ← tapeAux b; emit 2 x y
  | .sub a b => do let x ← tapeAux a; let y ← tapeAux b; emit 3 x y
  | .mul a b => do let x ← tapeAux a; let y ← tapeAux b; emit 4 x y
  | .neg a => do let x ← tapeAux a; emit 5 x 0
  | .pow a n => do let x ← tapeAux a; emit 6 x n
  | .div a b => do let x ← tapeAux a; let y ← tapeAux b; emit 7 x y
  | .sqrt a => do let x ← tapeAux a; emit 8 x 0
  | _ => failure

def u32le (b : ByteArray) (x : UInt32) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

/-- The instructions `(op, a, b)` and the constant pool (lo, hi pairs), or `none` if the
expression has an operation the C checker does not implement (or more than 4096 nodes). -/
def tapeOf (fe : FExpr) : Option (Array UInt32 × Array Float) :=
  match (tapeAux fe).run (#[], #[]) with
  | some (_, (code, ks)) => if code.size ≤ 3 * 4096 then some (code, ks) else none
  | none => none

/-- Flat tape (12 bytes per instruction, little-endian) and constant pool. -/
def toTape (fe : FExpr) : Option (ByteArray × FloatArray) :=
  (tapeOf fe).map fun (code, ks) => (code.foldl u32le ByteArray.empty, ⟨ks⟩)

def boxFA (env : List Interval64) : FloatArray :=
  ⟨(env.flatMap fun X => [X.lo, X.hi]).toArray⟩

/-- A 64-bit pattern as 16 hex digits. -/
def hex16 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 (n % 2 ^ 64))
  "".pushn '0' (16 - s.length) ++ s

/-- The problem file read by the `realfp-grid` tool (`grid/src/problem.cpp`): the box, the goal
`f ≤ c` (`upper`) or `c ≤ f` with `c` given by its bits, and the tape. `none` if the expression
has no tape (an operation the tool and the C checker do not implement). -/
def problemText (fe : FExpr) (upper : Bool) (c : Nat) (env : List Interval64) : Option String :=
  (tapeOf fe).map fun (code, ks) => Id.run do
    let mut s := "realfp-grid-problem 1\n"
    s := s ++ s!"d {env.length}\n"
    for X in env do
      s := s ++ s!"box {hex16 X.lo.toBits.toNat} {hex16 X.hi.toBits.toNat}\n"
    s := s ++ s!"goal {if upper then "le" else "ge"} {hex16 c}\n"
    s := s ++ s!"consts {ks.size / 2}\n"
    for i in [0:ks.size / 2] do
      s := s ++ s!"{hex16 ks[2 * i]!.toBits.toNat} {hex16 ks[2 * i + 1]!.toBits.toNat}\n"
    s := s ++ s!"tape {code.size / 3}\n"
    for i in [0:code.size / 3] do
      s := s ++ s!"{code[3 * i]!} {code[3 * i + 1]!} {code[3 * i + 2]!}\n"
    return s

/-- The C runtime (`c/grid_tape.c`). -/
@[extern "rfg_check"]
opaque checkTapeExt (code : @& ByteArray) (ks : @& FloatArray) (upper : UInt8) (c : UInt64)
  (d : UInt32) (l0 : UInt32) (hex : @& String) (box : @& FloatArray) : Bool

def checkGridSpec [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkC3 fe (if upper then gLe c else gGe c) (decodeGrid d l0 hex env) env

def checkGridImpl [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  match toTape fe with
  | some (code, ks) =>
      if env.length == d && 0 < d && d ≤ 16 && c < 2 ^ 64 && l0 < 2 ^ 20 then
        checkTapeExt code ks (if upper then 1 else 0) c.toUInt64 d.toUInt32 l0.toUInt32 hex
          (boxFA env)
      else checkGridSpec fe upper c d l0 hex env
  | none => checkGridSpec fe upper c d l0 hex env

/-- Certificate check of the (sub)tree `hex` rooted at depth `l0` on the box `env`:
`upper`: `f ≤ c` (`gLe`), else `c ≤ f` (`gGe`); `c` = bits of the bound. -/
@[implemented_by checkGridImpl]
def checkGrid [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkGridSpec fe upper c d l0 hex env

theorem checkGrid_eq [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (hex : String)
    (env : List Interval64) :
    checkGrid fe upper c d l0 hex env =
      checkC3 fe (if upper then gLe c else gGe c) (decodeGrid d l0 hex env) env := rfl

/-! ### Split certificates -/

/-- `P` holds for every element (by recursion, so an explicit list unfolds to `∧`s). -/
def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ AllP P xs

theorem AllP_append {α : Type} (P : α → Prop) :
    ∀ (a b : List α), AllP P (a ++ b) ↔ AllP P a ∧ AllP P b
  | [], b => by simp [AllP]
  | x :: a, b => by simp only [List.cons_append, AllP, AllP_append P a b, and_assoc]

/-- One sub-check: subtree start depth, its hex, its box (bit patterns). -/
structure Job where
  l0 : Nat
  hex : String
  env : List KI

/-- The top of a split certificate: explicit splits (`m` = binary64 bits of the split point),
with sub-checks at the leaves (a box proved directly is a sub-check with `hex = "0"`). -/
inductive Top where
  | sub (l0 : Nat) (hex : String)
  | split (i m : Nat) (l r : Top)

def Top.toCert (d : Nat) : Top → List KI → Cert
  | .sub l0 hex, env => decodeGrid d l0 hex (env.map toIC)
  | .split i m l r, env =>
    .split i m (l.toCert d (env.set i ⟨(env.getD i zeroK).lo, m⟩))
      (r.toCert d (env.set i ⟨m, (env.getD i zeroK).hi⟩))

/-- The split-point tests of `checkK` at the top (pure `Nat`; the kernel evaluates this). -/
def Top.midsOK : Top → Bool
  | .sub _ _ => true
  | .split _ m l r => !isNaN m && Nat.blt m (2 ^ 64) && l.midsOK && r.midsOK

/-- The sub-checks with their boxes, in order (pure `Nat`; the kernel evaluates this). -/
def Top.jobs : Top → List KI → List Job
  | .sub l0 hex, env => [⟨l0, hex, env⟩]
  | .split i m l r, env =>
    l.jobs (env.set i ⟨(env.getD i zeroK).lo, m⟩) ++ r.jobs (env.set i ⟨m, (env.getD i zeroK).hi⟩)

def Job.check [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (j : Job) : Bool :=
  checkGrid fe upper c d j.l0 j.hex (j.env.map toIC)

theorem Top.soundP [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) :
    ∀ (t : Top) (env : List KI), t.midsOK = true →
      AllP (fun j => Job.check fe upper c d j = true) (t.jobs env) →
      checkC2 fe (if upper then gLe c else gGe c) (t.toCert d env) env = true := by
  intro t
  induction t with
  | sub l0 hex =>
    intro env _ h
    have h1 := h.1
    simp only [Job.check, checkGrid_eq] at h1
    simpa only [Top.toCert, ← checkC3_map] using h1
  | split i m l r ihl ihr =>
    intro env hm h
    simp only [Top.midsOK, Bool.and_eq_true] at hm
    simp only [Top.jobs] at h
    rw [AllP_append] at h
    simp only [Top.toCert, checkC2, hm.1.1.1, hm.1.1.2, ihl _ hm.1.2 h.1, ihr _ hm.2 h.2,
      Bool.and_self]

theorem AllP_of_all {α : Type} (p : α → Bool) : ∀ (l : List α), l.all p = true → AllP (fun x => p x = true) l
  | [], _ => trivial
  | x :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨h.1, AllP_of_all p xs h.2⟩

/-- `Top.soundP` with the sub-checks as one `List.all` (one `native_decide` per file). -/
theorem Top.sound [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (t : Top) (env : List KI)
    (hm : t.midsOK = true) (hj : (t.jobs env).all (Job.check fe upper c d) = true) :
    checkC2 fe (if upper then gLe c else gGe c) (t.toCert d env) env = true :=
  Top.soundP fe upper c d t env hm (AllP_of_all _ _ hj)

/-- Two-level split: a top tree whose leaves are arbitrary certificates. -/
inductive TopC where
  | leaf (c : Cert)
  | split (i m : Nat) (l r : TopC)

def TopC.toCert : TopC → Cert
  | .leaf c => c
  | .split i m l r => .split i m l.toCert r.toCert

def TopC.midsOK : TopC → Bool
  | .leaf _ => true
  | .split _ m l r => !isNaN m && Nat.blt m (2 ^ 64) && l.midsOK && r.midsOK

def TopC.leaves : TopC → List KI → List (Cert × List KI)
  | .leaf c, env => [(c, env)]
  | .split i m l r, env =>
    l.leaves (env.set i ⟨(env.getD i zeroK).lo, m⟩) ++ r.leaves (env.set i ⟨m, (env.getD i zeroK).hi⟩)

theorem TopC.sound [ExtTbl] (fe : FExpr) (g : KI → Bool) :
    ∀ (t : TopC) (env : List KI), t.midsOK = true →
      AllP (fun p => checkC2 fe g p.1 p.2 = true) (t.leaves env) →
      checkC2 fe g t.toCert env = true := by
  intro t
  induction t with
  | leaf c => intro env _ h; exact h.1
  | split i m l r ihl ihr =>
    intro env hm h
    simp only [TopC.midsOK, Bool.and_eq_true] at hm
    simp only [TopC.leaves] at h
    rw [AllP_append] at h
    simp only [TopC.toCert, checkC2, hm.1.1.1, hm.1.1.2, ihl _ hm.1.2 h.1, ihr _ hm.2 h.2,
      Bool.and_self]

open Lean Elab Term in
/-- `grid_hex% "file"`: the hex line of a certificate file (the first line that is not empty and
does not start with `#`), as a string literal; the path is relative to the current file. -/
elab "grid_hex% " p:str : term => do
  let dir := (← getFileName) |> System.FilePath.mk |>.parent |>.getD "."
  let txt ← IO.FS.readFile (dir / p.getString)
  let line := (txt.splitOn "\n").filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""
  return mkStrLit line

end RealFP.Grid
