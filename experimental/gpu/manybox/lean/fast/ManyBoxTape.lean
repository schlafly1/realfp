import ManyBoxFast

/-! C batch checker for manybox certificates.

`checkHex fe upper c d hex env` is, by definition, realfp-checkable `checkC3` on the decoded
certificate (`ManyBox.checkHex_eq`). Natively it is `@[implemented_by checkHexImpl]`: the
expression is compiled once to a flat tape and the whole tree walk (decode + per-leaf interval
evaluation + goal test) runs in C (`c/mbtape.c`, extern `mb_check_tape`), calling realfp's own
directed-rounding kernels `iv64_dir_*`. Same attach pattern as realfp's Bernstein checker
(`checkGeB` / `checkGeBImpl` / `iv64_bern_check`). Expressions with other nodes (div, sqrt,
transcendental), or arguments outside the C path's range, fall back to `checkC3`.

Trust: under `native_decide`, `mb_check_tape` is trusted to compute the spec. -/

open Interval64 Interval64.KF

namespace ManyBox

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

/-- Flat tape (12 bytes per instruction) and constant pool, or `none` if unsupported. -/
def toTape (fe : FExpr) : Option (ByteArray × FloatArray) :=
  match (tapeAux fe).run (#[], #[]) with
  | some (_, (code, ks)) =>
      if code.size ≤ 3 * 4096 then
        some (code.foldl u32le ByteArray.empty, ⟨ks⟩)
      else none
  | none => none

def boxFA (env : List Interval64) : FloatArray :=
  ⟨(env.flatMap fun X => [X.lo, X.hi]).toArray⟩

/-- The C runtime (`c/mbtape.c`). -/
@[extern "mb_check_tape"]
opaque checkTapeExt (code : @& ByteArray) (ks : @& FloatArray) (upper : UInt8) (c : UInt64)
  (d : UInt32) (hex : @& String) (box : @& FloatArray) : Bool

def checkHexSpec [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkC3 fe (if upper then gLe c else gGe c) (decodeCertC d hex) env

def checkHexImpl [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  match toTape fe with
  | some (code, ks) =>
      if env.length == d && 0 < d && d ≤ 16 && c < 2 ^ 64 then
        checkTapeExt code ks (if upper then 1 else 0) c.toUInt64 d.toUInt32 hex (boxFA env)
      else checkHexSpec fe upper c d hex env
  | none => checkHexSpec fe upper c d hex env

/-- Certificate check, `upper`: `f ≤ c` (`gLe`), else `c ≤ f` (`gGe`). -/
@[implemented_by checkHexImpl]
def checkHex [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkHexSpec fe upper c d hex env

theorem checkHex_le [ExtTbl] (fe : FExpr) (c d : Nat) (hex : String) (env : List Interval64) :
    checkHex fe true c d hex env = checkC3 fe (gLe c) (decodeCertC d hex) env := rfl

theorem checkHex_ge [ExtTbl] (fe : FExpr) (c d : Nat) (hex : String) (env : List Interval64) :
    checkHex fe false c d hex env = checkC3 fe (gGe c) (decodeCertC d hex) env := rfl

/-! ### Sub-tree checks: a certificate split into independent sub-boxes

`checkHexAt … l0 cs0 hex env` checks the subtree that `decC` decodes when started at depth
`l0` with integer box coordinates `cs0` (the GPU's coordinates of a sub-box). A big
certificate is split into a small top tree (`Top`, explicit split points) whose leaves are
such sub-checks; each sub-check can be its own `native_decide` theorem (own file, own process),
and `Top.sound` glues them into realfp's `checkC2` on the whole box. -/

def decodeCertAt (d l0 : Nat) (cs0 : List Nat) (hex : String) : Cert :=
  (decC d hex.toUTF8 l0 cs0.toArray 0).1

def u64le (b : ByteArray) (x : UInt64) : ByteArray := Id.run do
  let mut b := b
  for k in [0:8] do b := b.push (x >>> (8 * k).toUInt64).toUInt8
  return b

def csBytes (cs : List Nat) : ByteArray := cs.foldl (fun b c => u64le b c.toUInt64) ByteArray.empty

/-- The C runtime for sub-trees (`c/mbtape.c`). -/
@[extern "mb_check_tape_at"]
opaque checkTapeAtExt (code : @& ByteArray) (ks : @& FloatArray) (upper : UInt8) (c : UInt64)
  (d : UInt32) (l0 : UInt32) (cs0 : @& ByteArray) (hex : @& String) (box : @& FloatArray) : Bool

def checkHexAtSpec [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (cs0 : List Nat)
    (hex : String) (env : List Interval64) : Bool :=
  checkC3 fe (if upper then gLe c else gGe c) (decodeCertAt d l0 cs0 hex) env

def checkHexAtImpl [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (cs0 : List Nat)
    (hex : String) (env : List Interval64) : Bool :=
  match toTape fe with
  | some (code, ks) =>
      if env.length == d && cs0.length == d && 0 < d && d ≤ 16 && c < 2 ^ 64 && l0 < 2 ^ 20 &&
          cs0.all (· < 2 ^ 64) then
        checkTapeAtExt code ks (if upper then 1 else 0) c.toUInt64 d.toUInt32 l0.toUInt32
          (csBytes cs0) hex (boxFA env)
      else checkHexAtSpec fe upper c d l0 cs0 hex env
  | none => checkHexAtSpec fe upper c d l0 cs0 hex env

@[implemented_by checkHexAtImpl]
def checkHexAt [ExtTbl] (fe : FExpr) (upper : Bool) (c d l0 : Nat) (cs0 : List Nat)
    (hex : String) (env : List Interval64) : Bool :=
  checkHexAtSpec fe upper c d l0 cs0 hex env

/-- One sub-check: subtree start depth and coordinates, its hex, its box (bit patterns). -/
structure Job where
  l0 : Nat
  cs0 : List Nat
  hex : String
  env : List KI

/-- The top of a split certificate: explicit splits (`m` = binary64 bits of the split point),
    with sub-checks at the leaves (a box proved directly is a sub-check with `hex = "0"`). -/
inductive Top where
  | sub (l0 : Nat) (cs0 : List Nat) (hex : String)
  | split (i m : Nat) (l r : Top)

def Top.toCert (d : Nat) : Top → Cert
  | .sub l0 cs0 hex => decodeCertAt d l0 cs0 hex
  | .split i m l r => .split i m (l.toCert d) (r.toCert d)

/-- The split-point tests of `checkK` at the top (pure `Nat`; the kernel evaluates this). -/
def Top.midsOK : Top → Bool
  | .sub _ _ _ => true
  | .split _ m l r => !isNaN m && Nat.blt m (2 ^ 64) && l.midsOK && r.midsOK

/-- The sub-checks with their boxes, in order (pure `Nat`; the kernel evaluates this). -/
def Top.jobs : Top → List KI → List Job
  | .sub l0 cs0 hex, env => [⟨l0, cs0, hex, env⟩]
  | .split i m l r, env =>
    l.jobs (env.set i ⟨(env.getD i zeroK).lo, m⟩) ++ r.jobs (env.set i ⟨m, (env.getD i zeroK).hi⟩)

def Job.check [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (j : Job) : Bool :=
  checkHexAt fe upper c d j.l0 j.cs0 j.hex (j.env.map toIC)

theorem Top.sound [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) :
    ∀ (t : Top) (env : List KI), t.midsOK = true →
      (t.jobs env).all (Job.check fe upper c d) = true →
      checkC2 fe (if upper then gLe c else gGe c) (t.toCert d) env = true := by
  intro t
  induction t with
  | sub l0 cs0 hex =>
    intro env _ h
    simp only [Top.jobs, List.all_cons, List.all_nil, Bool.and_true, Job.check, checkHexAt,
      checkHexAtSpec] at h
    simpa only [Top.toCert, ← checkC3_map] using h
  | split i m l r ihl ihr =>
    intro env hm h
    simp only [Top.midsOK, Bool.and_eq_true] at hm
    simp only [Top.jobs, List.all_append, Bool.and_eq_true] at h
    simp only [Top.toCert, checkC2, hm.1.1.1, hm.1.1.2, ihl _ hm.1.2 h.1, ihr _ hm.2 h.2,
      Bool.and_self]

open Lean Elab Term in
/-- `mb_hex% "file"`: the hex line of a certificate file as a string literal (path relative to
the current file); Mathlib-free twin of `mb_cert%`. -/
elab "mb_hex% " p:str : term => do
  let dir := (← getFileName) |> System.FilePath.mk |>.parent |>.getD "."
  let txt ← IO.FS.readFile (dir / p.getString)
  let line := (txt.splitOn "\n").filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""
  return mkStrLit line

end ManyBox
