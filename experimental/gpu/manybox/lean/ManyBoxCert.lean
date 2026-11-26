import RealFPMathlib

/-! Shared part of the manybox Lean check (see `../README.md`).

A manybox certificate is the preorder bit string of the GPU's bisection tree (1 = split,
0 = leaf) in hex. `decodeCert d s` rebuilds realfp's bisection certificate `Cert` from it:
the box at depth `l` is split in variable `l mod d` at its midpoint
`-1 + (2c+1) 2^-s` (exact, `s` = number of earlier splits of that variable).

Nothing here is trusted: `checkK` (realfp's kernel-level checker) re-evaluates every leaf, and
`RealFP.prove_le` / `prove_ge` turn `checkK … = true` into the real-number theorem. A wrong
split point or a wrong bit only makes the check fail. -/
open Lean Elab Term Meta
open Interval64.KF

namespace ManyBox

/-- Hex digit value (non-hex characters count as 0). -/
@[inline] def hexVal (b : UInt8) : Nat :=
  if b ≥ 48 && b ≤ 57 then (b - 48).toNat
  else if b ≥ 97 && b ≤ 102 then (b - 87).toNat else 0

/-- Bit `i` of the hex string (most significant bit of each digit first). -/
@[inline] def bitAt (s : ByteArray) (i : Nat) : Bool :=
  (hexVal (s.get! (i / 4))).testBit (3 - i % 4)

/-- Midpoint `-1 + (2c+1) 2^-s` as binary64 bits (exact for `s ≤ 52`). -/
def midBits (c s : Nat) : Nat :=
  ((-1 : Float) + (2 * c + 1).toFloat * Float.scaleB 1 (-(s : Int))).toBits.toNat

/-- Preorder decoding. `cs` = integer coordinates of the current box, `l` its depth,
`pos` the next bit. Returns the subtree and the next position. -/
partial def dec (d : Nat) (s : ByteArray) (l : Nat) (cs : Array Nat) (pos : Nat) : Cert × Nat :=
  if !bitAt s pos then (.leaf, pos + 1)
  else
    let i := l % d
    let sp := (l + d - 1 - i) / d
    let c := cs[i]!
    let (L, p1) := dec d s (l + 1) (cs.set! i (2 * c)) (pos + 1)
    let (R, p2) := dec d s (l + 1) (cs.set! i (2 * c + 1)) p1
    (.split i (midBits c sp) L R, p2)

/-- Certificate from the hex preorder string of a `d`-dimensional manybox run on `[-1,1]^d`. -/
def decodeCert (d : Nat) (hex : String) : Cert :=
  (dec d hex.toUTF8 0 (Array.replicate d 0) 0).1

/-- `mb_cert% "file"`: the hex line of a certificate file, as a string literal
(path relative to this directory). -/
elab "mb_cert% " p:str : term => do
  let dir := (← getFileName) |> System.FilePath.mk |>.parent |>.getD "."
  let txt ← IO.FS.readFile (dir / p.getString)
  let line := (txt.splitOn "\n").filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""
  return mkStrLit line

/-! ### The two problems as `IExpr`s (same operation order as `../mbexpr.h`) -/

def x2 (i : Nat) : IExpr := .pow (.var i) 2
/-- `T8` in Horner form in `u = x^2`: `(((128 u - 256) u + 160) u - 32) u + 1`. -/
def t8 (i : Nat) : IExpr :=
  .add (.mul (.sub (.mul (.add (.mul (.sub (.mul (.rat 128) (x2 i)) (.rat 256)) (x2 i)) (.rat 160))
    (x2 i)) (.rat 32)) (x2 i)) (.rat 1)
/-- P1: `T8(x) + T8(y)`. -/
def eP1 : IExpr := .add (t8 0) (t8 1)
/-- P2 (Choi–Lam): `x²y² + y²z² + z²x² + w⁴ − 4(xy)(zw)`. -/
def eP2 : IExpr :=
  .sub (.add (.add (.add (.mul (x2 0) (x2 1)) (.mul (x2 1) (x2 2))) (.mul (x2 2) (x2 0)))
      (.pow (.var 3) 4))
    (.mul (.mul (.rat 4) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))

def box1 : List (ℚ × ℚ) := [(-1, 1), (-1, 1)]
def box2 : List (ℚ × ℚ) := [(-1, 1), (-1, 1), (-1, 1), (-1, 1)]

end ManyBox

namespace ManyBox
open Lean Elab Tactic Meta

/-- `mb_kernel d "file" chunk`: for goals `?cert : Cert` and `checkK e g ?cert env = true` (as
left by `refine prove_le e bs c ?_ ?_ xs ?_`), decode the certificate file, assign it, and
prove the check with `decide +kernel`, `chunk` leaves per kernel call (realfp's
`proveCheck`, the same proof shape as the `interval` tactic). -/
elab "mb_kernel " d:num p:str chunk:num : tactic => do
  let gs ← getGoals
  let (gc, gh, rest) ← match gs with
    | a :: b :: r => pure (a, b, r)
    | _ => throwError "mb_kernel: expected the goals ?cert and checkK … = true"
  let dir := (← getFileName) |> System.FilePath.mk |>.parent |>.getD "."
  let txt ← IO.FS.readFile (dir / p.getString)
  let line := (txt.splitOn "\n").filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""
  let cert := decodeCert d.getNat line
  gc.assign (RealFP.IntervalTactic.certToExpr cert)
  let ty ← instantiateMVars (← gh.getType)
  let some (_, lhs, _) := ty.eq? | throwError "mb_kernel: goal is not an equation"
  let args := lhs.getAppArgs
  unless args.size == 5 do throwError m!"mb_kernel: goal is not `checkK e g cert env = true`: {args.size} args in {lhs}"
  setGoals [gh]
  let pf ← RealFP.IntervalTactic.proveCheck chunk.getNat args[1]! args[2]! cert args[4]!
  gh.assign pf
  setGoals rest

/-- Close `InBoxes xs bs` (realfp's `inBoxesTac`). -/
elab "mb_inboxes" : tactic => RealFP.IntervalTactic.inBoxesTac

end ManyBox

/-! ### A fast native checker: `checkF`

`checkK` evaluates boxes with realfp's kernel evaluator `evalK` (binary64 emulated on `Nat`
bit patterns), which is what `decide +kernel` and realfp's `(trust := native)` run. `checkF`
walks the same certificate but evaluates each leaf with `evalF`, i.e. realfp's hardware
interval evaluator `evalI` (the `@[implemented_by]` C runtime). `checkF_sound` proves
`checkF … = true → checkK … = true` (from `evalK_toI`), so a `native_decide` proof of `checkF`
gives the theorem through the ordinary `prove_le` / `prove_ge`. The extra trust compared with
`checkK` under `native_decide` is the C runtime (already trusted by `native_decide` in
realfp). -/

namespace ManyBox
open Interval64 Interval64.KF RealFP.IntervalTactic

def checkF (e : IExpr) (g : KI → Bool) : Cert → List KI → Bool
  | .leaf, env => g (evalF env e)
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkF e g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkF e g r (env.set i ⟨m, (env.getD i zeroK).hi⟩)

theorem evalF_eq {env : List KI} (h : ∀ X ∈ env, WF X) (e : IExpr) :
    evalF env e = ⟨canon (evalK env e).lo, canon (evalK env e).hi⟩ := by
  have hK := evalK_toI h e
  have hm : (env.map fun X => (⟨toFl X.lo, toFl X.hi⟩ : Interval64)) = env.map toI := rfl
  have h1 : evalI (env.map fun X => (⟨toFl X.lo, toFl X.hi⟩ : Interval64)) e = toI (evalK env e) := by
    rw [hm, hK.1]
  unfold evalF
  simp only [h1]
  show KI.mk (toF (evalK env e).lo).toBits.toNat (toF (evalK env e).hi).toBits.toNat = _
  rw [toNat_toBits_toF hK.2.1, toNat_toBits_toF hK.2.2]

/-- The goal predicates only look at non-NaN endpoints, where `canon` is the identity. -/
def CanonOK (g : KI → Bool) : Prop := ∀ a b, g ⟨canon a, canon b⟩ = true → g ⟨a, b⟩ = true

theorem isNaN_qNaN : isNaN qNaN = true := by decide

theorem gLe_canon (c : Nat) : CanonOK (gLe c) := by
  intro a b h
  unfold gLe KF.canon at *
  cases ha : isNaN a <;> cases hb : isNaN b <;> simp_all [isNaN_qNaN]

theorem gGe_canon (c : Nat) : CanonOK (gGe c) := by
  intro a b h
  unfold gGe KF.canon at *
  cases ha : isNaN a <;> cases hb : isNaN b <;> simp_all [isNaN_qNaN]

theorem checkF_sound (e : IExpr) (g : KI → Bool) (hg : CanonOK g) :
    ∀ (c : Cert) (env : List KI), (∀ X ∈ env, WF X) → checkF e g c env = true →
      checkK e g c env = true := by
  intro c
  induction c with
  | leaf =>
    intro env hwf h
    simp only [checkF, checkK] at *
    rw [evalF_eq hwf] at h
    exact hg _ _ h
  | split i m l r ihl ihr =>
    intro env hwf h
    simp only [checkF, checkK, Bool.and_eq_true] at *
    obtain ⟨⟨⟨hn, hm⟩, hl⟩, hr⟩ := h
    have hm' : m < 2 ^ 64 := Nat.blt_eq ▸ hm
    have hwi := getD_wf hwf i
    refine ⟨⟨⟨hn, hm⟩, ihl _ (set_wf hwf i ⟨hwi.1, hm'⟩) hl⟩, ihr _ (set_wf hwf i ⟨hm', hwi.2⟩) hr⟩

theorem proveF_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkF e (gLe (KI.ofRat c).lo) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  RealFP.prove_le e bs c cert (checkF_sound e _ (gLe_canon _) cert _ (boxes_wf bs) h) xs hxs

theorem proveF_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkF e (gGe (KI.ofRat c).hi) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  RealFP.prove_ge e bs c cert (checkF_sound e _ (gGe_canon _) cert _ (boxes_wf bs) h) xs hxs

end ManyBox
