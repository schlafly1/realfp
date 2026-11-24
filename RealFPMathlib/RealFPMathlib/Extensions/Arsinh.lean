/-
`Real.arsinh` (Mathlib: `arsinh x = log (x + √(1 + x²))`) as a realfp extension.

Enclosure: `arsinh` is increasing, so a box `[a, b]` maps to `[arsinh a, arsinh b]`, with point
enclosures (`ExtFn.ofMonoK`):
* `|q| ≤ 2⁻¹²`: rational bounds `q - q³/6 ≤ arsinh q ≤ q - q³/6 + 3q⁵/40` (`q ≥ 0`, odd symmetry
  for `q < 0`) — relative width `≤ 3q⁴/40 < 2⁻⁵²`;
* otherwise the kernel's `log (|q| + √(1 + q²))` (no cancellation), relative error `≲ 10⁻¹²`
  just above `2⁻¹²` and a few ulps for `|q| ≳ 1`.
Derivative `1/√(1 + x²)` (`Real.hasDerivAt_arsinh`), everywhere.
-/
import RealFPMathlib.Registry
import Mathlib.Analysis.SpecialFunctions.Arsinh

open Real
open Interval64 Interval64.KF

namespace RealFP.Arsinh

theorem inv_sqrt_ge (u : ℝ) (hu : 0 ≤ u) : 1 - u / 2 ≤ (√(1 + u))⁻¹ := by
  rcases le_or_gt (1 - u / 2) 0 with h | h
  · exact h.trans (by positivity)
  · rw [← Real.sqrt_inv]
    apply Real.le_sqrt_of_sq_le
    rw [← one_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u)]

theorem inv_sqrt_le (u : ℝ) (hu : 0 ≤ u) : (√(1 + u))⁻¹ ≤ 1 - u / 2 + 3 * u ^ 2 / 8 := by
  have hp : 0 < 1 - u / 2 + 3 * u ^ 2 / 8 := by nlinarith [sq_nonneg (u - 2/3)]
  rw [← Real.sqrt_inv, ← Real.sqrt_sq hp.le]
  apply Real.sqrt_le_sqrt
  rw [← one_div, div_le_iff₀ (by positivity)]
  have h3 : 0 ≤ u ^ 3 := by positivity
  nlinarith [mul_nonneg h3 (by nlinarith [sq_nonneg (u - 5/6)] : (0:ℝ) ≤ 40 - 15 * u + 9 * u ^ 2)]

theorem lower {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ arsinh x := by
  have := nonneg_of_hasDerivAt (F := fun y => arsinh y - (y - y ^ 3 / 6))
    (F' := fun y => (√(1 + y ^ 2))⁻¹ - (1 - y ^ 2 / 2)) (by simp)
    (fun y _ _ => by
      have := (hasDerivAt_arsinh y).sub (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)))
      convert this using 1
      · funext z; simp
      · norm_num; ring)
    (fun y _ _ => by have := inv_sqrt_ge (y ^ 2) (sq_nonneg y); linarith) hx
  beta_reduce at this; linarith

theorem upper {x : ℝ} (hx : 0 ≤ x) : arsinh x ≤ x - x ^ 3 / 6 + 3 * x ^ 5 / 40 := by
  have := nonneg_of_hasDerivAt (F := fun y => (y - y ^ 3 / 6 + 3 * y ^ 5 / 40) - arsinh y)
    (F' := fun y => (1 - y ^ 2 / 2 + 3 * (y ^ 2) ^ 2 / 8) - (√(1 + y ^ 2))⁻¹) (by simp)
    (fun y _ _ => by
      have := (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        (((hasDerivAt_pow 5 y).const_mul 3).div_const 40)).sub (hasDerivAt_arsinh y)
      convert this using 1
      · funext z; simp
      · norm_num; ring)
    (fun y _ _ => by have := inv_sqrt_le (y ^ 2) (sq_nonneg y); linarith) hx
  beta_reduce at this; linarith

/-- `arsinh q` lies between `A = q - q³/6` and `A + 3q⁵/40` (either order). -/
theorem between (q : ℝ) : min (q - q ^ 3 / 6) (q - q ^ 3 / 6 + 3 * q ^ 5 / 40) ≤ arsinh q ∧
    arsinh q ≤ max (q - q ^ 3 / 6) (q - q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
  rcases le_or_gt 0 q with h | h
  · exact ⟨min_le_left _ _ |>.trans (lower h), (upper h).trans (le_max_right _ _)⟩
  · have h' : 0 ≤ -q := by linarith
    have l := lower h'; have u := upper h'
    rw [arsinh_neg] at l u
    constructor
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (by nlinarith : arsinh q ≤ q - q ^ 3 / 6).trans (le_max_left _ _)

/-- `log (x + √(1 + x²))` and `-log (-x + √(1 + x²))`. -/
def gPos : IExpr := .log (.add (.var 0) (.sqrt (.add (.rat 1) (.pow (.var 0) 2))))
def gNeg : IExpr := .neg (.log (.add (.neg (.var 0)) (.sqrt (.add (.rat 1) (.pow (.var 0) 2)))))

/-- Point enclosure of `arsinh` at the bit pattern `b`. -/
def pt (b : Nat) : KI :=
  match ratOfBits b with
  | some q =>
    if |q| ≤ 1 / 4096 then
      let A := q - q ^ 3 / 6
      let B := A + 3 * q ^ 5 / 40
      KI.ofRatInterval (min A B) (max A B)
    else if 0 ≤ q then evalK [ptK b] gPos else evalK [ptK b] gNeg
  | none => KI.whole

theorem pt_mem (b : Nat) (q : ℚ) (hb : b < 2 ^ 64) (hq : ratOfBits b = some q) :
    arsinh q ∈ (toI (pt b)).toSet := by
  unfold pt; rw [hq]; dsimp only
  split_ifs with h1 h2
  · rw [(KF.ofRatInterval_toI _ _).1]
    have := between (q : ℝ)
    apply mem_toSet_ofRatInterval <;> push_cast
    · exact this.1
    · exact this.2
  · have := denote_mem_evalK_pt hb hq gPos
    simpa [gPos, IExpr.denote, arsinh] using this
  · have := denote_mem_evalK_pt hb hq gNeg
    have e : arsinh (q : ℝ) = -arsinh (-(q : ℝ)) := by rw [arsinh_neg, neg_neg]
    rw [e]; simpa [gNeg, IExpr.denote, arsinh, neg_sq] using this

/-- Derivative template `1/√(1 + x²)`. -/
def arsinhDeriv : IExpr := .inv (.sqrt (.add (.rat 1) (.pow (.var 0) 2)))

end RealFP.Arsinh

namespace RealFP
open Arsinh

attribute [fun_prop] Real.continuous_arsinh

/-- The kernel implementation of `Real.arsinh`. -/
def arsinhExt : ExtFn := ExtFn.ofMonoK "arsinh" Arsinh.pt (fun _ => true) (fun _ => true) arsinhDeriv

/-- Registers `Real.arsinh` for all realfp tactics. -/
@[realfp_fn] theorem arsinh_sound : ExtSound arsinh (fun _ => True) arsinhExt :=
  ExtSound.ofMonoK (S := Set.univ) (arsinh_strictMono.monotone.monotoneOn _)
    (fun _ _ _ _ _ _ _ => Set.mem_univ _) (fun b q hb hq _ => pt_mem b q hb hq)
    (fun _ _ _ _ _ _ _ => trivial) rfl
    (fun x _ => by simpa [arsinhDeriv, IExpr.denoteB] using hasDerivAt_arsinh x)

end RealFP
