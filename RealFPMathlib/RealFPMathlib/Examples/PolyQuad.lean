/-
Polynomial sign certificates and rigorous quadrature, checked by the kernel
(`decide +kernel` on the Lean specification; no `native_decide`, standard axioms only).

* `taylor_exp_pos` : `0 < 1 - x + x²/2 - x³/6 + x⁴/24` on `[0, 4]`.
* `gauss_integral_bounds` : `0.7451171875 ≤ ∫₀¹ e^{-x²} dx ≤ 0.748046875`.
-/
import RealFPMathlib.Quad

open Interval64 Interval64.Quad Interval64.KF RealFP RealFP.Poly RealFP.Quad Polynomial

namespace RealFP.Examples.PolyQuad

/-! ### Polynomial positivity -/

def e4 : Array ℚ := #[1, -1, 1/2, -1/6, 1/24]

theorem e4_check : (IPoly.ofRats e4).checkGt 0 (ofRatInterval 0 4) 12 = true := by decide +kernel

theorem toReal_zero : (0 : Float).toReal = 0 := by
  rw [toReal_of_bitsToRat? (q := 0) (by decide +kernel)]; simp

theorem taylor_exp_pos {x : ℝ} (h0 : 0 ≤ x) (h4 : x ≤ 4) :
    0 < 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  have hx : x ∈ ofRatInterval 0 4 :=
    mem_toSet_ofRatInterval (by push_cast; exact h0) (by push_cast; exact h4)
  have h := lt_of_checkGt (contains_ofRats e4) e4_check hx
  rw [toReal_zero, eval_ratPoly] at h
  simp [e4, Finset.sum_range_succ] at h
  linarith

/-! ### `∫₀¹ e^{-x²}` -/

/-- `e^{-x²}` as a reflected expression in variable `0`. -/
def g : IExpr := .exp (.neg (.mul (.var 0) (.var 0)))

/-- Second-order adaptive quadrature, 2⁴ cells. -/
def R : Interval64 := integrateE1 g 0 1 0 4

theorem R_ok : ((0.7451171875 : Float) ≤ R.lo ∧ R.hi ≤ (0.748046875 : Float)) := by decide +kernel

theorem toReal_one : (1 : Float).toReal = 1 := by
  rw [toReal_of_bitsToRat? (q := 1) (by decide +kernel)]; simp

theorem c_lo : (0.7451171875 : Float).toReal = 763 / 1024 := by
  rw [toReal_of_bitsToRat? (q := 763 / 1024) (by decide +kernel)]; norm_num

theorem c_hi : (0.748046875 : Float).toReal = 383 / 512 := by
  rw [toReal_of_bitsToRat? (q := 383 / 512) (by decide +kernel)]; norm_num

theorem integral_mem_R : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ∈ R := by
  have h := integral_mem_integrateE1 g (a := 0) (b := 1) (fun x _ => by simp [g, Dom]) 0 4
  rw [toReal_zero, toReal_one] at h
  have e : ∀ x : ℝ, g.denote [x] = Real.exp (-x ^ 2) := fun x => by simp [g, IExpr.denote, sq]
  simp only [e] at h
  exact h

/-- **`0.7451171875 ≤ ∫₀¹ e^{-x²} dx ≤ 0.748046875`** (true value `0.746824…`). -/
theorem gauss_integral_bounds :
    (763 / 1024 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 383 / 512 := by
  have h := integral_mem_R
  have hcn : (0.7451171875 : Float).isNaN = false := by decide +kernel
  have hci : (0.7451171875 : Float).isInf = false := by decide +kernel
  have hdn : (0.748046875 : Float).isNaN = false := by decide +kernel
  have hdi : (0.748046875 : Float).isInf = false := by decide +kernel
  constructor
  · have := le_of_lo hcn hci h R_ok.1; rwa [c_lo] at this
  · have := ge_of_hi hdn hdi h R_ok.2; rwa [c_hi] at this

end RealFP.Examples.PolyQuad
