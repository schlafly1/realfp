/-
Higher-order 2D quadrature (tensor Taylor cells), checked by the kernel on `KI` bit patterns.

* `gauss2_bounds` : `0.5566 ≤ ∫₀¹ ∫₀¹ e^{-x²-y²} dy dx ≤ 0.5585` (true value `0.5577462853…`),
  `taylor2Bound` with `K = 4` on a `2 × 2` grid (enclosure `[0.556673, 0.558420]`, width
  `1.7e-3`). The first-order rule `integrate2E1` needs `2^8 × 2^8` cells for width `1.9e-3`.
* `gauss2_rect_bounds` : the same for the integral over `[0,1] × [0,1]` (Fubini).
-/
import RealFPMathlib.KTaylor2

open Interval64 Interval64.Quad Interval64.KF Interval64.KF.KQ RealFP RealFP.KTaylor2
open MeasureTheory Set

namespace RealFP.Examples.Taylor2

def g2 : IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))

/-- `uniformCells 0 1 2` (bit patterns of `(0, 1/4, 1/2)`, `(1/2, 3/4, 1)`). -/
def cs2 : List (Nat × Nat × Nat) :=
  [(0, 4598175219545276416, 4602678819172646912),
   (4602678819172646912, 4604930618986332160, 4607182418800017408)]

theorem cert2 : taylor2Bound g2 4 0 4607182418800017408 0 4607182418800017408 cs2 cs2 0 1 0 1
    (5566 / 10000) (5585 / 10000) = true := by decide +kernel

theorem gauss2_bounds :
    (0.5566 : ℝ) ≤ (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (-(x * x + y * y))) ∧
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (-(x * x + y * y))) ≤ 0.5585 := by
  have h := integral2_bounds_of_taylor2Bound cert2
  simp only [g2, IExpr.denote, List.getD_cons_zero, List.getD_cons_succ, Rat.cast_zero,
    Rat.cast_one] at h
  constructor
  · have := h.1; norm_num at this ⊢; linarith
  · have := h.2; norm_num at this ⊢; linarith

theorem gauss2_rect_bounds :
    (0.5566 : ℝ) ≤ (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-(p.1 * p.1 + p.2 * p.2))) ∧
      (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Real.exp (-(p.1 * p.1 + p.2 * p.2))) ≤ 0.5585 := by
  have hc : ContinuousOn (Function.uncurry fun x y : ℝ => Real.exp (-(x * x + y * y)))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    apply Continuous.continuousOn; unfold Function.uncurry; fun_prop
  rw [show (fun p : ℝ × ℝ => Real.exp (-(p.1 * p.1 + p.2 * p.2))) =
      fun p => (fun x y : ℝ => Real.exp (-(x * x + y * y))) p.1 p.2 from rfl,
    RealFP.Quad2.setIntegral_rect_eq zero_le_one zero_le_one hc]
  exact gauss2_bounds

end RealFP.Examples.Taylor2
