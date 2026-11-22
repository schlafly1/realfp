/-
Slow (≈65 s, ≈7 GB) kernel example for the 2D Taylor rule: `K = 4` on a `4 × 4` grid,
enclosure `[0.557718, 0.557767]` (width `4.9e-5`) of `∫₀¹ ∫₀¹ e^{-x²-y²} = 0.5577462853…`.
-/
import RealFPMathlib.Examples.Taylor2

open Interval64 Interval64.KF Interval64.KF.KQ RealFP RealFP.KTaylor2

namespace RealFP.Examples.Taylor2

/-- `uniformCells 0 1 4`. -/
def cs4 : List (Nat × Nat × Nat) :=
  [(0, 4593671619917905920, 4598175219545276416),
   (4598175219545276416, 4600427019358961664, 4602678819172646912),
   (4602678819172646912, 4603804719079489536, 4604930618986332160),
   (4604930618986332160, 4606056518893174784, 4607182418800017408)]

theorem cert4 : taylor2Bound g2 4 0 4607182418800017408 0 4607182418800017408 cs4 cs4 0 1 0 1
    (557715 / 1000000) (557770 / 1000000) = true := by decide +kernel

theorem gauss2_bounds_tight :
    (0.557715 : ℝ) ≤ (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (-(x * x + y * y))) ∧
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (-(x * x + y * y))) ≤ 0.55777 := by
  have h := integral2_bounds_of_taylor2Bound cert4
  simp only [g2, IExpr.denote, List.getD_cons_zero, List.getD_cons_succ, Rat.cast_zero,
    Rat.cast_one] at h
  constructor
  · have := h.1; norm_num at this ⊢; linarith
  · have := h.2; norm_num at this ⊢; linarith

end RealFP.Examples.Taylor2
