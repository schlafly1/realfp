import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p21_mv2_rosen : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-1 : ℝ) 3, (1 - x) ^ 2 + 100 * (y - x ^ 2) ^ 2 ≥ -1 / 100 := by
  realfp
#print axioms p21_mv2_rosen
