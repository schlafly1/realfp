import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p12_mv3_poly : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, x * y + y * z + z * x ≤ 3 := by
  realfp
#print axioms p12_mv3_poly
