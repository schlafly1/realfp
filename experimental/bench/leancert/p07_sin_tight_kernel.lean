import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p07_sin_tight : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1 / 1000 := by
  realfp
#print axioms p07_sin_tight
