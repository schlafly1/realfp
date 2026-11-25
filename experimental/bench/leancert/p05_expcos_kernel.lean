import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p05_expcos : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  realfp
#print axioms p05_expcos
