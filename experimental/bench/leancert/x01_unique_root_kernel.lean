import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem x01 : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  realfp
#print axioms x01
