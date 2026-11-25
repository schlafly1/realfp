import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p02_log2_tight : (0.6931471 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931472 := by
  realfp
#print axioms p02_log2_tight
