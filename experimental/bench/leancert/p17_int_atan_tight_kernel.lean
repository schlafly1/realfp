import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p17_int_atan_tight : (∫ x in (0 : ℝ)..1, Real.arctan x) ≤ 0.43882 := by
  realfp
#print axioms p17_int_atan_tight
