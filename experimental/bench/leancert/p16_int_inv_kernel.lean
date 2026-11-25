import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p16_int_inv : (∫ x in (1 : ℝ)..2, 1 / x) ≤ 0.6932 := by
  realfp
#print axioms p16_int_inv
