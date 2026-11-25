import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p19_int_inv_loose : (∫ x in (1 : ℝ)..2, 1 / x) ≤ 0.7 := by
  realfp
#print axioms p19_int_inv_loose
