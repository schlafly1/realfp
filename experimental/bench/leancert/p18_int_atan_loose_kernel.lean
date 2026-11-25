import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p18_int_atan_loose : (∫ x in (0 : ℝ)..1, Real.arctan x) ≤ 0.439 := by
  realfp
#print axioms p18_int_atan_loose
