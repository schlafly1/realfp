import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p01_log2_loose : Real.log 2 < 7 / 10 := by
  realfp
#print axioms p01_log2_loose
