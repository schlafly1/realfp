import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p03_pi : (3.14159 : ℝ) < Real.pi ∧ Real.pi < 3.1416 := by
  realfp
#print axioms p03_pi
