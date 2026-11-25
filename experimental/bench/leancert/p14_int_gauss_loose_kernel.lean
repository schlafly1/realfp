import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p14_int_gauss_loose : (0.74 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by
  realfp
#print axioms p14_int_gauss_loose
