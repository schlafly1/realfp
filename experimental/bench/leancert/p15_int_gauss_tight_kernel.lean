import RealFPMathlib.Front
set_option maxHeartbeats 0
open MeasureTheory
theorem p15_int_gauss_tight : (0.7468 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by
  realfp
#print axioms p15_int_gauss_tight
