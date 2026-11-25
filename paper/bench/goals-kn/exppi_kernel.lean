import RealFPMathlib
set_option maxHeartbeats 0
theorem T : Real.exp (Real.exp 1 * Real.log Real.pi) < Real.exp Real.pi := by
  realfp
#print axioms T
