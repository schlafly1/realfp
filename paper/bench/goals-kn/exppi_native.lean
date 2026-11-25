import RealFPMathlib
set_option maxHeartbeats 0
set_option realfp.native true
theorem T : Real.exp (Real.exp 1 * Real.log Real.pi) < Real.exp Real.pi := by
  realfp
#print axioms T
