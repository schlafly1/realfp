import RealFPMathlib
set_option maxHeartbeats 0
set_option realfp.native true
theorem T : Real.pi < 22 / 7 := by
  realfp
#print axioms T
