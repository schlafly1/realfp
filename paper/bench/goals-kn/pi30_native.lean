import RealFPMathlib
set_option maxHeartbeats 0
set_option realfp.native true
theorem T : (3.14159265358979323846264338327950 : ℝ) < Real.pi ∧
      Real.pi < 3.14159265358979323846264338327951 := by
  realfp (precision := 128)
#print axioms T
