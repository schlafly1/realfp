import RealFPMathlib
set_option maxHeartbeats 0
set_option realfp.native true
theorem T : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, Real.exp (x * y) - x - y ≥ -1 / 100 := by
  realfp
#print axioms T
