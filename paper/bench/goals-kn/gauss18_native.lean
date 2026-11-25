import RealFPMathlib
set_option maxHeartbeats 0
set_option realfp.native true
theorem T : (0.746824132812427025 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 0.746824132812427026 := by
  integral_bound (precision := 128)
#print axioms T
