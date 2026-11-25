import RealFPMathlib
set_option maxHeartbeats 0
theorem T : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by
  integral_bound
#print axioms T
