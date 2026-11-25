import RealFPMathlib
set_option maxHeartbeats 0
theorem T : ∀ x ∈ Set.Icc (0 : ℝ) (157 / 100), 2 * x / Real.pi ≤ Real.sin x := by
  realfp
#print axioms T
