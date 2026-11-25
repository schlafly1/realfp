import RealFPMathlib
set_option maxHeartbeats 0
theorem T : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4 ≥ -1.032 := by realfp
#print axioms T
