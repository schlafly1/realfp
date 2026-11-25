import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p07_sin_tight : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1 / 1000 := by
  intros; interval (depth := 24)
#print axioms p07_sin_tight
