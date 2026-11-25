import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p08_exp_touch : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  intros; interval (depth := 24)
#print axioms p08_exp_touch
