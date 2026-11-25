import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p09_sin_touch : ∀ x ∈ Set.Icc (0 : ℝ) 2, Real.sin x ≤ x := by
  first | interval | (intros; interval)
#print axioms p09_sin_touch
