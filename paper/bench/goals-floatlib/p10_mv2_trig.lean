import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p10_mv2_trig : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, Real.sin x * Real.cos y ≤ 1.01 := by
  first | interval | (intros; interval)
#print axioms p10_mv2_trig
