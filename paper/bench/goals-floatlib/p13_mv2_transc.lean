import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p13_mv2_transc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, Real.exp (x * y) - x - y ≥ -0.01 := by
  first | interval | (intros; interval)
#print axioms p13_mv2_transc
