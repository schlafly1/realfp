import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p06_poly_tight : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ 1 / 4 + 1 / 1000 := by
  intros; interval (depth := 24)
#print axioms p06_poly_tight
