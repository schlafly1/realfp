import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p11_mv2_poly : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x * y - x - y ≥ -1.01 := by
  first | interval | (intros; interval)
#print axioms p11_mv2_poly
