import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p20_mv2_quad_near : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + y ^ 2 - x * y ≥ -1 / 100 := by
  intros; interval (depth := 24)
#print axioms p20_mv2_quad_near
