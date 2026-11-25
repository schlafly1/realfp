import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p04_exp1_tight : Real.exp 1 ≤ 2.7183 ∧ (2.7182 : ℝ) ≤ Real.exp 1 := by
  first | interval | (intros; interval)
#print axioms p04_exp1_tight
