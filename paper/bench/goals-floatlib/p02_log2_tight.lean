import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p02_log2_tight : (0.6931471 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931472 := by
  first | interval | (intros; interval)
#print axioms p02_log2_tight
