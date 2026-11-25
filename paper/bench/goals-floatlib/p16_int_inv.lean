import FloatLib.Tactic.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option maxHeartbeats 0
open MeasureTheory
theorem p16_int_inv : (∫ x in (1 : ℝ)..2, 1 / x) ≤ 0.6932 := by
  first | interval | (intros; interval)
#print axioms p16_int_inv
