import FloatLib.Tactic.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option maxHeartbeats 0
open MeasureTheory
theorem p15_int_gauss_tight : (0.7468 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by
  first | interval | (intros; interval)
#print axioms p15_int_gauss_tight
