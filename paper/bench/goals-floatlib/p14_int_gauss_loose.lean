import FloatLib.Tactic.Interval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option maxHeartbeats 0
open MeasureTheory
theorem p14_int_gauss_loose : (0.74 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by
  first | interval | (intros; interval)
#print axioms p14_int_gauss_loose
