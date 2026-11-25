import FloatLib.Tactic.Interval
set_option maxHeartbeats 0
open MeasureTheory
theorem p03_pi : (3.14159 : ℝ) < Real.pi ∧ Real.pi < 3.1416 := by
  refine ⟨?_, ?_⟩ <;> first | interval | interval (depth := 24)
#print axioms p03_pi
