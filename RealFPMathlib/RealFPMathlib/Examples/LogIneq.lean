/-
The classical inequalities for the natural logarithm and the exponential,
proved with `realfp` in the default kernel-checked mode (Lean's standard
axioms only). For `x ≥ 0`:

    x / (1 + x) ≤ log(1 + x) ≤ x ≤ exp(x) − 1

Equality holds at `x = 0`, the left-hand endpoint of the interval.

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/LogIneq.lean
-/
import RealFPMathlib

namespace RealFP.Examples.LogIneq

/-- `log(1 + x) ≤ x` on `[0, 10]`. -/
theorem log_one_add_le :
    ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.log (1 + x) ≤ x := by
  realfp

/-- `x / (1 + x) ≤ log(1 + x)` on `[0, 10]`. -/
theorem log_one_add_ge :
    ∀ x ∈ Set.Icc (0 : ℝ) 10, x / (1 + x) ≤ Real.log (1 + x) := by
  realfp

/-- `1 + x ≤ exp x` on `[0, 10]`. -/
theorem one_add_le_exp :
    ∀ x ∈ Set.Icc (0 : ℝ) 10, 1 + x ≤ Real.exp x := by
  realfp

end RealFP.Examples.LogIneq
