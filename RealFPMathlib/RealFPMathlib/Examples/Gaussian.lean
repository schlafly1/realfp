/-
The Gaussian integral

    I = ∫₀¹ exp(-x²) dx = 0.74682413281242702539…

has no elementary antiderivative. This file bounds it in two ways, both in
the default kernel-checked mode (Lean's standard axioms only):

* four decimal places with the default binary64 `integral_bound`;
* 18 significant digits with 128-bit Taylor models
  (`integral_bound (precision := 128)`).

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/Gaussian.lean
-/
import RealFPMathlib

namespace RealFP.Examples.Gaussian

/-- `∫₀¹ exp(-x²)` to four decimal places. -/
theorem gauss_four_digits :
    (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by
  integral_bound

/-- `∫₀¹ exp(-x²)` to 18 significant digits. -/
theorem gauss_18_digits :
    (0.746824132812427025 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 0.746824132812427026 := by
  integral_bound (precision := 128)

end RealFP.Examples.Gaussian
