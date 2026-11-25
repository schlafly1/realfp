/-
Two classical inequalities for the sine, on the first quadrant. The
statements use the rational endpoint `157/100 = 1.57`, which is safely
below `π/2 ≈ 1.570796…` (the `realfp` tactic needs numeral bounds, so
the box cannot be written as `[0, π/2]` itself).

* Taylor remainder:  x − x³/6 ≤ sin x ≤ x
  (the first two nonzero terms of the sine series, with remainder sign).
* Jordan's inequality:  (2/π) x ≤ sin x
  (the graph of sine lies above the chord from 0 to π/2; the same
  inequality holds on the slightly smaller interval used here).

Both are proved with `realfp` in the default kernel-checked mode (Lean's
standard axioms only).

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/Jordan.lean
-/
import RealFPMathlib

namespace RealFP.Examples.Jordan

/-- `x − x³/6 ≤ sin x ≤ x` on `[0, 157/100]`. -/
theorem sin_taylor :
    ∀ x ∈ Set.Icc (0 : ℝ) (157 / 100),
      x - x ^ 3 / 6 ≤ Real.sin x ∧ Real.sin x ≤ x := by
  realfp

/-- Jordan's inequality: `(2/π) x ≤ sin x` on `[0, 157/100] ⊂ [0, π/2]`. -/
theorem jordan :
    ∀ x ∈ Set.Icc (0 : ℝ) (157 / 100), 2 * x / Real.pi ≤ Real.sin x := by
  realfp

end RealFP.Examples.Jordan
