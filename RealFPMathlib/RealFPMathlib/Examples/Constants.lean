/-
Famous constants to 30 decimal places, proved with 128-bit dyadic intervals
(`realfp (precision := 128)`). Everything is in the default kernel-checked
mode and depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

    π  = 3.14159265358979323846264338327950…
    e  = 2.71828182845904523536028747135266…
    √2 = 1.41421356237309504880168872420969…
    φ  = (1 + √5)/2 = 1.61803398874989484820458683436563…

Also Archimedes' classical bounds 223/71 < π < 22/7, which binary64
interval arithmetic can prove without raising the precision.

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/Constants.lean
-/
import RealFPMathlib

namespace RealFP.Examples.Constants

/-- `π` to 30 decimals. -/
theorem pi_bounds :
    (3.14159265358979323846264338327950 : ℝ) < Real.pi ∧
      Real.pi < 3.14159265358979323846264338327951 := by
  realfp (precision := 128)

/-- `e = exp 1` to 30 decimals. -/
theorem e_bounds :
    (2.7182818284590452353602874713526 : ℝ) < Real.exp 1 ∧
      Real.exp 1 < 2.7182818284590452353602874713527 := by
  realfp (precision := 128)

/-- `√2` to 30 decimals. -/
theorem sqrt2_bounds :
    (1.41421356237309504880168872420969 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < 1.41421356237309504880168872420970 := by
  realfp (precision := 128)

/-- The golden ratio `φ = (1 + √5)/2` to 30 decimals. -/
theorem golden_ratio_bounds :
    (1.61803398874989484820458683436563 : ℝ) < (1 + Real.sqrt 5) / 2 ∧
      (1 + Real.sqrt 5) / 2 < 1.61803398874989484820458683436564 := by
  realfp (precision := 128)

/-- Archimedes' upper bound: `π < 22/7`. -/
theorem pi_lt_22_div_7 : Real.pi < 22 / 7 := by
  realfp

/-- Archimedes' lower bound: `223/71 < π`. -/
theorem pi_gt_223_div_71 : 223 / 71 < Real.pi := by
  realfp

end RealFP.Examples.Constants
