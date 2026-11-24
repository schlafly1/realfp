/-
Examples for `Real.sinc` (Mathlib), registered by `@[realfp_fn] sinc_sound`
(`RealFPMathlib/Extensions/Sinc.lean`). The removable singularity at `0` is handled by the
enclosure; the registered derivative only holds away from `0`.
-/
import RealFPMathlib.Extensions.Sinc
import RealFPMathlib.Front

open Real RealFP

namespace RealFP.Examples.Sinc

/-! Bounds: `sinc 1 = sin 1 ≈ 0.8414709848`; `sinc 0 = 1`; near `0`, `sinc x ≈ 1 - x²/6` -/

example : (0.841470984 : ℝ) < sinc 1 ∧ sinc 1 < 0.841470985 := by realfp
example : (0.9999 : ℝ) < sinc 0 := by realfp
example : (0.99999999833 : ℝ) < sinc 1e-4 ∧ sinc 1e-4 < 0.99999999834 := by realfp
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, 0.45 ≤ sinc x := by realfp
example : ∀ x ∈ Set.Icc (-10 : ℝ) 10, sinc x ≤ 1 := by realfp
-- `0` inside the box: the enclosure uses evenness and the endpoint value `sinc 1`
example (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : 0.84 ≤ sinc x := by interval

/-! Roots: `sinc x = 1/2` at `x ≈ 1.8954943`; the first zero is `π` -/

example : ∃ x ∈ Set.Icc (1.89549 : ℝ) 1.8955, sinc x = 1/2 := by root_exists
-- Krawczyk needs `sin`/`cos` in the kernel (~0.5 s each) on many boxes: check `∃!` natively.
example : ∃! x ∈ Set.Icc (1.8 : ℝ) 2, sinc x = 1/2 := by realfp (trust := native)
example : ∃! x ∈ Set.Icc (3 : ℝ) 3.2, sinc x = 0 := by realfp (trust := native)

/-! Integrals: `∫₁² sinc = Si 2 - Si 1 ≈ 0.6593299`. Integrals over a range containing `0`
(e.g. `∫₀¹ sinc = Si 1`) are not supported: Taylor quadrature needs the derivative on every
cell. -/

example : (∫ x in (1 : ℝ)..2, sinc x) ∈ Set.Icc (0.655 : ℝ) 0.663 := by integral_bound

/-! Optimisation: `min_{[0, 10]} sinc ≈ -0.2172336` at the first root of `tan x = x`, `x ≈ 4.4934`
(the `∀` bound needs many `sin` boxes away from `[-3, 3]`, so it is checked natively) -/

example : ∀ x ∈ Set.Icc (0 : ℝ) 10, -0.21724 ≤ sinc x := by realfp (trust := native)
example : ∃ x ∈ Set.Icc (0 : ℝ) 10, sinc x ≤ -0.21723 := by realfp

end RealFP.Examples.Sinc
