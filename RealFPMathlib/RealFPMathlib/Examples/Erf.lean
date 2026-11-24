/-
Examples for the first registered function, `RealFP.erf` (`RealFPMathlib/Extensions/Erf.lean`).
Nothing in the tactics knows about `erf`: it is plugged in by `@[realfp_fn] erf_sound`.
-/
import RealFPMathlib.Extensions.Erf
import RealFPMathlib.Front

open RealFP

namespace RealFP.Examples.Erf

/-! Bounds (`realfp` / `interval`; derivative modes use the registered derivative `2/√π e^{-x²}`) -/

example : (0.5204 : ℝ) < erf (1/2) ∧ erf (1/2) < 0.5205 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 3, erf x ≤ x + 0.03 := by realfp
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, erf x ≠ 2 := by realfp
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2) : erf x + Real.exp (-x) ≥ 0.999 := by interval

/-! Roots: the median of the half-normal, `erf x = 1/2` at `x ≈ 0.476936` -/

example : ∃! x ∈ Set.Icc (0 : ℝ) 1, erf x = 1/2 := by realfp
example : ∃ x ∈ Set.Icc (0.4769 : ℝ) 0.477, erf x = 1/2 := by root_exists
example : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    erf p.1 - p.2 = 0 ∧ p.1 + p.2 - 1 = 0 := by realfp

/-! Integrals: `∫₀¹ erf = erf 1 - (1 - e⁻¹)/√π ≈ 0.486064` -/

example : (∫ x in (0 : ℝ)..1, erf x) ∈ Set.Icc (0.4860 : ℝ) 0.4861 := by integral_bound
example : (0.486 : ℝ) ≤ ∫ x in (0 : ℝ)..1, erf x := by realfp

/-! Optimisation: `max_{[0,3]} (erf x - x/2) ≈ 0.3469104` at `x = √(log(4/π)) ≈ 0.4915` -/

example : ∀ x ∈ Set.Icc (0 : ℝ) 3, erf x - x / 2 ≤ 0.346912 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 3, 0.346909 ≤ erf x - x / 2 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 3, ∀ y ∈ Set.Icc (0 : ℝ) 3, erf y - y / 2 ≤ erf x - x / 2 := by
  realfp

end RealFP.Examples.Erf
