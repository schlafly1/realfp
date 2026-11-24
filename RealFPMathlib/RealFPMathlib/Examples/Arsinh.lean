/-
Examples for `Real.arsinh` (Mathlib), registered by `@[realfp_fn] arsinh_sound`
(`RealFPMathlib/Extensions/Arsinh.lean`).
-/
import RealFPMathlib.Extensions.Arsinh
import RealFPMathlib.Front

open Real RealFP

namespace RealFP.Examples.Arsinh

/-! Bounds: `arsinh 1 = log (1 + √2) ≈ 0.8813735870`; near `0`, `arsinh x ≈ x - x³/6` -/

example : (0.881373587 : ℝ) < arsinh 1 ∧ arsinh 1 < 0.881373588 := by realfp
example : (9.99999999983e-6 : ℝ) < arsinh 1e-5 ∧ arsinh 1e-5 < 9.99999999984e-6 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 10, arsinh x ≤ x := by realfp
example : ∀ x ∈ Set.Icc (-3 : ℝ) 3, arsinh x ≠ 2 := by realfp
example (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 4) : arsinh x ≤ Real.log (2 * x) + 0.25 := by interval

/-! Roots: `arsinh x = 1` at `x = sinh 1 ≈ 1.1752012` -/

example : ∃! x ∈ Set.Icc (0 : ℝ) 2, arsinh x = 1 := by realfp
example : ∃ x ∈ Set.Icc (1.1752 : ℝ) 1.17521, arsinh x = 1 := by root_exists

/-! Integrals: `∫₀¹ arsinh = arsinh 1 - √2 + 1 ≈ 0.4671600` -/

example : (∫ x in (0 : ℝ)..1, arsinh x) ∈ Set.Icc (0.46716 : ℝ) 0.467161 := by integral_bound
example : (0.4671 : ℝ) ≤ ∫ x in (0 : ℝ)..1, arsinh x := by realfp

/-! Optimisation: `max_{[0,3]} (arsinh x - x/2) = log (2 + √3) - √3/2 ≈ 0.4509325` at `x = √3` -/

example : ∀ x ∈ Set.Icc (0 : ℝ) 3, arsinh x - x / 2 ≤ 0.450933 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 3, 0.450932 ≤ arsinh x - x / 2 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 3, ∀ y ∈ Set.Icc (0 : ℝ) 3, arsinh y - y / 2 ≤ arsinh x - x / 2 := by
  realfp

end RealFP.Examples.Arsinh
