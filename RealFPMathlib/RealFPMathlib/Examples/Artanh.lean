/-
Examples for `Real.artanh` (Mathlib), registered on its domain `(-1, 1)` by
`@[realfp_fn] artanh_sound` (`RealFPMathlib/Extensions/Artanh.lean`). Ranges must stay strictly
inside `(-1, 1)`.
-/
import RealFPMathlib.Extensions.Artanh
import RealFPMathlib.Front

open Real RealFP

namespace RealFP.Examples.Artanh

/-! Bounds: `artanh ½ = ½ log 3 ≈ 0.5493061443`; near `0`, `artanh x ≈ x + x³/3` -/

example : (0.549306144 : ℝ) < artanh (1/2) ∧ artanh (1/2) < 0.549306145 := by realfp
example : (1.0000000000333e-5 : ℝ) < artanh 1e-5 ∧ artanh 1e-5 < 1.0000000000334e-5 := by realfp
example : ∀ x ∈ Set.Icc (-0.99 : ℝ) 0.99, artanh x ≤ 2.65 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 0.9, x ≤ artanh x := by realfp
example (x : ℝ) (h0 : -0.5 ≤ x) (h1 : x ≤ 0.5) : artanh x * artanh x ≤ 0.31 := by interval

/-! Roots: `artanh x = 1` at `x = tanh 1 ≈ 0.7615942` -/

example : ∃! x ∈ Set.Icc (0 : ℝ) 0.9, artanh x = 1 := by realfp
example : ∃ x ∈ Set.Icc (0.76159 : ℝ) 0.7616, artanh x = 1 := by root_exists

/-! Integrals: `∫₀^½ artanh = ¼ log 3 + ½ log ¾ ≈ 0.1308120` -/

example : (∫ x in (0 : ℝ)..(1/2), artanh x) ∈ Set.Icc (0.1308 : ℝ) 0.1309 := by integral_bound
example : (0.1308 : ℝ) ≤ ∫ x in (0 : ℝ)..(1/2), artanh x := by realfp

/-! Optimisation: `min_{[0, 0.9]} (artanh x - 2x) = log (1 + √2) - √2 ≈ -0.5328400` at `x = 1/√2` -/

example : ∀ x ∈ Set.Icc (0 : ℝ) 0.9, artanh x - 2 * x ≤ 0 := by realfp
-- The interior minimum needs derivative boxes, each with several kernel `log` evaluations
-- (~0.1 s each): the kernel check exceeds the default heartbeats, so check it natively.
example : ∀ x ∈ Set.Icc (0 : ℝ) 0.9, -0.532841 ≤ artanh x - 2 * x := by realfp (trust := native)
example : ∃ x ∈ Set.Icc (0 : ℝ) 0.9, artanh x - 2 * x ≤ -0.532839 := by realfp

end RealFP.Examples.Artanh
