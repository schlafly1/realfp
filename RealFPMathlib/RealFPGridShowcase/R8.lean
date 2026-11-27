import RealFPGridShowcase.Gen.R8.Main

/-! R8 ≥ −9 on `[−1, 1]⁸`: 5.3·10⁹ boxes (`grid/showcase.sh r8 R8 16 8 gpu64`; docs/GPU.md,
"Showcases"). realfp's `interval` would need days for this; see `README.md`. -/

theorem r8_ge :
  ∀ x0 ∈ Set.Icc (-1 : ℝ) 1, ∀ x1 ∈ Set.Icc (-1 : ℝ) 1, ∀ x2 ∈ Set.Icc (-1 : ℝ) 1,
  ∀ x3 ∈ Set.Icc (-1 : ℝ) 1, ∀ x4 ∈ Set.Icc (-1 : ℝ) 1, ∀ x5 ∈ Set.Icc (-1 : ℝ) 1,
  ∀ x6 ∈ Set.Icc (-1 : ℝ) 1, ∀ x7 ∈ Set.Icc (-1 : ℝ) 1,
    (-9 : ℝ) ≤
      ((8 * x0 ^ 2 - 8) * x0 ^ 2 + 1) * ((8 * x1 ^ 2 - 8) * x1 ^ 2 + 1) +
      ((8 * x1 ^ 2 - 8) * x1 ^ 2 + 1) * ((8 * x2 ^ 2 - 8) * x2 ^ 2 + 1) +
      ((8 * x2 ^ 2 - 8) * x2 ^ 2 + 1) * ((8 * x3 ^ 2 - 8) * x3 ^ 2 + 1) +
      ((8 * x3 ^ 2 - 8) * x3 ^ 2 + 1) * ((8 * x4 ^ 2 - 8) * x4 ^ 2 + 1) +
      ((8 * x4 ^ 2 - 8) * x4 ^ 2 + 1) * ((8 * x5 ^ 2 - 8) * x5 ^ 2 + 1) +
      ((8 * x5 ^ 2 - 8) * x5 ^ 2 + 1) * ((8 * x6 ^ 2 - 8) * x6 ^ 2 + 1) +
      ((8 * x6 ^ 2 - 8) * x6 ^ 2 + 1) * ((8 * x7 ^ 2 - 8) * x7 ^ 2 + 1) +
      ((8 * x7 ^ 2 - 8) * x7 ^ 2 + 1) * ((8 * x0 ^ 2 - 8) * x0 ^ 2 + 1) := by
  interval_grid (use := RealFPGridShowcase.Gen.R8.bound)

#print axioms r8_ge
