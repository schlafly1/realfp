import RealFPGridShowcase.Gen.M6.Main

/-! M6 ≥ −1/4 on `[−1, 1]⁶` (Reznick's AM–GM form): 6.5·10⁹ boxes
(`grid/showcase.sh m6 M6 16 8 gpu64`; docs/GPU.md, "Showcases"). -/

theorem m6_ge :
  ∀ x1 ∈ Set.Icc (-1 : ℝ) 1, ∀ x2 ∈ Set.Icc (-1 : ℝ) 1, ∀ x3 ∈ Set.Icc (-1 : ℝ) 1,
  ∀ x4 ∈ Set.Icc (-1 : ℝ) 1, ∀ x5 ∈ Set.Icc (-1 : ℝ) 1, ∀ x6 ∈ Set.Icc (-1 : ℝ) 1,
    (-1 / 4 : ℝ) ≤
      x6 ^ 12 + x1 ^ 2 * x2 ^ 2 * x3 ^ 2 * x4 ^ 2 * x5 ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2)
        - 6 * x6 ^ 2 * (x1 ^ 2 * x2 ^ 2 * x3 ^ 2 * x4 ^ 2 * x5 ^ 2) := by
  interval_grid (use := RealFPGridShowcase.Gen.M6.bound)

#print axioms m6_ge
