import RealFPGrid

/-! Problem files for the showcases (`grid/showcase.sh`). `#grid_export` writes
`problems/NAME.problem` (for `realfp-grid`) and `problems/NAME.problem.lean.txt` (for
`grid/gen_lean.py`); it proves nothing. -/

/- R8: a ring of 8 Chebyshev "spins", `Σᵢ T₄(xᵢ) T₄(xᵢ₊₁ mod 8) ≥ −9` on `[−1, 1]⁸`
(`T₄(x) = (8x² − 8)x² + 1`; the true minimum is −8). -/
#grid_export "problems/r8.problem" :
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
      ((8 * x7 ^ 2 - 8) * x7 ^ 2 + 1) * ((8 * x0 ^ 2 - 8) * x0 ^ 2 + 1)

/- M6: Reznick's AM–GM form in 6 variables, `x₆¹² + P(x₁² + ⋯ + x₅²) − 6x₆²P ≥ −1/4`,
`P = x₁²⋯x₅²` (the minimum is 0, attained, so a margin is needed). -/
#grid_export "problems/m6.problem" :
  ∀ x1 ∈ Set.Icc (-1 : ℝ) 1, ∀ x2 ∈ Set.Icc (-1 : ℝ) 1, ∀ x3 ∈ Set.Icc (-1 : ℝ) 1,
  ∀ x4 ∈ Set.Icc (-1 : ℝ) 1, ∀ x5 ∈ Set.Icc (-1 : ℝ) 1, ∀ x6 ∈ Set.Icc (-1 : ℝ) 1,
    (-1 / 4 : ℝ) ≤
      x6 ^ 12 + x1 ^ 2 * x2 ^ 2 * x3 ^ 2 * x4 ^ 2 * x5 ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2)
        - 6 * x6 ^ 2 * (x1 ^ 2 * x2 ^ 2 * x3 ^ 2 * x4 ^ 2 * x5 ^ 2)

/- Nesbitt on `[1, 3]³` (small; tests the split workflow). -/
#grid_export "problems/nesbitt.problem" :
  ∀ a ∈ Set.Icc (1 : ℝ) 3, ∀ b ∈ Set.Icc (1 : ℝ) 3, ∀ c ∈ Set.Icc (1 : ℝ) 3,
    3 / 2 - 1 / 64 ≤ a / (b + c) + b / (c + a) + c / (a + b)
