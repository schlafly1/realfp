import RealFPGridShowcase.Gen.Nesbitt.Main

/-! The split-certificate workflow on a small problem (`grid/showcase.sh nesbitt Nesbitt 9 3`). -/

theorem nesbitt_split : ∀ a ∈ Set.Icc (1 : ℝ) 3, ∀ b ∈ Set.Icc (1 : ℝ) 3, ∀ c ∈ Set.Icc (1 : ℝ) 3,
    3 / 2 - 1 / 64 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  interval_grid (use := RealFPGridShowcase.Gen.Nesbitt.bound)

#print axioms nesbitt_split
