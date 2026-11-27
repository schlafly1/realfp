import RealFPGrid

/-! Quick start for `interval_grid` (docs/GPU.md). -/

set_option trace.interval true in
/-- Nesbitt's inequality on `[1, 3]³`, with a margin of 1/64: 141,007 boxes. -/
theorem nesbitt (a b c : ℝ) (ha : 1 ≤ a) (ha' : a ≤ 3) (hb : 1 ≤ b) (hb' : b ≤ 3) (hc : 1 ≤ c)
    (hc' : c ≤ 3) : 3 / 2 - 1 / 64 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  interval_grid (cert := "certs/nesbitt.cert")

/-- Power means: `√a + √b + √c ≤ √(3(a+b+c))` up to 1/64 on `[1, 3]³`. -/
theorem power_means (a b c : ℝ) (ha : 1 ≤ a) (ha' : a ≤ 3) (hb : 1 ≤ b) (hb' : b ≤ 3) (hc : 1 ≤ c)
    (hc' : c ≤ 3) : √a + √b + √c - √(3 * (a + b + c)) ≤ 1 / 64 := by
  interval_grid (cert := "certs/power_means.cert")

/-- A small one, built-in search (no tool, no cache). -/
theorem small : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, x * y - x ^ 2 ≤ 1 / 4 + 1 / 1000 := by
  interval_grid (tool := none)

#print axioms nesbitt
#print axioms power_means
#print axioms small
