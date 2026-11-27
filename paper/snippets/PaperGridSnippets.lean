import RealFPGrid

/-! Snippets for the paper's section on `interval_grid` (docs/GPU.md).
Check with `cd RealFPMathlib && lake lean ../paper/snippets/PaperGridSnippets.lean`. -/

namespace PaperGridSnippets

-- `(explore := true)` proves nothing and always fails; it reports the maximum.
/-- error: interval_grid (explore := true) -/
#guard_msgs (substring := true) in
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    x * y - x ^ 2 ≤ 1 / 4 + 1 / 1000 := by
  interval_grid (explore := true)

theorem nesbitt (a b c : ℝ) (ha : 1 ≤ a) (ha' : a ≤ 3) (hb : 1 ≤ b)
    (hb' : b ≤ 3) (hc : 1 ≤ c) (hc' : c ≤ 3) :
    3 / 2 - 1 / 64 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  interval_grid (cert := "certs/nesbitt.cert")

theorem small : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    x * y - x ^ 2 ≤ 1 / 4 + 1 / 1000 := by
  interval_grid (tool := none)

#print axioms nesbitt
#print axioms small

end PaperGridSnippets
