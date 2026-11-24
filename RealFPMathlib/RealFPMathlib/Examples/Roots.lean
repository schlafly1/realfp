/-
Root finding with kernel-checked certificates (`root_exists`, `root_unique`, via `realfp`),
exclusion (`≠` via `interval`) and positive definiteness (`pos_def`). Every theorem here uses
only `propext`, `Classical.choice`, `Quot.sound`.
-/
import RealFPMathlib.Front

namespace RealFP.Examples.Roots

/-! ### One variable -/

/-- `√2` is the unique root of `x² - 2` in `[1, 2]` (LeanCert's `x01`). Sign change at the
ends (IVT) plus a positive derivative enclosure (strict monotonicity). -/
theorem sqrt2_unique : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by realfp

theorem sqrt2_unique' : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp

/-- The Dottie number exists. -/
theorem dottie_exists : ∃ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by realfp

theorem dottie_unique : ∃! x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by realfp

theorem exp_line_unique : ∃! x ∈ Set.Icc (0 : ℝ) 1, Real.exp x = 3 - 2 * x := by realfp

/-- A root pinned to a tiny interval (found by Newton, checked by sign change). -/
theorem cubic_root_tight : ∃ x ∈ Set.Icc (1.3247 : ℝ) 1.3248, x ^ 3 - x - 1 = 0 := by realfp

/-! ### Exclusion -/

theorem exp_ne_two_x : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≠ 2 * x := by realfp

theorem cos_ne_zero : ∀ x ∈ Set.Icc (-1.5 : ℝ) 1.5, Real.cos x ≠ 0 := by realfp

/-! ### Systems (Krawczyk) -/

/-- `x² + y = 2, x + y² = 2` has exactly one solution in `[0.9, 1.1]²` (namely `(1, 1)`). -/
theorem sys2_unique : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by realfp

/-- Circle ∩ diagonal: existence on a wide box (Krawczyk on a small box around the Newton
point, which is inside). -/
theorem circle_diag_exists : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 3 ∧ p.2 ∈ Set.Icc (0 : ℝ) 3 ∧
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 = p.2 := by realfp

/-- A transcendental system; bounds written as inequalities, in any order. -/
theorem exp_sys_unique : ∃! p : ℝ × ℝ, Real.exp p.1 + p.2 = 2 ∧ -1/20 ≤ p.1 ∧ p.1 ≤ 1/20 ∧
    p.1 + p.2 ^ 2 = 1 ∧ 19/20 ≤ p.2 ∧ p.2 ≤ 21/20 := by realfp

/-- A cyclic 3×3 system over `Fin 3 → ℝ`. -/
theorem cyc3_unique : ∃! p : Fin 3 → ℝ, p 0 ∈ Set.Icc (0.95 : ℝ) 1.05 ∧
    p 1 ∈ Set.Icc (0.95 : ℝ) 1.05 ∧ p 2 ∈ Set.Icc (0.95 : ℝ) 1.05 ∧
    p 0 ^ 2 + p 1 = 2 ∧ p 1 ^ 2 + p 2 = 2 ∧ p 2 ^ 2 + p 0 = 2 := by realfp

/-- `sin x + y = 1, x - y² = -1` on a wide box (the root `(0, 1)` is found by Newton from a
grid of starting points, then certified by Krawczyk on a small box around it). -/
theorem trig_sys_exists : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 2 ∧
    Real.sin p.1 + p.2 = 1 ∧ p.1 - p.2 ^ 2 = -1 := by realfp

/-! ### Positive definiteness -/

theorem pd2 : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by realfp

theorem pd3 : (!![4, 1, 0.5; 1, 3, -1; 0.5, -1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by realfp

theorem hilbert4_pd : (Matrix.of fun i j : Fin 4 => (1 : ℝ) / ((i : ℝ) + j + 1)).PosDef := by
  realfp

end RealFP.Examples.Roots
