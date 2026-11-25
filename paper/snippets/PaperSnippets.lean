/-
Every Lean snippet that appears in `paper/realfp.tex`, collected so that
it can be checked with
    cd RealFPMathlib && lake lean ../paper/snippets/PaperSnippets.lean
-/
import RealFPMathlib

namespace PaperSnippets

-- §1 Introduction
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp

example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp

-- §6 Examples: constants
theorem pi_bounds :
    (3.14159265358979323846264338327950 : ℝ) < Real.pi ∧
      Real.pi < 3.14159265358979323846264338327951 := by
  realfp (precision := 128)

theorem pi_lt_22_div_7 : Real.pi < 22 / 7 := by realfp

theorem exp_pi_gt_pi_exp :
    Real.exp (Real.exp 1 * Real.log Real.pi) < Real.exp Real.pi := by realfp

-- Gaussian integral
theorem gauss_four_digits :
    (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by
  integral_bound

theorem gauss_18_digits :
    (0.746824132812427025 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 0.746824132812427026 := by
  integral_bound (precision := 128)

-- Jordan
theorem jordan :
    ∀ x ∈ Set.Icc (0 : ℝ) (157 / 100), 2 * x / Real.pi ≤ Real.sin x := by
  realfp

-- Touching points
theorem sqrt_le_avg :
    ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 := by
  realfp (touch := [1])

theorem one_add_le_exp :
    ∀ x ∈ Set.Icc (-2 : ℝ) 5, 1 + x ≤ Real.exp x := by
  realfp (touch := auto)

theorem motzkin_quadrant :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  realfp (touch := [(1, 1)])

theorem near_touch :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      0 < x ^ 4 - 4 * x ^ 2 + 4 + 9 * y ^ 4 - 6 * y ^ 2 + 1 + 1 / 10 ^ 13 := by
  realfp (touch := auto)

-- Roots, systems, optimisation, matrices
theorem dottie_unique : ∃! x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by realfp

theorem sys2_unique : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by
  realfp

theorem exp_sInf :
    sInf ((fun x : ℝ => Real.exp x - 2 * x) '' Set.Icc 0 2) ∈
      Set.Icc 0.613705 0.613706 := by
  realfp

example : (!![4, 1, 0; 1, 3, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  pos_def

-- Native mode
theorem exp_pi_native :
    Real.exp 1 * Real.log Real.pi < Real.pi := by realfp (trust := native)

end PaperSnippets

#print axioms PaperSnippets.motzkin_quadrant
#print axioms PaperSnippets.gauss_18_digits
#print axioms PaperSnippets.exp_pi_native
