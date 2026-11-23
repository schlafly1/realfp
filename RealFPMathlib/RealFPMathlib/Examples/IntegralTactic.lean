/-
`integral_bound` examples (kernel Taylor quadrature, standard axioms only).
-/
import RealFPMathlib.IntegralTactic

namespace RealFP.Examples.IntegralTactic

theorem gauss_lower : (0.7468 : ℝ) ≤ ∫ x in (0:ℝ)..1, Real.exp (-x ^ 2) := by integral_bound

theorem gauss_icc : (∫ x in (0:ℝ)..1, Real.exp (-x ^ 2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by
  integral_bound

/-- `log 2 = ∫₁² 1/x` to four digits (adaptive cells, power-denominator quotient rule). -/
theorem inv_icc : (∫ x in (1:ℝ)..2, 1 / x) ∈ Set.Icc (0.6931 : ℝ) 0.6932 := by integral_bound

/-- `1 - cos 1 = ∫₀¹ sin x`. -/
theorem sin_icc : (∫ x in (0:ℝ)..1, Real.sin x) ∈ Set.Icc (0.4596 : ℝ) 0.4598 := by integral_bound

/-- `π/4 = ∫₀¹ 1/(1+x²)`. -/
theorem atan_icc : (∫ x in (0:ℝ)..1, 1 / (1 + x ^ 2)) ∈ Set.Icc (0.7853 : ℝ) 0.7854 := by
  integral_bound

end RealFP.Examples.IntegralTactic
