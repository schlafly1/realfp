/-
`integral_bound` examples (kernel Taylor quadrature, standard axioms only).
-/
import RealFPMathlib.IntegralTactic

namespace RealFP.Examples.IntegralTactic

theorem gauss_lower : (0.7468 : ℝ) ≤ ∫ x in (0:ℝ)..1, Real.exp (-x ^ 2) := by integral_bound

theorem gauss_icc : (∫ x in (0:ℝ)..1, Real.exp (-x ^ 2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by
  integral_bound

end RealFP.Examples.IntegralTactic
