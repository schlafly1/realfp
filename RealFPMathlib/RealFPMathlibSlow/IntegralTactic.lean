/-
Slower `integral_bound` examples with `sin` integrands (each 30–90 s, ≈4.5 GB): every cell
evaluates `KI.sin`/`KI.cos` in the kernel (≈1 s each), once per shared let thanks to the
witnessed CSE certificate (`RealFP.KQS.integral_bounds_of_quadBoundW`).
-/
import RealFPMathlib.IntegralTactic

namespace RealFP.Examples.IntegralTactic

set_option maxHeartbeats 0

/-- `Si 2 - Si 1 = ∫₁² sin x / x`. -/
theorem sinc_icc : (∫ x in (1:ℝ)..2, Real.sin x / x) ∈ Set.Icc (0.6593 : ℝ) 0.6594 := by
  integral_bound

/-- `(1 - cos 10)/10 = ∫₀¹ sin (10x)`. -/
theorem sin10_icc : (∫ x in (0:ℝ)..1, Real.sin (10 * x)) ∈ Set.Icc (0.1839 : ℝ) 0.1840 := by
  integral_bound

/-- Fresnel-type `∫₀³ sin (x²)`. -/
theorem sinsq_icc : (∫ x in (0:ℝ)..3, Real.sin (x ^ 2)) ∈ Set.Icc (0.7735 : ℝ) 0.7736 := by
  integral_bound

end RealFP.Examples.IntegralTactic
