/-
Global optimisation over boxes with `realfp`: lower/upper bounds, discovered bounds (`∃ m : ℚ`),
`sInf`/`sSup` statements (including exact values), witnesses, and existence/localisation of
minimisers. The search (best-first branch-and-bound, bisection, centred forms) runs natively and
is untrusted; every certificate is checked by `decide +kernel`. Everything here except
`trig2_native` uses only `propext`, `Classical.choice`, `Quot.sound`.
-/
import RealFPMathlib.Front

namespace RealFP.Examples.Optimization

/-! ### One variable -/

/-- `x² - x` has minimum exactly `-1/4` at `x = 1/2` (derivative zero at the minimum: the
certificate uses monotonicity on both halves). -/
theorem quad_min_exact : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≥ -1/4 := by realfp

theorem quad_min_tight : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≥ -1/4 - 1/1000000 := by realfp

/-- Double-well, minimum `-1` attained at `x = ±1`. -/
theorem quartic_min_exact : ∀ x ∈ Set.Icc (-2 : ℝ) 2, -1 ≤ x ^ 4 - 2 * x ^ 2 := by realfp

/-- Mathlib-idiomatic: the infimum of the image is exactly `-1/4`. -/
theorem quad_sInf : sInf ((fun x : ℝ => x ^ 2 - x) '' Set.Icc 0 1) = -1/4 := by realfp

/-- `min_{[-1,1]} x² + sin x ≈ -0.2324656` to `10⁻⁶` (irrational minimiser). -/
theorem sin_sq_sInf :
    |sInf ((fun x : ℝ => x ^ 2 + Real.sin x) '' Set.Icc (-1) 1) - (-0.2324656)| ≤ 1/10^6 := by
  realfp

/-- `min_{[0,2]} eˣ - 2x = 2 - 2 ln 2 ≈ 0.6137056`. -/
theorem exp_sInf :
    sInf ((fun x : ℝ => Real.exp x - 2 * x) '' Set.Icc 0 2) ∈ Set.Icc 0.613705 0.613706 := by
  realfp

/-- `max_{[0,3]} x e^{-x} = 1/e`. -/
theorem xexp_sSup :
    sSup ((fun x : ℝ => x * Real.exp (-x)) '' Set.Icc 0 3) ∈ Set.Icc 0.367879 0.36788 := by
  realfp

/-- Discovery: `realfp` finds a rational lower bound itself. -/
theorem x02_discover : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + Real.sin x ≥ m := by realfp

theorem xexp_discover : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 3, x * Real.exp (-x) ≤ M := by realfp

/-- Witness: a point that is nearly optimal. -/
theorem exp_near_min : ∃ x ∈ Set.Icc (0 : ℝ) 2, Real.exp x - 2 * x < 0.6138 := by realfp

/-- A global minimiser exists (compactness + continuity via `fun_prop`). -/
theorem quad_argmin :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≤ y ^ 2 - y := by realfp

/-- …and it lies in `[-0.451, -0.45]` (localisation: the sub-box minimum beats the rest). -/
theorem sin_sq_argmin_loc :
    ∃ x ∈ Set.Icc (-0.451 : ℝ) (-0.45), ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      x ^ 2 + Real.sin x ≤ y ^ 2 + Real.sin y := by realfp

/-! ### Several variables -/

/-- Six-hump camel, global minimum `≈ -1.0316285` (two minimisers). -/
theorem camel_lower : ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4 ≥ -1.032 := by realfp

theorem camel_discover : ∃ m : ℚ, ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4 ≥ m := by realfp

theorem camel_witness : ∃ x ∈ Set.Icc (-2 : ℝ) 2, ∃ y ∈ Set.Icc (-1 : ℝ) 1,
    4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4 ≤ -1.0316 := by realfp

/-- Himmelblau: `inf = 0`, attained at `(3, 2)` (found on a rational grid). -/
theorem himmelblau_sInf :
    sInf ((fun p : ℝ × ℝ => (p.1^2 + p.2 - 11)^2 + (p.1 + p.2^2 - 7)^2) ''
      (Set.Icc (-5) 5 ×ˢ Set.Icc (-5) 5)) = 0 := by realfp

/-- Rosenbrock: `inf = 0` at `(1, 1)`. -/
theorem rosenbrock_sInf :
    sInf ((fun p : ℝ × ℝ => (1 - p.1)^2 + 100*(p.2 - p.1^2)^2) ''
      (Set.Icc (-2) 2 ×ˢ Set.Icc (-1) 3)) = 0 := by realfp

theorem three_var : ∀ x ∈ Set.Icc (0:ℝ) 2, ∀ y ∈ Set.Icc (0:ℝ) 2, ∀ z ∈ Set.Icc (-2:ℝ) 0,
    -6 ≤ (x - 1)^2 + (y - 2)^2 + (z + 1)^2 + x*y*z := by realfp

theorem three_var_discover : ∃ m : ℚ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    ∀ z ∈ Set.Icc (-1 : ℝ) 1, m ≤ x^2 + y^2 + z^2 - x*y - y*z + x - z := by realfp

/-- Transcendental, two variables: cheap with `native` trust (the kernel spends minutes on the
`sin`/`cos` monotonicity certificates). -/
theorem trig2_native : ∀ x ∈ Set.Icc (-3 : ℝ) 3, ∀ y ∈ Set.Icc (-3 : ℝ) 3,
    -0.795 ≤ Real.sin x * Real.cos y + (x^2 + y^2) / 10 := by realfp (trust := native)

/-! ### Reports (no proof): approximate minimum and minimiser -/

#realfp_min (x ∈ Set.Icc (-2:ℝ) 2) (y ∈ Set.Icc (-1:ℝ) 1),
  4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4
#realfp_max (x ∈ Set.Icc (0:ℝ) 3), x * Real.exp (-x)

end RealFP.Examples.Optimization
