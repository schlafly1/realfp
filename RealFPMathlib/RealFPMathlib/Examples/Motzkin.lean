/-
The Motzkin polynomial

    M(x, y) = x⁴y² + x²y⁴ − 3x²y² + 1

is nonnegative on ℝ² (by AM–GM on x⁴y², x²y⁴ and 1), but it is the classic
example of a nonnegative polynomial that is not a sum of squares of
polynomials. Its minimum value 0 is attained at the four interior points
(±1, ±1).

`realfp (touch := [(1, 1)])` proves `M ≥ 0` on the quadrant `[0, 2]²`: it
checks `M(1, 1) = 0` and `∇M(1, 1) = 0` exactly, proves the Hessian is
positive definite on a small box around `(1, 1)` (exact rational `LDLᵀ`
certificate), and bisects the rest of the quadrant. Because `M` depends
only on `x²` and `y²`, the bound on `[-2, 2]²` follows from the quadrant.

Both theorems are kernel-checked and use Lean's standard axioms only. You
can also give all four points at once, as in
`realfp (touch := [(1, 1), (-1, 1), (1, -1), (-1, -1)])` on `[-2, 2]²`.
That works, but it needs about four times as many boxes.

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/Motzkin.lean
-/
import RealFPMathlib

namespace RealFP.Examples.Motzkin

/-- The Motzkin polynomial is nonnegative on `[0, 2]²` (zero at `(1, 1)`). -/
theorem motzkin_quadrant :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  realfp (touch := [(1, 1)])

/-- The Motzkin polynomial is nonnegative on `[-2, 2]²` (zeros at `(±1, ±1)`). -/
theorem motzkin_nonneg :
    ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-2 : ℝ) 2,
      0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  intro x hx y hy
  have h := motzkin_quadrant |x| ⟨abs_nonneg x, abs_le.2 hx⟩ |y| ⟨abs_nonneg y, abs_le.2 hy⟩
  simpa only [Even.pow_abs (by decide : Even 4), Even.pow_abs (by decide : Even 2)] using h

end RealFP.Examples.Motzkin
