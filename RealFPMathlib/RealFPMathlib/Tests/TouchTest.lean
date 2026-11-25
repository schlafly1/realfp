/-
Tests for `interval (touch := [p₁, …])` / `realfp (touch := …)` (`RealFPMathlib.Touch`): bounds
attained at interior points, proved by a second-order Taylor leaf around each point plus
ordinary bisection elsewhere. Kernel-checked unless marked `native`.
-/
import RealFPMathlib.Front

namespace RealFP.TouchTests

-- one variable: lower bounds (convex at the point) and an upper bound (concave)
theorem u1 : ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 := by interval (touch := [1])
theorem u2 : ∀ x ∈ Set.Icc (0 : ℝ) 3, x * (1 - x) ≤ 1 / 4 := by interval (touch := [1/2])
theorem u3 : ∀ x ∈ Set.Icc (-2 : ℝ) 3, 0 ≤ x ^ 4 - 2 * x ^ 2 + 1 := by
  interval (touch := [1, -1])
theorem u4 (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 5) : 1 + x ≤ Real.exp x := by
  realfp (touch := [(0)])
-- the bound may hold with slack at the point (here `f(1) = 1/2 > 0`; `f'(1) = 0`)
theorem u5 : ∀ x ∈ Set.Icc (0 : ℝ) 3, 0 ≤ (x - 1) ^ 2 + 1 / 2 := by interval (touch := [1])
-- the bound as `f ≥ c` with the constant on the right
theorem u6 : ∀ x ∈ Set.Icc (0 : ℝ) 2, x ^ 2 - 2 * x ≥ -1 := by interval (touch := [1])
-- both sides non-constant (moved to `lhs - rhs ≤ 0`)
theorem u7 : ∀ x ∈ Set.Icc (1 / 10 : ℝ) 10, Real.log x ≤ x - 1 := by interval (touch := [1])

-- several variables: coordinates in binder order (asymmetric point, three variables)
theorem m1 : ∀ x ∈ Set.Icc (0 : ℝ) 3, ∀ y ∈ Set.Icc (0 : ℝ) 3, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    0 ≤ (x - 1) ^ 2 + (y - 2) ^ 2 * (1 + x ^ 2) + (z + 1 / 2) ^ 2 := by
  interval (touch := [(1, 2, -1/2)])
-- variables first used in a different order than bound
theorem m2 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) (hy : 0 ≤ y ∧ y ≤ 4) :
    0 ≤ (y - 3) ^ 2 + (x - 1) ^ 2 + x * y - x * y := by
  interval (touch := [(1, 3)])
-- Motzkin polynomial on a quadrant, native trust (an `example`: the axiom audit allows
-- `native_decide` only in `RealFP.Demo` / `RealFP.Examples`)
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
    0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  realfp (touch := [(1, 1)]) (trust := native)

-- errors
-- plain bisection never lands on `x = 1` in `[0, 10]`
example : ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 := by
  fail_if_success interval
  interval (touch := [1])
/--
error: interval: touching point [1]: no touch box found (the touch check failed (f(p) does not satisfy the bound, or the gradient at p does not evaluate to exactly 0 in binary64, or the expression is not differentiable on the box)); the Hessian must be positive definite at the point (negative definite for an upper bound)
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 - 1 / 1000 := by
  interval (touch := [1])
example : ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 := by
  fail_if_success interval (touch := [2])   -- not stationary
  interval (touch := [1])
example : ∀ x ∈ Set.Icc (-2 : ℝ) 3, 0 ≤ x ^ 4 - 2 * x ^ 2 + 1 := by
  fail_if_success interval (touch := [1])   -- a touching point is missing
  interval (touch := [1, -1])
/--
error: interval: touching point coordinate 1/3 is not exactly representable in binary64; (touch := _) needs dyadic points such as 1, -1/2, 3/8
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (3 * x - 1) ^ 2 := by
  interval (touch := [1/3])
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2, 0 ≤ (x - 1) ^ 2 + (y - 1) ^ 2 := by
  fail_if_success interval (touch := [1])    -- wrong number of coordinates
  interval (touch := [(1, 1)])
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 ≤ (x - 3) ^ 2 := by
  fail_if_success interval (touch := [3])    -- outside the box
  interval
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 < (x - 1) ^ 2 + 1 := by
  fail_if_success interval (touch := [1])    -- strict
  interval
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, (x - 1) ^ 2 + 1 ≠ 0 := by
  fail_if_success interval (touch := [1])    -- `≠`
  interval
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 ≤ (x - 1) ^ 2 := by
  fail_if_success interval (touch := [1]) (precision := 128)
  fail_if_success realfp (touch := [])
  interval (touch := [1])
/--
error: interval: touching point [1]: no touch box found (the exact LDLᵀ pivot 0 is -1/4194304 ≤ 0, so the matrix is not positive definite); the Hessian must be positive definite at the point (negative definite for an upper bound)
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 3, 0 ≤ (x - 1) ^ 4 := by
  interval (touch := [1])    -- degenerate (zero second derivative) touching point
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  fail_if_success realfp (touch := [1])     -- not a bound goal
  realfp

end RealFP.TouchTests
