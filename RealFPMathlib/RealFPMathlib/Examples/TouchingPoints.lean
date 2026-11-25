/-
Touching points: inequalities `f ≥ c` where `f` comes down to `c`, exactly
or almost, at a point inside the box.

Interval bisection alone cannot prove such a bound. Every box containing the
touching point `p` gets an enclosure that dips slightly below `c`, however
small the box. The `touch` option of `realfp` / `interval` handles a small
box `B` around `p` differently:

* it proves the Hessian of `f` is positive definite on all of `B` (an
  interval Hessian plus an exact rational `LDLᵀ` certificate), so `f` is
  convex on `B` and lies above its tangent plane at `p`:
  `f(x) ≥ f(p) + ∇f(p)·(x − p)`;
* it checks the bound on that tangent plane over `B`. At an exact touching
  point the gradient is `0` and this is just `f(p) ≥ c`.

The rest of the box is bisected as usual. Everything is checked by the Lean
kernel (`decide +kernel`); the theorems use only Lean's standard axioms.

Sections:
1. `(touch := auto)`: realfp finds the touching points itself (Newton's
   method on `∇f = 0`).
2. Exact touching at rational points such as `1/3`, which are not binary64
   numbers: `f(p)` and `∇f(p)` are computed exactly in `ℚ`.
3. Near touching at an irrational point, where plain bisection fails.
4. What cannot work: exact touching at an irrational point.

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/TouchingPoints.lean
-/
import RealFPMathlib

namespace RealFP.Examples.TouchingPoints

/-! ### 1. Points found automatically -/

/-- `x⁴ − 2x² + 1 = (x² − 1)² ≥ 0` (written expanded), with zeros at `x = ±1`.
`auto` finds both. -/
theorem quartic :
    ∀ x ∈ Set.Icc (-2 : ℝ) 3, 0 ≤ x ^ 4 - 2 * x ^ 2 + 1 := by
  realfp (touch := auto)

/-- A quadratic form in three variables. Its minimum `0` is at `(1/3, 1/3, 1/3)`, which `auto`
locates and snaps to the exact rational point. -/
theorem three_vars :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2, ∀ z ∈ Set.Icc (0 : ℝ) 2,
      0 ≤ x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x + (x - 1 / 3) ^ 2 := by
  realfp (touch := auto)

/-! ### 2. Exact rational touching points -/

/-- `9x² − 6x + 1 = (3x − 1)² ≥ 0`, touching at `x = 1/3`. -/
theorem third :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 9 * x ^ 2 - 6 * x + 1 := by
  realfp (touch := [1/3])

/-- Two variables, touching at `(1/3, 1/5)`. -/
theorem third_fifth :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      0 ≤ 9 * x ^ 2 - 6 * x + 25 * y ^ 2 - 10 * y + 2 := by
  realfp (touch := [(1/3, 1/5)])

/-! ### 3. Near touching at an irrational point

The minimum of `(x² − 2)² + (3y² − 1)²` is `0`, at `(√2, 1/√3)`. Adding `10⁻¹³` makes the
bound strict with a margin of `10⁻¹³`. Plain `realfp` / `interval` fails here: at depth 24
the boxes around the minimum are still too wide. With `auto` the tangent plane at the
binary64 point nearest the minimum (gradient ≈ `10⁻¹⁶`) does it with about 40 boxes. -/

theorem near_touch :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      0 < x ^ 4 - 4 * x ^ 2 + 4 + 9 * y ^ 4 - 6 * y ^ 2 + 1 + 1 / 10 ^ 13 := by
  realfp (touch := auto)

/-! ### 4. What cannot work: exact touching at an irrational point

`x⁴ − 4x² + 4 = (x² − 2)²` is `0` exactly at `x = √2`. Every rational point near `√2`
has `f > 0`, but `f` cannot be evaluated there exactly enough to separate it from `0` once
the box contains `√2`. Every interval enclosure of `f` near `√2` contains negative
numbers. With `auto` realfp finds the point, the tangent-plane check fails, and the error
explains that the goal needs symbolic help. Here that help is one `nlinarith` step. -/

theorem sqrt_two_touch :
    ∀ x ∈ Set.Icc (0 : ℝ) 3, 0 ≤ x ^ 4 - 4 * x ^ 2 + 4 := by
  fail_if_success realfp (touch := auto)
  intro x _
  nlinarith [sq_nonneg (x ^ 2 - 2)]

end RealFP.Examples.TouchingPoints
