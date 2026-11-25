/-
Classical inequalities whose equality case is an *interior* point of the
interval, proved with `realfp (touch := [p])` in the default kernel-checked
mode (Lean's standard axioms only).

* AM–GM for `1` and `x`:  √x ≤ (1 + x)/2 on [0, 10], equality at x = 1.
* The tangent line of the logarithm:  log x ≤ x − 1 on [1/10, 10], equality at x = 1.
* The tangent line of the exponential:  1 + x ≤ eˣ on [-2, 5], equality at x = 0.

Plain interval bisection cannot prove these: every box containing the
equality point gets an enclosure that dips slightly below the bound.
`(touch := [p])` names the point where the two sides meet. realfp checks
that the bound holds at `p` and that the derivative is exactly `0` there,
and proves the second derivative has the right sign on a small box around
`p`. Taylor's theorem then covers that box, and ordinary bisection covers
the rest of the interval. With `(touch := auto)` realfp finds the point
itself (Newton's method on `f′ = 0`); the last example uses that.

(On `[0, 4]` plain `realfp` already proves AM–GM: bisection lands exactly on
`x = 1`, where the two sides are equal in binary64 and monotonicity takes
over. On `[0, 10]` the bisection points never hit `1`, so `touch` is needed.
The same goes for `[-2, 5]` and `x = 0`.)

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/AMGM.lean
-/
import RealFPMathlib

namespace RealFP.Examples.AMGM

/-- AM–GM: `√x ≤ (1 + x) / 2` on `[0, 10]`, with equality at `x = 1`. -/
theorem sqrt_le_avg :
    ∀ x ∈ Set.Icc (0 : ℝ) 10, Real.sqrt x ≤ (1 + x) / 2 := by
  realfp (touch := [1])

/-- `log x ≤ x − 1` on `[1/10, 10]`, with equality at `x = 1`. -/
theorem log_le_sub_one :
    ∀ x ∈ Set.Icc (1 / 10 : ℝ) 10, Real.log x ≤ x - 1 := by
  realfp (touch := [1])

/-- `1 + x ≤ exp x` on `[-2, 5]`, with equality at `x = 0`. -/
theorem one_add_le_exp :
    ∀ x ∈ Set.Icc (-2 : ℝ) 5, 1 + x ≤ Real.exp x := by
  realfp (touch := auto)

end RealFP.Examples.AMGM
