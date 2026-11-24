/-
`(precision := 128)`: Interval128 (double-double, about 106-bit) endpoints in `interval` and
`realfp`. Every bound below is out of reach at the default precision 64 (pinned by
`fail_if_success`) and is proved with `decide +kernel` at precision 128 (standard axioms only),
except `sqrt2_native`, which uses `trust := native`.

Kernel times on the dev box (8 cores, AVX-512 build), 64-bit attempt / 128-bit proof:
* `sqrt2_gap_*`      fails / about 0.3 s each
* `pi_upper`         fails / about 0.3 s
* `poly7_*`          fails / about 4 s each (expanded `(x - 1)^7` at `x = 1.001`)
* `sqrt_cancel_*`    fails / about 0.3 s each
* `quad_box`         fails / about 20 s (one variable, about 120 boxes at depth 70)
-/
import RealFPMathlib.Front

namespace RealFP.Examples.Precision128

/-! ### Constants: digits beyond binary64

`√2 - 1.4142135623730950488 ≈ 1.6887e-21`: at precision 64 the enclosure of `√2` alone is
`2.2e-16` wide. -/

example : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by
  fail_if_success interval
  interval (precision := 128)

theorem sqrt2_gap_upper : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by
  interval (precision := 128)

theorem sqrt2_gap_lower : 1.6e-21 < Real.sqrt 2 - 1.4142135623730950488 := by
  realfp (precision := 128)

theorem sqrt2_native : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by
  realfp (precision := 128) (trust := native)

/-- `π` is enclosed by Mathlib's 20-digit bounds `pi_gt_d20` / `pi_lt_d20` at precision 128
(Interval64 gives `π < 3.14159265358979356`). -/
theorem pi_upper : Real.pi < 3.1415926535897932385 := by
  fail_if_success interval
  interval (precision := 128)

/-! ### Cancellation

The expanded form of `(x - 1)^7` at `x = √1.000002 ≈ 1 + 10⁻⁶` is about `10⁻⁴²`, while its
terms are about `35`: binary64 rounding errors alone are about `10⁻¹⁴`, double-double ones
about `10⁻³⁰`. (With a rational `x` both precisions succeed, since closed rational expressions
are evaluated exactly by `norm_num` first.) -/

theorem poly7_upper : Real.sqrt 1.000002 ^ 7 - 7 * Real.sqrt 1.000002 ^ 6 +
    21 * Real.sqrt 1.000002 ^ 5 - 35 * Real.sqrt 1.000002 ^ 4 + 35 * Real.sqrt 1.000002 ^ 3 -
    21 * Real.sqrt 1.000002 ^ 2 + 7 * Real.sqrt 1.000002 - 1 < 1e-25 := by
  fail_if_success interval
  interval (precision := 128)

theorem poly7_lower : -1e-25 < Real.sqrt 1.000002 ^ 7 - 7 * Real.sqrt 1.000002 ^ 6 +
    21 * Real.sqrt 1.000002 ^ 5 - 35 * Real.sqrt 1.000002 ^ 4 + 35 * Real.sqrt 1.000002 ^ 3 -
    21 * Real.sqrt 1.000002 ^ 2 + 7 * Real.sqrt 1.000002 - 1 := by
  interval (precision := 128)

/-- `√(10²⁰ + 1) - 10¹⁰ = 1 / (√(10²⁰ + 1) + 10¹⁰) ≈ 5·10⁻¹¹`: `10²⁰ + 1` is not a binary64
number, so at precision 64 the difference is only known to lie in `[0, 8e-7]`. -/
theorem sqrt_cancel_upper : Real.sqrt (10 ^ 20 + 1) - 10 ^ 10 < 5.01e-11 := by
  fail_if_success interval
  interval (precision := 128)

theorem sqrt_cancel_lower : 4.99e-11 < Real.sqrt (10 ^ 20 + 1) - 10 ^ 10 := by
  interval (precision := 128)

/-! ### A box

The maximum of `x² - x/3` on `[1, 2]` is `10/3` at `x = 2`. With a margin of `10⁻¹⁸` the
64-bit check fails even with monotonicity (the endpoint value is rounded); at precision 128
plain bisection proves it (the box next to `x = 2` must be narrower than `10⁻¹⁸`). -/
theorem quad_box (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-18 := by
  fail_if_success interval
  interval (precision := 128) (depth := 70)

/-! ### Functions without a double-double implementation

`exp`, `log`, `sin`, `cos`, … are still accepted at precision 128, but evaluated with
Interval64 precision; the failure message says so. -/

theorem exp_box : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x - x ≤ 1.72 := by
  realfp (precision := 128)

/--
error: realfp (trust := kernel): via `interval`: interval (precision := 128): no certificate within depth 24 / 50000 boxes (1 evaluations); enclosure on the whole box: [1.718281828459045090795598298427649, 1.718281828459045534884808148490265], bound 1.71828182845904523536028747135; note: exp is evaluated with Interval64 precision (about 1e-16 relative) even at precision 128
-/
#guard_msgs in
example : Real.exp 1 - 1 ≤ 1.71828182845904523536028747135 := by realfp (precision := 128)

end RealFP.Examples.Precision128
