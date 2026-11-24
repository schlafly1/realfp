/-
`(precision := 128)`: intervals with 128-bit dyadic endpoints (`Interval128/Dyadic.lean`, about
38 significant digits) in `interval` and `realfp`. Every bound below is out of reach at the
default precision 64 (pinned by `fail_if_success`) and is proved with `decide +kernel` at
precision 128 (standard axioms only), except `sqrt2_native`, which uses `trust := native`.
`π` comes from the 40-digit bounds `RealFP.pi_gt_d40` / `pi_lt_d40` (`RealFPMathlib/PiBounds.lean`).

Elaboration times on the dev box (whole declaration, minus the file's import time), 64-bit attempt
/ 128-bit proof; in brackets the time before the dyadic kernel path (double-double `Float` spec):
* `sqrt2_gap_*`, `pi_upper`, `sqrt_cancel_*`   fails / under 0.5 s each  [under 1 s]
* `poly7_*`          fails / about 0.6 s each  [about 4 s]
* `quad_box`, `quad_box_30`  fails / under 0.2 s (one monotonicity step)  [bisection: about 31 s
  in milestone 1, about 1–1.5 s with the dyadic path and 60–100 boxes]
* `quad_box_30_bisect` (`deriv := false`)  about 2.6 s (100 boxes)
* `logistic_box`     about 0.3 s (one split, two monotonicity steps)
* `exp_box_30`, `log_box_30`  fails / about 1–2 s
* `pi_*_30`, `pi_sq_*` fails / under 0.5 s each  [`π` known to 20 digits only]
* `exp_one_*`, `log_two_*`, `exp_cancel`, `sin_cancel`, `log_cancel`  fails / under 0.3 s each
* `sin_one_*`, `cos_one_*`, `logb_two_ten`, `cosh_sinh_one`, `sin_cos_two`  fails / 0.2–0.9 s
* `exp_box`  about 1 s
  [before the 128-bit elementary functions, all of these but `exp_box` failed at 128 too]
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

/-- Interval64 gives `π < 3.14159265358979356`. -/
theorem pi_upper : Real.pi < 3.1415926535897932385 := by
  fail_if_success interval
  interval (precision := 128)

/-! ### `π` to 32 digits

`π = 3.14159265358979323846264338327950288…`: the bounds below have margins of about `10⁻³²`,
and `π²` must be known to about `10⁻³²` as well. -/

theorem pi_upper_30 : Real.pi < 3.14159265358979323846264338327951 := by
  fail_if_success interval
  interval (precision := 128)

theorem pi_lower_30 : 3.14159265358979323846264338327950 < Real.pi := by
  interval (precision := 128)

theorem pi_sq_upper : Real.pi ^ 2 < 9.869604401089358618834490999876152 := by
  interval (precision := 128)

theorem pi_sq_lower : 9.869604401089358618834490999876150 < Real.pi ^ 2 := by
  interval (precision := 128)

/-! ### Cancellation

The expanded form of `(x - 1)^7` at `x = √1.000002 ≈ 1 + 10⁻⁶` is about `10⁻⁴²`, while its
terms are about `35`: binary64 rounding errors alone are about `10⁻¹⁴`, 128-bit ones
about `10⁻³⁶`. (With a rational `x` both precisions succeed, since closed rational expressions
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

/-! ### Boxes: monotonicity and centred forms at 128

The maximum of `x² - x/3` on `[1, 2]` is `10/3` at `x = 2`. With a margin of `10⁻¹⁸` the
64-bit check fails even with monotonicity (the endpoint value is rounded). At precision 128 the
derivative `2x - 1/3 ≥ 0` is proved on the box and the bound is checked at `x = 2`: one
monotonicity step, two kernel evaluations. Plain bisection (`deriv := false`) needs about 100
boxes (the box next to `x = 2` must be narrower than the margin). -/
theorem quad_box (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-18 := by
  fail_if_success interval
  interval (precision := 128)

theorem quad_box_30 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-30 := by
  interval (precision := 128)

/-- The same by plain bisection (100 boxes at depth 110). -/
theorem quad_box_30_bisect (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) :
    x ^ 2 - x / 3 ≤ 10 / 3 + 1e-30 := by
  interval (precision := 128) (deriv := false) (depth := 110)

/-- Interior maximum `1/4` at `x = 1/2`: one split at `1/2`, then monotone on each half (all
exact in binary64 too, so precision 64 also proves this one). -/
theorem logistic_box (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 + 1e-30 := by
  interval (precision := 128)

/-! ### Elementary functions to about 30 digits

`exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `logb 2`, `logb 10` have 128-bit
implementations (Taylor series with argument reduction and proved remainder bounds,
`RealFPMathlib/I128DyTransc.lean`); point enclosures are about `10⁻³³` wide.
`e = 2.71828182845904523536028747135266…`, `log 2 = 0.69314718055994530941723212145817…`,
`sin 1 = 0.84147098480789650665250232163029…`, `cos 1 = 0.54030230586813971740093660744297…`. -/

theorem exp_one_upper : Real.exp 1 < 2.7182818284590452353602874713527 := by
  fail_if_success interval
  interval (precision := 128)

theorem exp_one_lower : 2.7182818284590452353602874713526 < Real.exp 1 := by
  interval (precision := 128)

theorem log_two_upper : Real.log 2 < 0.6931471805599453094172321214582 := by
  fail_if_success interval
  interval (precision := 128)

theorem log_two_lower : 0.6931471805599453094172321214581 < Real.log 2 := by
  interval (precision := 128)

theorem sin_one_upper : Real.sin 1 < 0.8414709848078965066525023216303 := by
  fail_if_success interval
  interval (precision := 128)

theorem sin_one_lower : 0.8414709848078965066525023216302 < Real.sin 1 := by
  interval (precision := 128)

theorem cos_one_upper : Real.cos 1 < 0.5403023058681397174009366074430 := by
  fail_if_success interval
  interval (precision := 128)

theorem cos_one_lower : 0.5403023058681397174009366074429 < Real.cos 1 := by
  interval (precision := 128)

/-- `log₂ 10 = 3.32192809488736234787031942948939…` -/
theorem logb_two_ten : Real.logb 2 10 < 3.3219280948873623478703194294894 := by
  fail_if_success interval
  interval (precision := 128)

/-! ### Cancellation with elementary functions

At precision 64 each of these is only known to about `10⁻¹⁶`. -/

/-- `exp(10⁻¹⁰) - 1 - 10⁻¹⁰ = 5·10⁻²¹ + 1.7·10⁻³¹ + …` -/
theorem exp_cancel : Real.exp (1 / 10 ^ 10) - 1 - 1 / 10 ^ 10 < 5.000001e-21 := by
  fail_if_success interval
  interval (precision := 128)

/-- `sin(10⁻⁸) - 10⁻⁸ = -1.6666…·10⁻²⁵` -/
theorem sin_cancel : -1.66667e-25 < Real.sin (1 / 10 ^ 8) - 1 / 10 ^ 8 := by
  fail_if_success interval
  interval (precision := 128)

/-- `log(1 + 10⁻¹²) - 10⁻¹² = -5·10⁻²⁵ + …` -/
theorem log_cancel : Real.log (1 + 1 / 10 ^ 12) - 1 / 10 ^ 12 < -4.9999e-25 := by
  fail_if_success interval
  interval (precision := 128)

/-- `cosh² 1 - sinh² 1 = 1`, up to `10⁻³⁰`. -/
theorem cosh_sinh_one : Real.cosh 1 ^ 2 - Real.sinh 1 ^ 2 < 1 + 1e-30 := by
  fail_if_success interval
  interval (precision := 128)

/-- `sin² 2 + cos² 2 = 1`, up to `10⁻³⁰`. -/
theorem sin_cos_two : 1 - 1e-30 < Real.sin 2 ^ 2 + Real.cos 2 ^ 2 := by
  fail_if_success interval
  interval (precision := 128)

/-! ### Transcendental boxes

`exp x - x` on `[0, 1]` is maximal at `x = 1` with value `e - 1 = 1.71828182845904523536028747135266…`.
The derivative `exp x - 1` is `≥ 0` on `[1/2, 1]` (one split, one monotonicity step); plain
bisection at depth 24 cannot reach the margin of about `10⁻³²`. -/
theorem exp_box_30 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x - x ≤ 1.7182818284590452353602874713527 := by
  fail_if_success interval
  fail_if_success interval (precision := 128) (deriv := false)
  interval (precision := 128)

theorem exp_box : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x - x ≤ 1.72 := by
  realfp (precision := 128)

/-- `log (1 + x) ≤ log 1.5 = 0.405465108108164381978013115464349…` on `[0, 1/2]`. -/
theorem log_box_30 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.log (1 + x) ≤ 0.4054651081081643819780131154644 := by
  fail_if_success interval
  interval (precision := 128)

/-! ### Functions without a 128-bit implementation

`arctan`, `atan2`, `tan`, `arcsin`, `arccos` and extension functions (and `log` on arguments
not known to be positive) are still accepted at precision 128, but evaluated with Interval64
precision; the failure message says so. -/

/--
error: realfp (trust := kernel): via `interval`: interval (precision := 128): no certificate within depth 24 / 50000 boxes (1 evaluations); enclosure on the whole box: [-3.061616997868382943065411628248267e-17, 8.040613248383182461171198926247642e-17], bound 0.0000000000000000000000001; note: arctan is evaluated with Interval64 precision (about 1e-16 relative) even at precision 128
-/
#guard_msgs in
example : Real.arctan 1 - Real.pi / 4 ≤ 1e-25 := by realfp (precision := 128)

end RealFP.Examples.Precision128
