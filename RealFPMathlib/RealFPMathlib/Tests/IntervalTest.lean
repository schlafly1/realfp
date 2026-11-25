/-
Tests for the `interval` tactic (`RealFPMathlib.IntervalTactic`).
Every proof is a single `decide +kernel` evaluation of the certificate checker
(no `native_decide`; `RealFPMathlibAxioms.lean` checks the axioms).
-/
import RealFPMathlib.Front

set_option maxHeartbeats 0

namespace RealFP.IntervalTests

-- polynomials, one variable
theorem t01 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * (1 - x) ≤ 1 := by interval
theorem t02 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * (1 - x) ≤ 1/4 + 1/100 := by interval
theorem t03 (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : x * x - x ≤ 3 := by interval
theorem t04 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 - 0.1 * x + 2 ≤ 3 := by interval
theorem t05 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 5/2) : x * (6 - x * x) ≤ 5.6578 := by interval
theorem t06 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 5/2) : 6 * x - x ^ 3 ≤ 5.6578 := by interval
theorem t07 (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 2) : 0 ≤ x ^ 2 ∧ x ^ 2 ≤ 4 := by interval
theorem t08 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 3) : x ^ 2 - 2 * x + 1 ≥ -0.01 := by interval
theorem t09 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : x ^ 4 - x ^ 2 + 1/4 ≥ -0.001 := by interval
theorem t10 (x : ℝ) (h0 : -3 ≤ x) (h1 : x ≤ 3) : x ^ 3 - 3 * x ∈ Set.Icc (-19 : ℝ) 19 := by
  interval

-- rational functions, sqrt, abs
theorem t11 (x : ℝ) (h0 : 1/2 ≤ x) (h1 : x ≤ 3) : 1 / x ≤ 2 := by interval
theorem t12 (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : x / (x + 1) < 1/2 + 1/100 := by interval
theorem t13 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 4) : Real.sqrt x ≤ (x + 1) / 2 + 1/100 := by interval
theorem t14 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 3) : |x - 1| ≤ 2 := by interval
theorem t15 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : 1.414 < Real.sqrt (x + 1) := by interval
theorem t16 (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 2) : (x ^ 2 + 1)⁻¹ ≤ 1 := by interval

-- exp / log / sin / cos
theorem t17 (x : ℝ) (h₀ : 1 ≤ x) (h₁ : x ≤ 2) : Real.exp x < 8 := by interval
theorem t18 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : Real.exp x - x ≥ 0.99 := by interval
theorem t19 (x : ℝ) (h0 : 1/2 ≤ x) (h1 : x ≤ 2) : Real.log x < x := by interval
theorem t20 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 3) : Real.sin x ≤ 1.01 := by interval
theorem t21 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : 0.84 < Real.sin x := by interval
theorem t22 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.cos x ≥ 0.5 := by interval
theorem t23 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sin x ≤ x + 1/50 := by interval
theorem t24 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp (Real.sin x) ≤ 2.32 := by interval
theorem t25 (x : ℝ) (h0 : 2 ≤ x) (h1 : x ≤ 3) : Real.log x ∈ Set.Icc (0.69 : ℝ) 1.1 := by
  interval

-- several variables
theorem t26 (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : 0 ≤ y ∧ y ≤ 1) : x * y ≤ 1 := by interval
theorem t27 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) : x ^ 2 + y ^ 2 ≤ 2 := by
  interval
theorem t28 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) : x * y - x - y ≥ -1.01 := by
  interval
theorem t29 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    x * y + y * z + z * x ≤ 3 := by interval
theorem t30 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    Real.sin x * Real.cos y ≤ 1.01 := by interval

-- no variables
theorem t32 : 1.414 < Real.sqrt 2 := by interval
theorem t33 : Real.exp 1 ≤ 2.7183 ∧ 2.7182 ≤ Real.exp 1 := by interval

-- touching bounds (derivatives: monotonicity, higher-order signs)
theorem d01 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : 1 + x ≤ Real.exp x := by interval
theorem d02 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2) : Real.sin x ≤ x := by interval
theorem d03 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x - x ^ 3 / 6 ≤ Real.sin x := by interval
theorem d04 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sin x ≤ x + 1/1000 := by interval
theorem d05 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : 1 - x ^ 2 / 2 ≤ Real.cos x := by interval
theorem d06 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.log (1 + x) ≤ x := by interval
theorem d07 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by interval
theorem d08 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 4) : Real.sqrt x ≤ (x + 1) / 2 := by interval
theorem d10 (x : ℝ) (h0 : -1/10 ≤ x) (h1 : x ≤ 1/10) : 0.985 ≤ Real.exp x - x := by interval
theorem d09 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sin x ≤ x + 1/1000 := by
  interval (deriv := false)

-- atan, atan2 (= Complex.arg), π
theorem f01 : 3.14159 < Real.pi ∧ Real.pi < 3.1416 := by interval
theorem f02 : Real.arctan 1 < 0.7854 := by interval
theorem f03 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.arctan x ≤ x := by interval
theorem f04 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x - x^3/3 ≤ Real.arctan x := by interval (order := 5)
theorem f05 (x y : ℝ) (hx : 1 ≤ x) (hx' : x ≤ 2) (hy : 1 ≤ y) (hy' : y ≤ 2) :
    0.46 ≤ Complex.arg (↑x + ↑y * Complex.I) ∧ Complex.arg (↑x + ↑y * Complex.I) ≤ 1.11 := by interval
theorem f06 (x y : ℝ) (hx : -2 ≤ x) (hx' : x ≤ -1) (hy : 1 ≤ y) (hy' : y ≤ 2) :
    2.03 ≤ Complex.arg (↑x + ↑y * Complex.I) := by interval
theorem f07 (x y : ℝ) (hx : -2 ≤ x) (hx' : x ≤ 2) (hy : -1 ≤ y) (hy' : y ≤ 1) :
    Complex.arg (↑x + ↑y * Complex.I) ≤ 3.1416 := by interval
theorem f08 : 4 * Real.arctan (1/5) - Real.arctan (1/239) < Real.pi / 4 + 1/10^10 := by interval

-- sinh, cosh, tanh, log2, log10
theorem h01 : 1.1752 < Real.sinh 1 ∧ Real.sinh 1 < 1.1753 := by interval
theorem h02 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : 1 ≤ Real.cosh x := by interval
theorem h03 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.tanh x ≤ x := by interval
theorem h04 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2) : x ≤ Real.sinh x := by interval
theorem h05 : 0.7615 < Real.tanh 1 ∧ Real.tanh 1 < 0.7616 := by interval
theorem h06 : Real.logb 2 1024 = 10 ∨ 9.99999 < Real.logb 2 1024 := by right; interval
theorem h07 : 0.30102 < Real.logb 10 2 ∧ Real.logb 10 2 < 0.30103 := by interval
theorem h08 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 8) : Real.logb 2 x ≤ x - 1/2 := by interval

-- tan, asin, acos
theorem a01 : 1.5574 < Real.tan 1 ∧ Real.tan 1 < 1.5575 := by interval
theorem a02 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.tan x := by interval
theorem a03 : 0.5235 < Real.arcsin 0.5 ∧ Real.arcsin 0.5 < 0.5236 := by interval
theorem a04 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 0.9) : x ≤ Real.arcsin x := by interval
theorem a05 : 1.0471 < Real.arccos 0.5 ∧ Real.arccos 0.5 < 1.0472 := by interval

-- options
theorem t31 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1/4 + 1/1000 := by
  interval (depth := 30) (maxBoxes := 100000)

-- (precision := 128): 128-bit dyadic endpoints (every node kind; small, kernel-checked)
theorem p01 : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by interval (precision := 128)
theorem p02 : 4.99e-11 < Real.sqrt (10 ^ 20 + 1) - 10 ^ 10 := by interval (precision := 128)
theorem p03 : Real.pi < 3.1415926535897932385 := by interval (precision := 128)
theorem p04 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 2) : |x| / (x ^ 2 + 1) + (x ^ 2 + 2)⁻¹ ≤ 2 := by
  interval (precision := 128)
theorem p05 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) :
    Real.log x + Real.exp x + Real.arctan x ≤ 10 := by
  interval (precision := 128)
theorem p06 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : x ^ 4 ≤ 1 ∧ 0 ≤ x ^ 2 := by
  interval (precision := 128)
theorem p07 (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : Real.sqrt x ≤ 1.01 := by
  realfp (precision := 128)
theorem p08 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-3 := by
  interval (precision := 128)
theorem p09 : 3.1415926535897932384626433832795 < Real.pi := by interval (precision := 128)
-- 128-bit elementary functions
theorem p10 : Real.exp 1 < 2.7182818284590452353602874713527 := by interval (precision := 128)
theorem p11 : 0.6931471805599453094172321214581 < Real.log 2 := by interval (precision := 128)
theorem p12 : Real.sin 1 < 0.8414709848078965066525023216303 ∧
    0.5403023058681397174009366074429 < Real.cos 1 := by interval (precision := 128)
theorem p13 : Real.cosh 1 ^ 2 - Real.sinh 1 ^ 2 < 1 + 1e-30 ∧ Real.tanh 1 < 0.761594155955764888119458282605 ∧
    Real.logb 10 2 < 0.301029995663981195213738894725 := by interval (precision := 128)
theorem p14 : Real.sin 1000 < 0.82687954053200256025588742911 := by interval (precision := 128)
-- 128-bit derivative certificates (monotonicity, split + monotonicity, two variables)
theorem p15 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-30 := by
  interval (precision := 128)
theorem p16 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1.718281828459045235360287471352 < Real.exp x - x + 1 := by
  interval (precision := 128)
theorem p17 (x y : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (h2 : 0 ≤ y) (h3 : y ≤ 1) :
    x * y - x - y ≤ 1e-30 := by
  interval (precision := 128)

theorem p18 : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp (precision := 128)
theorem p20 : sInf ((fun x : ℝ => x ^ 2 - x) '' Set.Icc 0 1) ∈ Set.Icc (-0.2500000000000000000001) (-0.2499999999999999999999) := by
  realfp (precision := 128)
theorem p21 : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by root_unique (precision := 128)
theorem p22 : ∃ x ∈ Set.Icc (0.6299605249474365 : ℝ) 0.6299605249474366,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, x ^ 4 - x ≤ y ^ 4 - y := by realfp (precision := 128)
/--
info: minimum ∈ [-0.250000000000000000000000000000009245, -0.25] (gap 0.00000000000000000000000000000000924, 210 boxes; 128-bit enclosures, not a proof)
attained near x ≈ 0.5
statements `realfp (precision := 128)` should prove:
  ∀ x ∈ Set.Icc (0 : ℝ) 1, -0.25000000000000000000000000000002 ≤ x ^ 2 - x
  ∃ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≤ -0.24999999999999999999999999999999
-/
#guard_msgs in
#realfp_min (precision := 128) (x ∈ Set.Icc (0 : ℝ) 1), x ^ 2 - x
theorem p23 : (!![1, 1; 1, 1 + 1 / 10 ^ 25] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  realfp (precision := 128)
theorem p19 : Real.exp 1 ≠ 2.71828182845904523536028747135 := by interval (precision := 128)

/-- `integral_bound` at 128 (Taylor models; a polynomial is exact up to rounding). -/
theorem p24 : (∫ x in (0 : ℝ)..1, (x ^ 3 - x + 1 / 3)) ≤ 0.0833333333333333333333334 := by
  realfp (precision := 128)

-- precision 128, fixed-point Taylor models with sin, cos, log, exp (certificate checked in the kernel)
theorem p25 : ∫ x in (0 : ℝ)..1, (Real.sin x + Real.log (1 + x)) ≤ 0.84599205525176 := by
  integral_bound (precision := 128)
theorem p26 : (0.84147098480789650665250232163 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.cos x := by
  integral_bound (precision := 128)

/-- error: interval: (precision := _) must be 64 (default, Interval64) or 128 (128-bit dyadic endpoints) -/
#guard_msgs in
example : (1 : ℝ) ≤ 2 := by interval (precision := 32)

end RealFP.IntervalTests
