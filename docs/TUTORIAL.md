# realfp tutorial

A hands-on guide to proving real-number facts in Lean 4 + Mathlib with realfp (Interval64).
The [reference](REFERENCE.md) is the reference: every operation, theorem name, kernel and
benchmark. This file is the path through it, from adding the dependency to proving minima,
roots and integrals, and on to writing your own certificates.

**Every Lean snippet below is compiled.** They all live, in order, in
[`RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean`](../RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean),
which is part of the default `lake build`. Printed output (`#eval`, `#realfp_min`, error
messages) is pinned there with `#guard_msgs`, so what you read here is what Lean prints. The
whole file checks in about 40 s on an 8-core x86-64 box (one `lean` process, imports included).

Contents

1. [Setup](#1-setup)
2. [Computing with intervals](#2-computing-with-intervals)
3. [First proofs with `realfp`](#3-first-proofs-with-realfp)
4. [Trust: what a proof depends on](#4-trust-what-a-proof-depends-on)
5. [The tactics in depth](#5-the-tactics-in-depth)
6. [Lower level: certificates by hand](#6-lower-level-certificates-by-hand)
7. [Troubleshooting, performance, limitations](#7-troubleshooting-performance-limitations)

---

## 1. Setup

realfp is two Lake packages in one repository:

| package | directory | depends on | import |
|---|---|---|---|
| `interval64` (core) | repo root | nothing (no Mathlib) | `import Interval64`, `import Interval128` |
| `realfp_mathlib` | `RealFPMathlib/` | core + Mathlib | `import RealFPMathlib` (theorems and tactics) |

If you only want fast, rigorous interval computation (no proofs about `ℝ`), use the core.
If you want theorems about Mathlib's reals, use `realfp_mathlib`.

**Versions.** Lean `leanprover/lean4:v4.36.0` and Mathlib tag `v4.36.0`. Your project must use
the same two, so copy `RealFPMathlib/lean-toolchain` into your project.

**Lakefile** of a Mathlib project that uses realfp:

```lean
import Lake
open Lake DSL

package «my_project»

-- Brings the core and Mathlib (v4.36.0) with it.
require realfp_mathlib from git
  "https://github.com/schlafly1/realfp" @ "main" / "RealFPMathlib"

@[default_target]
lean_lib MyProject
```

Or, with a local clone: `require realfp_mathlib from "path/to/realfp/RealFPMathlib"`. The path
form is how `RealFPMathlib/` itself requires the core and how the test consumer project is set
up. The git-with-subdirectory form is standard Lake syntax but has not been tested end to end
yet. Then:

```bash
lake update
lake exe cache get   # prebuilt Mathlib; never build Mathlib yourself
lake build
```

**C compiler and CPU.** The core compiles C kernels with `cc`:

- **x86-64:** use gcc as `cc` (Lean's bundled clang lacks `immintrin.h`). The default backend
  uses AVX-512 embedded rounding and needs a CPU with AVX-512F. On an x86 CPU without it,
  build the core with `lake build -Kbackend=rnerr` (the portable backend).
- **arm64 (Apple silicon, Graviton, DGX Spark…):** the portable round-to-nearest +
  exact-error-term backend is selected automatically; any C compiler works.

Both backends compute bit-identical results; the theorems do not depend on which one you use.

**`precompileModules`.** The core sets `precompileModules := true`, so `#eval`, the editor and
the tactics' searches run the compiled C kernels. You do **not** set it in your own project
(in a Mathlib project it would compile Mathlib to native code).

**Run Lean through Lake.** Use the editor, `lake build`, or `lake lean File.lean`. Plain
`lean` and `lake env lean` do not load the compiled kernels. Then `#eval` on an interval stops
with `Could not find native implementation of external declaration …`, and the tactics stop
with a message that says what is wrong and prints the two flags that fix it:

```
realfp: the compiled realfp code (C kernels) is not loaded in this Lean process, so the
certificate search cannot run (…). Run Lean through Lake: the editor, `lake build`, or
`lake lean File.lean`. With plain `lean` / `lake env lean`, pass:
--load-dynlib=…/.lake/build/lib/libleaninterval64.so --plugin=…/.lake/build/lib/libinterval64_Interval64.so
```

So `lake env lean --load-dynlib=<core>/.lake/build/lib/libleaninterval64.so
--plugin=<core>/.lake/build/lib/libinterval64_Interval64.so File.lean` works too (the dynlib
must come first). Lean cannot load the plugin by itself after start-up (it crashes), so the
flags are needed.

A first sanity check (`Tutorial.lean` §1):

```lean
#eval Interval64.Directed.backendOk ()   -- true: the compiled backend can run on this CPU
#eval Interval64.Directed.backendName    -- "avx512 (embedded rounding)" or "rn+err (…)"
```

## 2. Computing with intervals

File: `Tutorial.lean` §2. Reference: [reference](REFERENCE.md) sections
[Conversions and literals](REFERENCE.md#conversions-and-literals-interval64convlean),
[More interval operations](REFERENCE.md#more-interval-operations-interval64opslean),
[Transcendentals](REFERENCE.md#transcendentals-exp-log-sin-cos).

An `Interval64` is a pair of doubles `lo ≤ hi`. Every operation rounds the lower end down and
the upper end up, so the result contains the exact real result. Literals are **exact
decimals**: `0.1 : Interval64` is the two doubles around 1/10, unlike `0.1 : Float`.

`#eval` prints `[lo, hi]` with 17 significant digits per endpoint, which is enough to read each
double back exactly. `.exact` gives the endpoints as exact rationals (`none` for NaN or ±∞):

```lean
open Interval64

#eval (0.1 : Interval64)                    -- [0.099999999999999992, 0.10000000000000001]
#eval (0.1 : Interval64).exact
-- (some (7205759403792793 / 72057594037927936), some (3602879701896397 / 36028797018963968))
```

Arithmetic and the elementary functions (`sqrt`, `exp`, `log`, `sin`, `cos`, `atan`, `pi`,
`sinh`…, `tan`, `asin`, `acos`, `rpow`; correctly rounded via CORE-MATH):

```lean
#eval (0.1 : Interval64) + 0.2              -- [0.29999999999999993, 0.30000000000000004]
#eval Interval64.sqrt 2                     -- [1.4142135623730949, 1.4142135623730951]
#eval Interval64.exp 1                      -- [2.7182818284590451, 2.7182818284590455]
#eval Interval64.pi                         -- [3.1415926535897931, 3.1415926535897936]
#eval Interval64.sin (ofRatInterval 1 2)    -- [0.8414709848078965, 1]
```

Dot notation works: for `X : Interval64`, `X.sqrt` is `Interval64.sqrt X`, and so on.
`X.widthRat` is the exact width `hi − lo` as a rational (`X.width` is the rounded-up `Float`).

```lean
def X : Interval64 := ofRatInterval 1 2
#eval X.sqrt                                -- [1, 1.4142135623730951]
#eval X.sqrt.widthRat                       -- some (1865452045155277 / 4503599627370496)
```

`ofRatInterval a b` is the outward-rounded `[a, b]`. Interval arithmetic has the
*dependency problem*: each occurrence of `X` is treated independently.

```lean
#eval ofRatInterval 0 1 * ofRatInterval 0 1 - ofRatInterval 0 1
-- [-1, 1]   (true range: [-1/4, 0])
```

The tactics below fight this by bisection and derivative information. For hand-written code,
`square X` and `pown X n` are dependency-aware.

Edge cases never raise errors. An empty result is `[NaN, NaN]` (it contains no real number),
and division by an interval containing 0 gives the whole line:

```lean
#eval Interval64.sqrt (-1)                       -- [NaN, NaN]
#eval (1 : Interval64) / ofRatInterval (-1) 1    -- [-inf, inf]
```

**Interval128** has double-double endpoints (about 106 bits) and the same design (Lean spec,
C runtime, enclosure theorems in `RealFP.I128`). It prints 34 significant digits:

```lean
open Interval128 in
#eval Interval128.sqrt 2
-- [1.414213562373095048801688724209682, 1.414213562373095048801688724209706]
-- Widths of √2: one ulp (2⁻⁵²) for Interval64, about 2⁻¹⁰⁵ for Interval128.
#eval (Interval64.sqrt 2).widthRat               -- some (1 / 4503599627370496)
open Interval128 in
#eval (Interval128.sqrt 2).widthRat              -- some (1 / 40564819207303340847894502572032)
```

Interval128 has `+ - * /`, `sqrt` and conversions; the tactics use Interval64 only. Its type is
`Interval128.Interval128` (write `Interval128` after `open Interval128`); dot notation works
there too.

## 3. First proofs with `realfp`

File: `Tutorial.lean` §3. Reference: [`realfp`](REFERENCE.md#realfp-one-tactic-for-kernel-checked-real-numerics-mathlib-layer).

`import RealFPMathlib` gives one tactic, `realfp`, which looks at the goal and picks a
backend. (`import RealFPMathlib.Front` gives just the tactics.)

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp
example (x : ℝ) (h₀ : 1 ≤ x) (h₁ : x ≤ 2) : Real.exp x < 8 := by realfp
example : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x * y - x - y ≥ -1.01 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≠ 2 * x := by realfp
```

What happens: the goal is *reified* into an expression tree (`IExpr`); a search runs natively
(untrusted, fast, using the C kernels) and produces a certificate, for example a tree of boxes
with a proof method for each; the Lean kernel then re-checks the certificate by
`decide +kernel` against a verified evaluator. Only that check is part of the proof.

Variables need numeral bounds, given either as `∀ x ∈ Set.Icc a b` or as hypotheses
`a ≤ x`, `x ≤ b` in the context. Numerals can be anything `norm_num` evaluates to a rational
(`0.1`, `1/3`, `10^6`). Any number of variables is allowed.

Bounds that **touch** (equality somewhere on the box) are fine, because the certificates can
use the sign of a derivative (monotonicity) rather than plain bisection:

```lean
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 + x ≤ Real.exp x := by realfp
```

### Reading failure messages

When the statement is false, `realfp` says so and shows where:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 4, x * Real.exp (-x) ≤ 0.3678 := by realfp
```

```
realfp (trust := kernel): via `interval`: no certificate within depth 24 / 50000 boxes
(1589 evaluations): the bound is false: the maximum is ≈ 0.367879441171 at x ≈ 1 (rigorous
value at that point), beyond 0.3678
```

The message names the backend (`interval`), the trust mode, the search budget, and either a
counterexample (with your variable names) (here the max of `x e⁻ˣ` is `1/e ≈ 0.36788`) or how small the margin is.
If the bound is true but tight, raise `depth`/`maxBoxes`, or loosen the constant.

### Options

Options go after the tactic, in any order:

| option | default | meaning |
|---|---|---|
| `(trust := kernel \| native)` | `kernel` | how the certificate is checked (§4) |
| `(depth := n)` | 24 | maximum bisection depth |
| `(maxBoxes := n)` | 50000 | maximum number of boxes in the search |
| `(order := n)` | 3 | how many derivatives deep the monotonicity proofs may go |
| `(deriv := false)` | on | plain bisection, no derivative certificates |
| `(chunk := n)` | 32 | boxes per kernel `decide` call; smaller keeps kernel memory bounded |
| `(precision := 64 \| 128)` | 64 | endpoint precision: Interval64 or 128-bit dyadic endpoints (§5) |

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by
  realfp (depth := 30) (maxBoxes := 100000) (chunk := 16)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ 1/4 + 1/100 := by realfp (deriv := false)
```

`set_option realfp.native true` sets the trust default for a whole section or declaration.

The table is for the `interval` backend (and optimisation). The other backends take their own
options (§5): `integral_bound` takes `trust`, `order` and `maxBoxes`; `pos_def` takes only
`trust`; `root_exists`/`root_unique` take the same options as `interval`. The same syntax
works whether you call `realfp` or the backend by name, and an option the chosen backend
cannot use is an error, not silently ignored:

```lean
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by realfp (depth := 30)
```

```
realfp (trust := kernel): via `pos_def`: option `depth` does not apply (pos_def takes only `trust`)
```

## 4. Trust: what a proof depends on

File: `Tutorial.lean` §4. Reference: [Proofs and trust](REFERENCE.md#proofs-and-trust).

By default (`trust := kernel`) every certificate check is closed by `decide +kernel`: the Lean
kernel evaluates the checker itself. The result depends only on Lean's three standard axioms:

```lean
theorem sin_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp

#print axioms sin_le
-- 'RealFP.Examples.Tutorial.sin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

With `trust := native` the same checks are closed by `native_decide`. That is much faster on
large certificates, but `#print axioms` shows an extra axiom, and the proof now trusts the Lean
compiler and the compiled C kernels:

```lean
theorem native_demo : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by
  realfp (trust := native)

#print axioms native_demo
-- 'RealFP.Examples.Tutorial.native_demo' depends on axioms: [propext,
--  Classical.choice,
--  Quot.sound,
--  native_demo._native.native_decide.ax_1_7]

set_option realfp.native true in
theorem native_demo' : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x ≥ 1/2 := by realfp
```

Mathlib does not accept `native_decide`, so use `kernel` for anything you want to upstream or
show to a skeptical audience, and `native` for exploration or very large checks.

What is trusted in each mode:

- **Always proved:** the enclosure theorems (directed rounding really encloses `+ − × ÷ √`,
  exp, log, sin, cos, …, as theorems about the Lean specification), the evaluator, the
  certificate checkers, and the tactics' soundness lemmas. Nothing uses `sorry`.
- **`kernel` mode:** nothing else. The C code is used only by the untrusted search.
- **`native` mode:** additionally the Lean compiler and the C kernels (AVX-512 or RN+err).
  Those kernels are checked differentially against the Lean specification (bit-for-bit, on
  millions of cases including hard-to-round ones), but that is testing, not proof.

**Axiom audit.** `RealFPMathlib/RealFPMathlib/AxiomAudit.lean` runs in every default
`lake build`. It walks every `RealFP.*` theorem (including this tutorial) and fails the build
if one uses anything beyond the standard axioms, except that `RealFP.Demo.*` and
`RealFP.Examples.*` may use `native_decide`; `sorryAx` is never allowed. Run it alone with
`RealFPMathlib/scripts/audit_axioms.sh`. You can copy the idea for your own namespace.

## 5. The tactics in depth

File: `Tutorial.lean` §5. More examples: `Examples/Roots.lean`, `Examples/Optimization.lean`,
`Examples/IntegralTactic.lean`, `Examples/MatrixPD.lean`, `Tests/IntervalTest.lean` (all under
`RealFPMathlib/RealFPMathlib/`).

`realfp` routes to one of these backends; each can also be called by name.

| goal | backend |
|---|---|
| `≤ < ≥ > ≠`, `∈ Set.Icc`, `∧`, `∀ x ∈ box` | `interval` |
| anything containing `∫ x in a..b, f x` | `integral_bound` |
| `∃ x ∈ box, f x = g x` / `∃! …` (one variable or a square system) | `root_exists` / `root_unique` |
| `M.PosDef` for a concrete rational matrix | `pos_def` |
| `∃ m, ∀ …`, `sInf`/`sSup`, witnesses `∃ x, f x ≤ c`, argmin | optimisation |

All backends share one expression language: `+ − × ÷ ⁻¹`, `^ n` (numeral `n`), `Real.sqrt`,
`exp`, `log`, `logb 2`, `logb 10`, `sin`, `cos`, `tan`, `arctan`, `arcsin`, `arccos`, `sinh`,
`cosh`, `tanh`, `Real.pi`, rational numerals, plus `|x|` and atan2
(`Complex.arg (↑x + ↑y * I)`) for inequalities only. Registered functions (§6, "Adding a
function"; import their `RealFPMathlib.Extensions.*` module, included in `import RealFPMathlib`):
`RealFP.erf`, `Real.sinc`, `Real.artanh` (on `(-1, 1)`), `Real.arsinh`.

### `interval`: bounds on a box

```lean
example (x : ℝ) (h0 : 2 ≤ x) (h1 : x ≤ 3) : Real.log x ∈ Set.Icc (0.69 : ℝ) 1.1 := by interval
```

The search bisects the widest variable. On each box it tries, in order: plain interval
evaluation; monotonicity in a variable whose partial derivative has a visible sign (then only
one face is checked); a centred form `f(m) + f′(X)(X − m)`; monotonicity with the derivative's
sign proved recursively (up to `order` derivatives); otherwise it splits. Derivatives are
symbolic (`IExpr.diff`) and proved correct against Mathlib's `HasDerivAt`. Trace with
`set_option trace.interval true`.

### Precision 128: bounds below binary64 resolution

Interval64 endpoints are binary64 numbers, so no bound can be tighter than about `1e-16`
relative. `(precision := 128)` makes `interval` (and `realfp` on interval goals) evaluate
with 128-bit dyadic endpoints `m · 2^e` (about `3e-39` relative, rounded outward after
every operation):

```lean
example : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by realfp (precision := 128)
example : 4.99e-11 < Real.sqrt (10 ^ 20 + 1) - 10 ^ 10 := by interval (precision := 128)
example : Real.pi < 3.1415926535897932385 := by
  fail_if_success interval      -- binary64: π < 3.14159265358979356 is the best it can do
  interval (precision := 128)
```

What is computed at 128 bits: `+ - * / ⁻¹ √ |·| ^n`, rational constants, `π` (40-digit
bounds proved with Mathlib's `pi_lower_bound` / `pi_upper_bound`, `RealFP.pi_gt_d40` /
`pi_lt_d40`), and `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`, `logb 2`, `logb 10`
(Taylor series with argument reduction and proved remainders, about `1e-33` relative):

```lean
example : Real.exp 1 < 2.7182818284590452353602874713527 := by interval (precision := 128)
example : 0.6931471805599453094172321214581 < Real.log 2 := by interval (precision := 128)
example : Real.exp (1 / 10 ^ 10) - 1 - 1 / 10 ^ 10 < 5.000001e-21 := by
  fail_if_success interval      -- binary64: exp (1e-10) is only known to about 2e-16
  interval (precision := 128)
```

`arctan`, `tan`, `arcsin`, `arccos`, `atan2` and registered functions are accepted but
evaluated with Interval64 precision, and a failure message says so. The search is plain
bisection at dyadic midpoints (no derivative certificates yet); the kernel check costs about
10–30 ms per box for arithmetic and 0.2–0.7 s per elementary-function evaluation, so it is
best for tight bounds on small boxes. The same `trust` options apply. Other backends
(roots, optimisation, integrals, `≠`) reject `(precision := 128)` for now. More
examples: `RealFPMathlib/Examples/Precision128.lean`.

### `integral_bound`: definite integrals

```lean
example : (0.7468 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by realfp
example : (∫ x in (1 : ℝ)..2, 1 / x) ∈ Set.Icc (0.6931 : ℝ) 0.6932 := by integral_bound
example : (∫ x in (1 : ℝ)..2, 1 / x) ∈ Set.Icc (0.6931 : ℝ) 0.6932 := by
  integral_bound (order := 6) (maxBoxes := 64)
```

Adaptive Taylor quadrature of order 2–8 with a Lagrange remainder on each cell. By default it
tries orders 2, 4, 6, 8 with up to 512 cells; `(order := n)` (2, 4, 6 or 8) fixes the order and
`(maxBoxes := n)` caps the cells. Limits are
rational numerals and must be exact doubles; the integrand must be differentiable on the
interval (no `|x|`). Trigonometric integrands needing many cells are slow under `kernel`
(about 1 s per kernel `sin`/`cos`).

### `root_exists` / `root_unique`: equations

```lean
example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by root_exists
example : ∃! x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by root_unique
example : ∃ x ∈ Set.Icc (1.3247 : ℝ) 1.3248, x ^ 3 - x - 1 = 0 := by realfp
```

One variable: existence is a sign change (intermediate value theorem); uniqueness adds a
derivative enclosure of one sign on the whole interval (strict monotonicity).

Systems (`ℝ × ℝ`, `ℝ × ℝ × ℝ`, `Fin n → ℝ`, as many equations as unknowns) use the
**Krawczyk** operator: if `x ↦ x − Y F(x)` maps the box into itself and contracts, Banach's
fixed-point theorem gives exactly one zero.

```lean
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by realfp
example : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 3 ∧ p.2 ∈ Set.Icc (0 : ℝ) 3 ∧
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 = p.2 := by realfp
```

For `∃`, Newton finds an approximate root anywhere in the box and Krawczyk is checked on a
tiny box around it. For `∃!`, Krawczyk must contract on the **whole** box you give, so wide
boxes fail, with a useful hint:

```lean
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 3 ∧ p.2 ∈ Set.Icc (0 : ℝ) 3 ∧
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 = p.2 := by realfp
```

```
realfp (trust := kernel): via `root_unique`: no certificate for the system on [0, 3] × [0, 3]:
• Krawczyk on the whole box [0, 3] × [0, 3]: centre = midpoint: contraction factor
  ‖I - Y·J(X)‖∞ ≈ 1.000000 ≥ 1 (box too wide or Jacobian too ill-conditioned); centre =
  Newton point: contraction factor ‖I - Y·J(X)‖∞ ≈ 1.121320 ≥ 1 (…)
 An approximate root is (1.414214, 1.414214); a smaller box around it usually works for `∃!`.
```

Box bounds can also be written as separate inequalities in any order
(`-1/20 ≤ p.1 ∧ p.1 ≤ 1/20 ∧ …`); see `Examples/Roots.lean`.

### `pos_def`: positive-definite matrices

```lean
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by realfp
example : (!![4, 1, 0; 1, 3, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by pos_def
```

A floating-point congruence `X ≈ L⁻¹` (from Cholesky, untrusted) is checked in the kernel:
`X M Xᵀ` must be strictly diagonally dominant with positive diagonal. Entries must be
rational numerals. The only option is `trust`. `Examples/MatrixPD.lean` does the 10×10 Hilbert matrix (condition number
≈ 1.6·10¹³) and eigenvalue lower bounds.

### Optimisation: minima and maxima over a box

Start by *asking* what the minimum is. `#realfp_min` / `#realfp_max` run branch and bound and
print statements to prove (they produce no proof themselves):

```lean
#realfp_min (x ∈ Set.Icc (-1:ℝ) 1), x ^ 2 + Real.sin x
```

```
minimum ∈ [-0.232465575843, -0.232465575159] (gap 0.000000000683762102494, 77 boxes; estimate from the enclosures, not a proof)
attained near x ≈ -0.450183611364
statements `realfp` should prove:
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, -0.232467 ≤ x ^ 2 + Real.sin x
  ∃ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + Real.sin x ≤ -0.232464
```

Then prove them, or one of the other shapes:

```lean
-- the two suggested statements: a lower bound and a witness
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -0.232467 ≤ x ^ 2 + Real.sin x := by realfp
example : ∃ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + Real.sin x ≤ -0.232464 := by realfp
-- an exact minimum (attained at x = 1/2)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≥ -1/4 := by realfp
-- discovery: realfp chooses m itself
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + Real.sin x ≥ m := by realfp
-- Mathlib-style statements about sInf / sSup of an image
example : sInf ((fun x : ℝ => x ^ 2 - x) '' Set.Icc 0 1) = -1/4 := by realfp
example : |sInf ((fun x : ℝ => x ^ 2 + Real.sin x) '' Set.Icc (-1) 1) - (-0.2324656)| ≤ 1/10^6 := by
  realfp
-- a minimiser exists (compactness + continuity by fun_prop)…
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≤ y ^ 2 - y := by realfp
-- …and lies in a small interval (localisation, one variable)
example : ∃ x ∈ Set.Icc (-0.451 : ℝ) (-0.45), ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    x ^ 2 + Real.sin x ≤ y ^ 2 + Real.sin y := by realfp
-- several variables (Himmelblau)
example : ∀ x ∈ Set.Icc (-5 : ℝ) 5, ∀ y ∈ Set.Icc (-5 : ℝ) 5,
    (x^2 + y - 11)^2 + (x + y^2 - 7)^2 ≥ -1/100 := by realfp
```

How each shape is proved: a `∀` bound is a certificate as in `interval` (plus multivariate
centred forms); a witness is a short rational point found by branch and bound and checked at
that point; `sInf`/`sSup` statements are reduced by Mathlib lemmas (`le_csInf` etc.) to a
bound plus a witness, so an exact `sInf = v` needs `v` to be attained at a rational point.
`Examples/Optimization.lean` has the six-hump camel, Rosenbrock and 3-variable problems.

## 6. Lower level: certificates by hand

File: `Tutorial.lean` §6. Reference: [Mathlib layer](REFERENCE.md#mathlib-layer-optional-theorems-over-ℝ),
[Computer-assisted-proof toolkit](REFERENCE.md#computer-assisted-proof-toolkit-pd-matrices-polynomials-quadrature),
[Kernel fast path](REFERENCE.md#kernel-fast-path-interval64kernel-interval64proofskernellean).

The tactics cover most goals. When they don't (a custom algorithm, a huge certificate, a
statement that isn't a box inequality), you build the proof yourself from three ingredients:

1. **Enclosure theorems** in the `RealFP` namespace, one per operation: if `x ∈ X` and
   `y ∈ Y` then `x + y ∈ X + Y`, and so on. They are `RealFP.Iv.add_mem`, `Iv.sub_mem`,
   `Iv.mem_mul`, `Iv.mem_div` (`y ≠ 0`), `Iv.mem_sqrt` (`0 ≤ x`), `Iv.exp_mem`,
   `Iv.log_mem` (`0 < x`), `Iv.sin_mem`, `Iv.cos_mem`, `Iv.atan_mem`, … in `∈` form, and
   `add_mem_toSet`, `mem_toSet_mul`, `mem_toSet_div`, `mem_toSet_sqrt`, … in `toSet` form
   (`x ∈ X` is `x ∈ X.toSet`). None needs finite endpoints.
2. **Literal enclosures:** `mem_toSet_ofRatInterval`, `ratCoe_mem`, `ofNat_mem`,
   `ofScientific_mem` (`(0.1 : ℝ) ∈ (0.1 : Interval64)`).
3. **A decidable check** on concrete doubles, closed by `decide +kernel` (or `native_decide`).

### One interval evaluation

```lean
def I : Interval64 := ofRatInterval (1/10) (3/10)   -- [1/10, 3/10], rounded outward
def J : Interval64 := I * I + I                      -- one interval evaluation of x*x + x

theorem J_hiLe : J.hiLe (13/32) = true := by decide +kernel

theorem sq_add_le (x : ℝ) (hx : x ∈ Set.Icc (1/10 : ℝ) (3/10)) : x * x + x ≤ 13/32 := by
  have hxI : x ∈ I :=
    mem_toSet_ofRatInterval (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  have hJ : x * x + x ∈ J := Iv.add_mem (Iv.mem_mul hxI hxI) hxI
  have h := le_of_mem_hiLe hJ J_hiLe
  push_cast at h
  exact h
```

`X.hiLe q` is the Boolean check "the upper endpoint is a finite double and at most the rational
`q`" (`X.loGe q` is the mirror image); `RealFP.le_of_mem_hiLe` / `ge_of_mem_loGe` turn it into
`x ≤ q` / `q ≤ x` for every `x ∈ X`. (The older `le_of_mem_toSet_of_hi_le` takes the
comparison `X.hi ≤ c` on doubles plus a separate `bitsToRat?` fact; it still works.)

The kernel evaluates `J` by running the Lean specification of IEEE directed rounding. For
anything bigger than a few dozen operations, use the bit-pattern ("`KF`/`KI`") evaluator that
the tactics use: it computes the same doubles with GMP-accelerated `Nat` arithmetic, is proved
equal to the specification, and is 10–20× faster in the kernel. `IExpr` (reflected
expressions), `evalK` and the bisection checkers `checkK` / `checkD` live in
`Interval64/Kernel/Reflect.lean` and `Deriv.lean`, with soundness in
`RealFPMathlib/IntervalSound.lean` and `IntervalDeriv.lean`.

### Matrices, polynomials, quadrature

The toolkit's checkers can be called directly. After `open RealFP`, the kernel-path names
are short: `KI`, `IExpr` (and `IExpr.denote`), `ofRatFn`, `PDCert`, `pdCheckK`, `quadK`,
`quadBound`, `posDef_of_ratMat`, `posDef_of_pdCheckK`, `integral_bounds_of_quadBound`, … (aliases
from `RealFPMathlib/Kernel.lean`; the long names such as `Interval64.KF.KM.ofRatFn` and
`RealFP.KM.posDef_of_ratMat` still work). Positive definiteness with a precomputed
certificate (`ki_lit%` rounds rational entries to literal bit patterns, `pd_certs%` computes
the congruence natively; the kernel re-checks both):

```lean
open RealFP

def hq (i j : ℕ) : ℚ := 1 / ((i : ℚ) + j + 1)
def H4 : Array KI := ki_lit% (ofRatFn 4 hq)

theorem hilbert4_posDef : (Matrix.of fun i j : Fin 4 => ((hq i j : ℚ) : ℝ)).PosDef :=
  posDef_of_ratMat (A := H4) (c := pd_certs% 4 H4) (by decide +kernel)
    (by decide +kernel) (fun i j _ _ => by simp [hq, add_comm])
```

Taylor quadrature with an explicit rule (order `K = 4`, 4 uniform cells) on a reflected
integrand:

```lean
def g : IExpr := .exp (.neg (.mul (.var 0) (.var 0)))

theorem gauss_bounds :
    (7468 / 10000 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 7469 / 10000 := by
  have h := integral_bounds_of_quadBound (e := g) (K := 4) (a := bits% 0) (b := bits% 1)
    (cs := cells% 0 1 4) (qa := 0) (qb := 1) (ql := 7468 / 10000) (qh := 7469 / 10000)
    (by decide +kernel)
  have e : ∀ x : ℝ, g.denote [x] = Real.exp (-x ^ 2) := fun x => by simp [g, IExpr.denote, sq]
  simp only [e] at h
  push_cast at h
  exact h
```

Other building blocks ([reference](REFERENCE.md) toolkit section): `IPoly` polynomial arithmetic and sign
checks, Bernstein range enclosures (`Examples/Bernstein.lean`), 2D quadrature over rectangles
with Fubini (`Examples/Quad2.lean`, `Examples/Taylor2.lean`), eigenvalue lower bounds and
Loewner order (`Examples/MatrixPD.lean`), extended division `divSplit`
(`Examples/Split.lean`).

### Splitting large checks across declarations

Kernel cost grows faster than linearly inside **one** declaration (the kernel's caches grow),
so a big check is cheaper as many small theorems glued together:

```lean
theorem piece₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x - 2 * x ≥ 0.6 := by realfp
theorem piece₂ : ∀ x ∈ Set.Icc (1 : ℝ) 2, Real.exp x - 2 * x ≥ 0.6 := by realfp

theorem glued : ∀ x ∈ Set.Icc (0 : ℝ) 2, Real.exp x - 2 * x ≥ 0.6 := by
  intro x ⟨h0, h2⟩
  rcases le_total x 1 with h | h
  · exact piece₁ x ⟨h0, h⟩
  · exact piece₂ x ⟨h, h2⟩
```

Separate theorems also build **in parallel** (in separate files) and are cached by Lake.
(`chunk := n` does a version of this inside one tactic call.)

Lessons from the two research showcases (an 8-point Coulomb energy minimisation and a
four-body central-configuration proof; see [COMPARISONS.md](COMPARISONS.md)):

- **Make the kernel check, not search.** Compute everything you can natively (search,
  preconditioners, approximate inverses, midpoints) and pass it to the checker as literal
  data, so the kernel only verifies.
- **Store data as literals the kernel reads cheaply:** `Nat`/`Int` (GMP-backed), not
  `String`, `Float` structures or long `List Rat`. Packing several numbers into one big `Nat`
  works well.
- **Fixed-point integer intervals** are the fastest kernel arithmetic. The 8-point showcase
  used intervals of `Int`s scaled by 2⁻¹⁶⁰ (≈ 0.3 ms per operation in the kernel) instead of
  doubles, and checked polynomial identities by Kronecker substitution (evaluate at
  `B = 2¹⁶⁰` and compare one big integer). That code lives in the showcase repository, not
  in realfp yet.
- **One file per batch, many declarations per file,** then let `lake build -j` use all cores.
  The kernel-only 8-point proof took 6:50 on 20 cores; the same with `native_decide` took 0:55.
- Kernel checking costs roughly 10⁵× native evaluation. Estimate before committing: count the
  interval operations natively, multiply by ~0.3 ms.
- `simp`/`of_decide_eq_true` on a Boolean check can trigger evaluation during elaboration;
  state the check as a `Prop` and prove it with `decide +kernel`.

### Adding a function

A new real function can be plugged into every tactic (`realfp`, `interval` with its derivative
modes, `root_exists`/`root_unique`, `integral_bound`, the optimisation forms, `#realfp_min`)
without touching the library: register it with `@[realfp_fn]` (`RealFPMathlib/Registry.lean`).
The complete example is `RealFPMathlib/Extensions/Erf.lean` (Mathlib has no `erf`, so it is
defined there by its integral and everything is proved from that definition).

You supply three things:

1. the function, a constant `f : ℝ → ℝ`;
2. an `ExtFn` (core, Mathlib-free): the kernel enclosure `evK : KI → KI`, a domain test `domK`
   (where `f` is differentiable) and the derivative as an `IExpr` template in `var 0` using
   built-in functions only. `ExtFn.ofMono` builds the enclosure of a monotone function from
   rational point bounds `fl q ≤ f q ≤ fu q` and global bounds; a C fast path for the native
   search can be attached to `evK` with `@[implemented_by]`;
3. a proof `ExtSound f D F` (enclosure, domain and derivative), tagged `@[realfp_fn]`.

```lean
noncomputable def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)
def erfDeriv : IExpr := .mul (.div (.rat 2) (.sqrt .pi)) (.exp (.neg (.pow (.var 0) 2)))
def erfExt : ExtFn :=
  ExtFn.ofMono "erf" erfLo erfHi (-1) 1 (fun _ => true) erfDeriv
@[realfp_fn] theorem erf_sound : ExtSound erf (fun _ => True) erfExt :=
  ExtSound.ofMono erf_monotone erfLo_le le_erfHi
```

Here `erfLo`/`erfHi` are rational bounds from the alternating Taylor series of `e^{-t²}`
integrated term by term (`Erf.P_le_Φ`, `Erf.Φ_le_P`). After that:

```lean
example : (0.5204 : ℝ) < erf (1/2) ∧ erf (1/2) < 0.5205 := by realfp
example : ∃! x ∈ Set.Icc (0 : ℝ) 1, erf x = 1/2 := by realfp
example : (∫ x in (0 : ℝ)..1, erf x) ∈ Set.Icc (0.4860 : ℝ) 0.4861 := by integral_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 3, erf x - x / 2 ≤ 0.346912 := by realfp
```

The proofs still depend only on `propext`, `Classical.choice`, `Quot.sound`: the tactics state
every certificate for a table built from the registered `ExtFn`s, and its soundness comes from
your `ExtSound` theorems. For the optimisation forms that need continuity, also tag a
continuity lemma `@[fun_prop]` (`continuous_erf`). Limitations: the function must be unary and
applied as `f a`; its derivative template must use built-in functions only (no `f` itself);
registered functions are evaluated in Lean, not by the C tape, so searches over them are
slower; `integral_bound` uses Taylor orders ≤ 4 for them; 2D quadrature and the adaptive
`Interval64.Quad` rules do not support them.

Three more registered functions use Mathlib's definitions directly:

| function | file | enclosure | derivative template | domain `D` |
|---|---|---|---|---|
| `Real.arsinh` | `Extensions/Arsinh.lean` | monotone; series `q - q³/6 (+ 3q⁵/40)` for `\|q\| ≤ 2⁻¹²`, else `log (\|q\| + √(1+q²))` | `1/√(1+x²)` | all `x` |
| `Real.artanh` | `Extensions/Artanh.lean` | monotone on `(-1, 1)`; series `q + q³/3 (+ q⁵/4)` for small `q`, else `½ log ((1+q)/(1-q))`; `whole` on boxes touching `±1` | `1/(1-x²)` | `-1 < x < 1` |
| `Real.sinc` | `Extensions/Sinc.lean` | even, decreasing in `\|x\|` on `[0, 3]`: endpoint values (`1` at `0`, `sin q / q` else); `sin x / x` on boxes away from `0` | `(x cos x - sin x)/x²` | `x ≠ 0` |

`ExtFn.ofMonoK P guard domK deriv` is the helper for the first two: `P b : KI` encloses `f` at
the double with bit pattern `b`, usually a built-in expression evaluated at that point:

```lean
def arsinhExt : ExtFn := ExtFn.ofMonoK "arsinh" Arsinh.pt (fun _ => true) (fun _ => true) arsinhDeriv
```

`sinc`'s template is undefined at `0`, so boxes containing `0` fail the domain check and only
zeroth-order (plain interval) bounds are available there: a bound that is tight *at* `0` (e.g.
`sinc x ≤ 1 - x²/7` near `0`) cannot be proved, and `integral_bound` cannot integrate over a range containing `0` (every cell
needs the derivative). Examples (`Examples/{Arsinh,Artanh,Sinc}.lean`):

```lean
example : (9.99999999983e-6 : ℝ) < arsinh 1e-5 ∧ arsinh 1e-5 < 9.99999999984e-6 := by realfp
example : ∃! x ∈ Set.Icc (0 : ℝ) 0.9, artanh x = 1 := by realfp
example : ∃ x ∈ Set.Icc (1.89549 : ℝ) 1.8955, sinc x = 1/2 := by root_exists
example : (∫ x in (1 : ℝ)..2, sinc x) ∈ Set.Icc (0.655 : ℝ) 0.663 := by integral_bound
```

## 7. Troubleshooting, performance, limitations

**Common problems**

| symptom | fix |
|---|---|
| `unknown tactic realfp` | `import RealFPMathlib` (or `RealFPMathlib.Front`) |
| `Could not find native implementation of external declaration …`, or "the compiled realfp code (C kernels) is not loaded" | run through the editor, `lake build` or `lake lean`; with plain `lean` / `lake env lean` pass the `--load-dynlib … --plugin …` flags the message prints (§1) |
| "option `k` does not apply" | that backend does not use the option; see the options in §3 and §5 |
| build error about `immintrin.h` | `cc` is clang without x86 intrinsics headers; install gcc |
| illegal instruction on x86 | CPU lacks AVX-512F: build with `-Kbackend=rnerr` (§1) |
| Mathlib version mismatch | your `lean-toolchain` and Mathlib tag must be `v4.36.0` |
| "the bound is false" | it is: the message shows the point; fix the constant |
| "no certificate within depth …" on a true bound | raise `depth`/`maxBoxes`, loosen the constant, shrink the box, or split it |
| `root_unique` "contraction factor ≥ 1" | use the printed approximate root to choose a smaller box, or prove `∃` |
| `coordinate … needs a numeral lower and upper bound` | every variable needs both bounds, as numerals |
| kernel check slow or out of memory | `(chunk := 8)`, split into several theorems, or `(trust := native)` |

**Performance tips**

- Try the statement with `(trust := native)` first: if that fails, the kernel version will too,
  and you find out in a second instead of a minute.
- Polynomials are cheap in the kernel (a few ms per box); `exp`/`log` cost tens of ms and
  `sin`/`cos` ~0.5 s per evaluation. Multivariate problems with `sin`/`cos`/`exp` may need
  `trust := native`.
- Smaller boxes and looser constants mean fewer boxes. A bound that touches its target is
  provable, but needs derivative certificates; leave `deriv` on.
- Rewriting can reduce the dependency problem: on `[0, 1]`, `x * (1 - x)` evaluates to
  `[0, 1]` but `x - x^2` to `[-1, 1]`. (The optimisation backend also tries Horner form for
  polynomials by itself.)
- Put each heavy theorem in its own declaration (and heavy groups in their own files).

**Limitations (current)**

- Boxes must be closed, with numeral bounds; no general constraints (`x² + y² ≤ 1`).
- Root systems must be square; `∃!` needs Krawczyk to contract on the whole given box.
- `|x|` and atan2 are allowed in inequalities but not in roots or integrals.
- Integrals: one variable, numeral limits that are exact doubles (2D rules exist at the
  certificate level, §6).
- Optimisation uses first-order (centred-form) bounds only; localising a minimiser works in
  one variable; exact `sInf = v` needs `v` attained at a rational point.
- `erf`, `sinc`, `artanh`, `arsinh` are registered functions (no C tape: slower searches).
  `sinc` has no derivative information on boxes containing `0` (zeroth-order bounds only
  there); `artanh` only works on boxes strictly inside `(-1, 1)`.
- Interval128 is not used by the tactics.

**Where next**

- `RealFPMathlib/RealFPMathlib/Examples/`: worked examples for every feature (Roots,
  Optimization, IntegralTactic, MatrixPD, Cubic, Jacobian, Transc, Trig, …).
- `RealFPMathlib/RealFPMathlib/Tests/IntervalTest.lean`: dozens of small `interval` goals.
- [REFERENCE.md](REFERENCE.md): the reference, including all theorem names and benchmarks.
- [COMPARISONS.md](COMPARISONS.md): measured comparisons with FloatLib, LeanCert and the
  research showcases.
