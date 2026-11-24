# realfp reference

Full reference for [realfp](../README.md) (core package name: `interval64`).
For a short introduction and install instructions, see the [README](../README.md).
For a hands-on guide, start with the [tutorial](TUTORIAL.md).

A small Lean 4 (v4.36.0) library for **binary64 interval arithmetic** with
**hardware directed rounding**, including correctly rounded directed `exp`
and `log` ([transcendentals](#transcendentals-exp-log-sin-cos)). The core has **no
Mathlib / FloatLib dependency**.

Each directed scalar operation (`+`, `-`, `*`, `/`, `sqrt`, down and up) has:

- a **computable Lean specification** (`Interval64.Spec` / `addDownSpec`, …)
  that the kernel can unfold — a software IEEE 754 binary64 implementation
  built on Lean 4.36’s `Float.Model.UnpackedFloat`, with round-toward-±∞
  (including IEEE 754-2019 §6.3 signed zeros and overflow to ±∞ vs ±MaxFinite);
- a **C runtime** attached with `@[implemented_by]` (externs `iv64_dir_*`),
  selected at build time by architecture:
  - **x86_64:** AVX-512 embedded rounding (`_mm_add_round_sd` and friends);
  - **aarch64 (arm64) and others:** round-to-nearest + exact error term
    (see [arm64 backend](#arm64-aarch64-backend)).

  Compiled code, `#eval`, and `native_decide` use the C kernel. The kernel
  itself sees the Lean body. The spec and all theorems are the same on both.

Interval operations (`Interval64.add`, `mul`, …) are defined in Lean on top
of those scalars, so they inherit both the spec and the fast path.

**Proving real inequalities, integral bounds, roots and positive definiteness in Mathlib:**
see the front-door tactic [`realfp`](#realfp-one-tactic-for-kernel-checked-real-numerics-mathlib-layer)
(kernel-checked by default, standard axioms only).

**New here? Start with [TUTORIAL.md](TUTORIAL.md)**, a hands-on guide from setup to
tactics and hand-written certificates (every snippet is compiled, in
`RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean`).

Comparisons with [FloatLib](https://github.com/lean-dojo/FloatLib),
[LeanCert](https://docs.leancert.io/), and two research showcases are in
[COMPARISONS.md](COMPARISONS.md). Known gaps are listed in [LIMITATIONS.md](LIMITATIONS.md), and the design rationale is in [PHILOSOPHY.md](PHILOSOPHY.md).

## Kernels

- **AVX-512 embedded rounding** (does not change MXCSR; x86_64 backend).
- **RN + exact error term** (`c/iv64_rnerr.h`; aarch64 backend, also built on x86).
- **fesetround fallback** (save / compute / restore), compiled with
  `-frounding-math -ffp-contract=off -fno-math-errno`.
- **RN + 1-ulp widening**, for speed comparison.
- A **batched `FE_UPWARD`** interval kernel using `-up(-x)` for lower bounds.

The C file is compiled with **gcc** (`cc`). The Lean 4.36 bundled clang on
this box is missing `immintrin.h`. Lake packages the object as
`extern_lib libleaninterval64` so downstream projects and
`precompileModules` / `#eval` see the C symbols.

## Build and run

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake exe interval64_tests
lake exe interval64_native
taskset -c 0 nice -n 19 lake exe interval64_bench
```

**Plain `lean`.** `#eval` and the tactics need the compiled code, which Lake loads for the
editor, `lake build` and `lake lean File.lean`. Plain `lean` / `lake env lean` do not; pass
`--load-dynlib=<core>/.lake/build/lib/libleaninterval64.so
--plugin=<core>/.lake/build/lib/libinterval64_Interval64.so` (in that order). Without them the
tactics stop with a clear message that prints these flags (`RealFP.requireNative`, using
`Interval64.NativeLoad.loadFlags`); `#eval` gives Lean's `Could not find native
implementation` error. Loading the plugin from inside Lean at run time is not possible (it
crashes), so the flags cannot be applied automatically.

A downstream project can `require interval64 from` a local path to this repository
(core only), or `require realfp_mathlib from` the `RealFPMathlib/` subdirectory
(theorems about `ℝ` and the tactics). See the [README](../README.md) for the
lakefile snippet.

**CI.** `.github/workflows/ci.yml` runs on every push and pull request to `main`:
it installs Lean from `lean-toolchain`, fetches the Mathlib olean cache, builds
the core libraries and proofs with `IV64_BACKEND=rnerr` (and `-Kbackend=rnerr`), runs `interval64_tests`
and `interval128_tests`, checks `Interval64Axioms.lean`, builds
`RealFPMathlib.AxiomAuditCore` (library + Demo + Tests, not Examples), and
checks the tutorial snippets. `.github/workflows/examples.yml` builds the slow
Examples and the full `AxiomAudit` weekly and on demand (`workflow_dispatch`).

## arm64 (aarch64) backend

ARM has no per-instruction rounding mode, so on aarch64 the kernels in
`c/iv64_rnerr.h` compute the round-to-nearest result `r` plus the **exact**
error, and step one ulp when needed. They never touch the FPCR on the main path.

| op | RN result | exact error term |
|----|-----------|------------------|
| `a+b`, `a-b` | `s = a+b` | branch-free TwoSum (operands below `2^1021`; larger ones use Fast2Sum on a cold path) |
| `a*b` | `p = a*b` | `fma(a, b, -p)` |
| `a/b` | `q = a/b` | `r = fma(-q, b, a)`; `a/b - q = r/b`, so `sign(r)·sign(b)` |
| `sqrt a` | `s = sqrt(a)` | `fma(-s, s, a)` |

If the exact value is above `r`, round-up returns `nextUp(r)`; if below,
round-down returns `nextDown(r)`; otherwise `r` (branch-free on the bits).
The hot path of each op is a single well-predicted range check on the operands or
result; NaN/inf/zero/tiny/huge cases go to out-of-line cold functions.
Special cases, all bit-identical to the Lean spec / AVX-512:

- **Overflow:** if RN gives `±inf` from finite operands, the exact value is
  beyond `maxFinite`, so the direction toward zero gives `±maxFinite`. If RN gives
  `maxFinite` but the exact value is larger, `nextUp(maxFinite) = +inf`.
- **Signed zero:** a sum that rounds to 0 is exact; round-down gives `-0`
  unless both operands are `+0` (so `x + (-x) = -0` down, `+0` up). Zero
  products/quotients with a zero (or infinite divisor) operand are exact, sign = xor.
  `sqrt(-0) = -0`.
- **Subnormals / underflow:** `+`/`-` are always exact in the subnormal range.
  For `*` and `/`, the fma error term can itself underflow, so tiny results
  (`|a*b| ≤ 2^-968`, or `/` with `|a| < 2^-968`, a subnormal divisor, or a
  quotient below `2^-1022`) take a rare slow path: save / `fesetround` / compute
  / restore. `sqrt` of `a < 2^-960` is scaled by `2^600` first (exact) and the
  result by `2^-300`.
- **NaN / inf operands:** returned from the RN operation (NaN payloads may
  differ; all tests treat every NaN as equal).

Assumptions: the thread's rounding mode is round-to-nearest (Lean never changes
it), no flush-to-zero (Linux default), and correctly rounded hardware `fma`/`sqrt`.

**Testing.** `tests/test_rnerr.c` is a standalone differential test (random
bits, any-exponent values, cancellations, subnormal / tiny products and quotients,
near-overflow, small integers, near-exact quotients and squares, specials):

- `--vs-avx N`: RN+err vs AVX-512 in-process (x86_64);
- `--gen FILE N` / `--check FILE`: AVX-512 expected outputs, checked by an
  aarch64 build under `qemu-aarch64` (`scripts/test_arm64_qemu.sh`);
- `--vs-fe N`: RN+err vs a `fesetround` (FPCR) reference, for real arm64 hardware;
- `--bench`: micro-benchmark, on normal-range operands and on the mixed test-generator
  operands (which hit the slow and overflow paths often), reported separately.

`lake -R -Kbackend=rnerr build interval64_tests` builds the portable RN+err
backend on x86_64 (no AVX-512 instructions, so the binary also runs on CPUs
without AVX-512F; this is what CI uses), so the Lean-side tests
(`.lake/build/bin/interval64_tests`, C runtime vs Lean spec) can run against
it; `lake -R build interval64_tests` switches back to AVX-512.
`IV64_BACKEND=rnerr` has the same effect and also works when another Lake package
(such as `RealFPMathlib`) builds this one, because Lake `-K` options are not
forwarded to required packages. CI sets this environment variable.
(Name the exe target: a plain `lake build` does not relink the test exe.)
`scripts/test_arm64_qemu.sh` also cross-compiles CORE-MATH exp/log/sin/cos and
`c/iv64_transc.c` for aarch64 and checks RD/RU (FPCR) against the mpmath oracle
under qemu. `scripts/test_arm64.sh` step 8 builds the Mathlib layer, runs its
axiom check and `Examples.lean` (`SKIP_MATHLIB=1` skips it; the first Mathlib
build downloads the cache).

**On a real arm64 box (Jetson Orin, DGX Spark, …):**

```bash
sudo apt install -y build-essential git curl
git clone https://github.com/schlafly1/realfp && cd realfp
scripts/test_arm64.sh        # C tests + bench, installs elan if needed,
                             # lake build, interval64_tests, Examples.lean, proofs,
                             # and scripts/check_axioms.sh
```

`scripts/check_axioms.sh` runs every `#print axioms` in `Interval64Axioms.lean`,
checks the count, and fails on `sorryAx` or any axiom other than `propext`,
`Classical.choice`, `Quot.sound` and the generated `native_decide` axioms.

## Transcendentals (`exp`, `log`, `sin`, `cos`)

`Interval64.Directed.expDown/expUp/logDown/logUp` are correctly rounded toward
−∞ / +∞; `Interval64.exp` and `Interval64.log` are the interval versions
(`Interval64/Transc.lean`).

**Runtime (C).** [CORE-MATH](https://core-math.gitlabpages.inria.fr/)
(`c/coremath/`, **MIT license**, files unmodified, upstream commit in
`c/coremath/VERSION`, license in `c/coremath/LICENSE` and in each file header).
CORE-MATH's `cr_exp`/`cr_log`/`cr_sin`/`cr_cos` do not call `fegetround`; they
are correctly rounded in whatever hardware rounding mode is active.
`c/iv64_transc.c` sets RD or RU around one call (x86_64: MXCSR via
`_mm_setcsr`; aarch64: FPCR.RMode via `msr fpcr`; otherwise `fesetround`) and
restores the caller's mode. Each CORE-MATH file is its own translation unit,
compiled with `-O2 -frounding-math -ffp-contract=off -fno-math-errno` (+`-mfma`
on x86_64). Cost of the mode switch (x86_64, this box, direct C calls):
exp RN 4.9 ns vs RD/RU 11–12 ns; log RN 6.9 ns vs RD/RU 9.6–9.8 ns. Through
the Lean extern: exp RD/RU ≈ 18 ns, log ≈ 16 ns (RN CORE-MATH ≈ 10.6 ns, libm
`Float.exp` ≈ 11.6 ns). sin/cos: see below.

**Specification (Lean, Mathlib-free).** Rational enclosures with explicit
error terms, refined by a Ziv loop:

- `expBounds q p`: `exp t` for `t ≥ 0` via `t = 2^s·r`, `r ≤ 2^-20`, Taylor
  sum with the `Real.exp_bound` remainder, then `s` squarings rounded outward
  to `2^-p`; `exp(-t) = 1/exp t`.
- `logBounds q p`: `q = m·2^e` with `m ∈ [3/4, 3/2)`, `log m = log(1-y)` by
  the series with remainder `|y|^(n+1)/(1-|y|)`, `log 2 = -log(1-1/2)` the same
  way. If the reduction guard `|y| ≤ 1/2` ever failed, the crude valid bounds
  `1-1/q ≤ log q ≤ q-1` are used.
- `ziv`: precisions `128·2^k`, `k < 5` (`zivFuel`); stops when the rounded
  lower and upper bounds agree (then the result is the correctly rounded
  value). On fuel exhaustion it returns the rounding of the last valid
  bound (still an enclosure, maybe 1 ulp loose); the tests count these
  "fallback hits".
- Special cases: `exp`: NaN→NaN, −∞→+0, +∞→+∞, ±0→1, `q > 710` → MaxFinite/+∞,
  `q < −746` → +0 / min subnormal. `log`: NaN or `< 0` → NaN, ±0 → −∞,
  1 → +0, +∞ → +∞.

**Interval policy.** `exp`: invalid if an endpoint is NaN, else
`[expDown lo, expUp hi]`. `log` (as `sqrt`): `hi < 0` → invalid; `lo ≤ 0` →
lower end −∞; `log [0, 0] = [−∞, −∞]`.

**Tests.** `lake exe interval64_tests` checks C vs the Lean spec bit-for-bit
(down and up) on specials, 2000×7 random inputs and 4000 CORE-MATH
hard-to-round cases (`tests/transc_hard.txt`, sampled from CORE-MATH's
`exp.wc`/`log.wc`): 36272 checks, 0 mismatches, **0 fallback hits** (exp:
14254 converged at 128 bits, 1882 at 256; log: all at 128), on both the
AVX-512 and `-Kbackend=rnerr` builds. `tests/test_transc.c` checks the C kernels
against an mpmath oracle (`tests/transc_oracle.txt`, 2500-bit mpmath,
`scripts/gen_transc_oracle.py`): 6104 inputs × RD/RU, 0 mismatches on x86_64
and under `qemu-aarch64`.

**Proofs (`RealFPMathlib/RealFPMathlib/Transc.lean`).** `expBounds_spec`,
`logBounds_spec` (rational bounds enclose `Real.exp`/`Real.log`),
`expDown_loR`, `expUp_hiR`, `logLo_loR`, `logUp_hiR` (pointwise, any input),
and the interval theorems

```lean
theorem exp_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.exp x ∈ (Interval64.exp X).toSet
theorem log_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 < x) :
    Real.log x ∈ (Interval64.log X).toSet
```

Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Enclosure is proved
for the spec; *correct rounding* of the spec (and C = spec) is tested, not
proved. `RealFPMathlib/Examples/Transc.lean` proves
`2.718281828459045 < exp 1 < 2.7182818284590456` and
`0.6931471805599452 < log 2 < 0.6931471805599455` with `decide +kernel` (the
kernel runs the Lean spec; no `native_decide`).

### `sin`, `cos` (`Interval64/Trig.lean`)

`Interval64.Directed.sinDown/sinUp/cosDown/cosUp` (C: CORE-MATH `cr_sin`/`cr_cos`
under RD/RU, as above) with a Mathlib-free Lean spec:

- **π.** `machinPi P` (Machin series) is only a candidate; `piCheck P` rounds it
  to `[a, b]` at `2^-P` and *certifies* it: `3 ≤ a ≤ b ≤ 63/20`,
  `cos(a/4) > 1/√2` and `cos(b/4) < 1/√2` via the Taylor enclosure (so
  `a ≤ π ≤ b` because `cos` is decreasing on `[0, π]` and `cos(π/4) = 1/√2`).
  If the check fails, the valid fallback `[3, 3.15]` is used. `piBounds` caches
  the 10 enclosures for the Ziv precisions (`p + 110` bits, or `p + 1104` bits
  for `|x| ≥ 2^30`, enough for the largest doubles).
- **Reduction.** `k = round(4q/(π_lo+π_hi))`, `r = q − kπ/2` enclosed in
  `[rl, rh]` (π bounds chosen by the sign of `k`), Taylor of `cis r0` at
  `r0 = rl` rounded down, widened by the Lipschitz bound `|r − r0| ≤ rh − r0`,
  then quadrant `k mod 4`. Same Ziv loop as exp/log; `±0` → `sin`: same zero,
  `cos`: 1; `±∞`/NaN → NaN.
- **Interval policy.** NaN endpoint → invalid; infinite endpoint → `[−1, 1]`.
  For finite `[a, b]` the lower end is `min(fDown a, fDown b)` when
  `avoids a b c` certifies `[a, b] ⊆ [(4n+c)π/2, (4n+c+4)π/2]` (no interior
  minimum; `c = 3` for sin, `2` for cos), else `−1`; the upper end likewise
  (`c = 1` sin, `0` cos), else `+1`. `avoids` uses the same certified π bounds.

**Tests.** C vs Lean spec bit-for-bit, down and up: 16204 checks each for sin
and cos (specials, randoms incl. huge arguments, 2000 CORE-MATH hard cases each
from `sin.wc`/`cos.wc`; `tests/transc_hard.txt` now has 8000 lines), 0
mismatches, 0 fallback hits (all converge at 128 bits), on both backends. All
10 cached π enclosures pass the certificate. 3000 random intervals × sample
points (26986 points) are checked to lie inside `Interval64.sin/cos`: 0
failures. The mpmath oracle (`tests/test_transc.c`) covers sin/cos under RD/RU
on x86_64 and qemu-aarch64.

**Proofs (`RealFPMathlib/RealFPMathlib/Trig.lean`).** `trigSmall_spec`
(Taylor, from `Complex.exp_bound`), `piCheck_spec`/`piBounds_spec`
(`π_lo ≤ π ≤ π_hi`), `trigBounds_spec` (reduction), `sinDown_loR` …
`cosUp_hiR` (finite input), unimodality lemmas `sin_min_le`, `sin_le_max`,
`cos_min_le`, `cos_le_max`, `avoids_spec`, and

```lean
theorem sin_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.sin x ∈ (Interval64.sin X).toSet
theorem cos_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.cos x ∈ (Interval64.cos X).toSet
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`. Example
(`RealFPMathlib/Examples/Trig.lean`, `decide +kernel`):
`∀ x ∈ [1, 2], 0.84147098480789 < sin x ∧ sin x ≤ 1`.

## `atan`, `atan2`, `π` (`Interval64/InvTrig.lean`)

`Directed.atanDown/atanUp`, `Directed.atan2Down/atan2Up` (C argument order `atan2 y x`) are
correctly rounded toward −∞ / +∞; `Interval64.atan`, `Interval64.atan2`, and the constants
`Interval64.pi = [π↓, π↑]` (`0x400921FB54442D18`, `…19`), `halfPi`, `negHalfPi`, `argHull = [-π↓, π↑]`.

**Runtime (C).** CORE-MATH `cr_atan`, `cr_atan2` (`c/coremath/atan.c`, `atan2.c`, `tint.h`;
MIT, unmodified, same upstream commit) under RD/RU exactly as for `exp` (MXCSR / FPCR.RMode).
Cost (x86_64, direct C): atan RN 7.5 ns, RD/RU 12.7/13.4 ns; atan2 RN 10.3 ns, RD/RU 16.2/17.8 ns.

**Specification (Lean, Mathlib-free).** `atanBounds q p`: an unverified candidate (≤ 12
half-angle steps with rounded square roots, then the Taylor series) is widened to `[a, b]` and
*certified* with the existing `sin`/`cos` enclosures (`trigBounds`): `|a|, |b| ≤ 1`,
`sin a ≤ q·cos a`, `q·cos b ≤ sin b` ⇒ `a ≤ atan q ≤ b`; relative precision for small `q`;
for tiny `q` (`q² ≤ 2^-(p+10)`) the bounds `q - q³/3 ≤ atan q ≤ q - q³/3 + q⁵/5`;
`atan q = π/2 - atan (1/q)` for `q > 1`, odd symmetry. `atan2Bounds y x p`: `atan (y/x)`
(`x > 0`), `atan (y/x) ± π` (`x < 0`), `±π/2` (`x = 0`). Special values follow C99 Annex F
(signed zeros: `atan2 (±0, -0) = ±π`, `atan2 (±0, +0) = ±0`, `atan2 (±∞, ±∞) = ±π/4, ±3π/4`, …).
Ziv loop as for `exp`.

**`atan2` and `Complex.arg`.** Over the reals `atan2 y x` is `Complex.arg (x + y i)` (range
`(-π, π]`, `arg 0 = 0`, `arg` of a negative real `= π`). The IEEE signed-zero results
(`atan2 (-0, x<0) = -π`, `atan2 (±0, -0) = ±π`) do not match `arg` at those points, so the
pointwise theorems assume `y ≠ 0 ∨ x > 0`. The interval version never relies on those:
`X > 0`: `atan (Y / X)`; `Y > 0`: `π/2 - atan (X / Y)`; `Y < 0`: `-π/2 - atan (X / Y)`;
otherwise the box meets the branch cut (`y = 0, x ≤ 0`) or the origin and the result is the hull
`[-π, π]`. (It uses the interval `div` + `atan`, so it can be ~1 ulp wider than evaluating the
pointwise `atan2Down/Up` at the corners.)

**Proofs (`RealFPMathlib/InvTrig.lean`).** `atanCheck_spec`, `arctan_series_bounds`,
`atanBounds_spec`, `piMul_spec`, `arg_right`, `arg_upper`, `arg_lower`, `atan2Bounds_spec`,
`atanDown_loR`, `atanUp_hiR` (any input, extended reals), `atan2Down_loR`, `atan2Up_hiR`
(finite inputs, `y ≠ 0 ∨ x > 0`), and

```lean
theorem pi_mem_toSet : Real.pi ∈ Interval64.pi.toSet
theorem atan_mem_toSet (hx : x ∈ X.toSet) : Real.arctan x ∈ (Interval64.atan X).toSet
theorem atan2_mem_toSet (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) ∈ (Interval64.atan2 Y X).toSet
```

**Tests.** `lake exe interval64_tests`: atan 10098 and atan2 13490 C-vs-spec checks (specials,
random, the mpmath oracle inputs), 0 mismatches, 0 fallback hits; `tests/func_oracle.txt`
(`scripts/gen_func_oracle.py`, mpmath 2500 bits, including 1500+1500 CORE-MATH worst cases from
`atan.wc`/`atan2.wc`): 6194 inputs, 0 C mismatches on x86_64 and under `qemu-aarch64`
(`tests/test_func.c`, run by `scripts/test_arm64.sh` / `test_arm64_qemu.sh`); 74564 interval
sample points.

**Tactic.** `interval` understands `Real.pi`, `Real.arctan`, and
`Complex.arg (↑x + ↑y * Complex.I)` (as `IExpr.pi/atan/atan2`; kernel path `KI.atan`, `atan2K`,
`evalK_toI` extended). `atan` has a derivative (`1/(1+a²)·a'`), `atan2` none (no
monotonicity/centred certificates through `atan2`; plain bisection). Kernel evaluation of
`atan` is costly (the spec runs `sin`/`cos` certificates): tests `f01`–`f08`, e.g.
`x - x^3/3 ≤ arctan x` on `[0,1]` (touching, 24 boxes, ~50 s).

## `sinh`, `cosh`, `tanh`, `log2`, `log10` (`Interval64/Hyp.lean`)

`Directed.{sinh,cosh,tanh,log2,log10}{Down,Up}` are correctly rounded toward −∞ / +∞ (CORE-MATH
`cr_sinh`, `cr_cosh`, `cr_tanh`, `cr_log2`, `cr_log10` under RD/RU, as for `exp`).
Interval versions `Interval64.sinh/tanh` (increasing), `cosh` (minimum `1` when `0 ∈ X`),
`log2/log10` (lower endpoint `-∞` when `lo ≤ 0`).

**Specification.** From the `exp`/`log` enclosures: `sinhBounds = ((a-d)/2, (b-c)/2)`,
`coshBounds = ((a+c)/2, (b+d)/2)` with `[a,b] ∋ eᑫ`, `[c,d] ∋ e⁻ᑫ` (exact Taylor sums for small
`|q|`); `tanh = sinh / cosh` (`|q| ≥ 22`: `[1 - 2⁻⁶⁰, 1]`); `log2 = log q / log 2`,
`log10 = log q / log 10` (exact `k` for `q = 2ᵏ` / `10ᵏ`). Ziv loop as for `exp`.

**Proofs (`RealFPMathlib/Hyp.lean`).** `sinhBounds_spec`, `coshBounds_spec`, `tanhBounds_spec`,
`log2Bounds_spec`, `log10Bounds_spec`, `sinhDown_loR`/`sinhUp_hiR`, `tanhDown_loR`/`tanhUp_hiR`,
`coshDown_loR_nonneg` …, and

```lean
theorem sinh_mem_toSet  (hx : x ∈ X.toSet) : Real.sinh x ∈ (Interval64.sinh X).toSet
theorem cosh_mem_toSet  (hx : x ∈ X.toSet) : Real.cosh x ∈ (Interval64.cosh X).toSet
theorem tanh_mem_toSet  (hx : x ∈ X.toSet) : Real.tanh x ∈ (Interval64.tanh X).toSet
theorem log2_mem_toSet  (hx : x ∈ X.toSet) (hx0 : 0 < x) : Real.logb 2 x ∈ (Interval64.log2 X).toSet
theorem log10_mem_toSet (hx : x ∈ X.toSet) (hx0 : 0 < x) : Real.logb 10 x ∈ (Interval64.log10 X).toSet
```

## `tan`, `asin`, `acos` (`Interval64/Tan.lean`, `Interval64/Asin.lean`)

CORE-MATH `cr_tan`, `cr_asin`, `cr_acos` under RD/RU. `Interval64.tan X` is
`[tan↓ lo, tan↑ hi]` when `X` provably contains no pole `π/2 + kπ`, else the whole line;
`asin` (increasing) and `acos` (decreasing) follow Mathlib's `Real.arcsin`/`Real.arccos`
(clamped outside `[-1, 1]`).

**Specification.** `tan q = sin q / cos q` from `trigBounds` once the sign of `cos q` is
certified (`tanRes`; fallback `±∞` never hit for binary64 inputs). `asin`: tiny `q`:
`q ≤ asin q ≤ q + q³/5`; otherwise a candidate `≈ atan (q/√(1-q²))` widened to `[a, b]` and
certified by the `sin` enclosures; odd symmetry, `asin (±1) = ±π/2`; `acos q = π/2 - asin q`
(64 extra bits, `acos 1 = 0` exactly).

**Proofs (`RealFPMathlib/Tan.lean`, `Asin.lean`).** `tanRes_spec`, `tanBounds_spec`,
`tanDown_loR`, `tanUp_hiR`, `asinBounds_spec`, `acosBounds_spec`, `asinDown_loR` …, and

```lean
theorem tan_mem_toSet  (hx : x ∈ X.toSet) : Real.tan x ∈ (Interval64.tan X).toSet
theorem asin_mem_toSet (hx : x ∈ X.toSet) : Real.arcsin x ∈ (Interval64.asin X).toSet
theorem acos_mem_toSet (hx : x ∈ X.toSet) : Real.arccos x ∈ (Interval64.acos X).toSet
```

(`Real.tan` at a pole is `0` in Mathlib; the whole-line result covers it.)

## Real power `rpow` (`Interval64/Pow.lean`, `RealFPMathlib/Pow.lean`)

`Interval64.rpow X Y = exp (Y * log X)`, the composition of the outward-rounded enclosures, so

```lean
theorem RealFP.Pow.rpow_mem_toSet (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) (hx0 : 0 < x) :
    x ^ y ∈ (Interval64.rpow X Y).toSet          -- Real.rpow, no finiteness assumption
```

It is sound but **not correctly rounded**: the width grows with `|y · log x|` (the `exp`
argument is an interval about one ulp of `y · log x` wide), so a few ulps when `|y · log x| ≲ 1`
(`rpow 2 (1/2)` is two adjacent doubles, `RealFP.Examples.Pow`) and hundreds of ulps when
`|y · log x| ≈ 100`. Spot check (`lake lean`, 20000 random `x ∈ [e⁻²⁵, e²⁵]`, `y ∈ [-50, 50]`):
`Float.pow x y` inside `rpow [x,x] [y,y]` every time. The vendored
CORE-MATH `cr_pow` (`iv64_dir_pow_down/up`) is compiled and linked but not used yet (a correctly
rounded pointwise `pow` needs its own exact Lean spec). Not supported by the `interval` tactic.

## `∈` forms (`RealFP.Iv`)

`Iv.pi_mem`, `Iv.atan_mem`, `Iv.atan2_mem`, `Iv.sinh_mem`, `Iv.cosh_mem`, `Iv.tanh_mem`,
`Iv.log2_mem`, `Iv.log10_mem`, `Iv.tan_mem`, `Iv.asin_mem`, `Iv.acos_mem`, `Iv.rpow_mem`
(`RealFPMathlib/Pow.lean`) restate the theorems above with `x ∈ X`, like `Iv.exp_mem`.

**Tactic.** `interval` understands `Real.sinh`, `Real.cosh`, `Real.tanh`, `Real.logb 2`,
`Real.logb 10`, `Real.tan`, `Real.arcsin`, `Real.arccos` (kernel path `KI.*`, derivatives in
`IntervalDeriv`); tests `h01`–`h08`, `a01`–`a05` in `Tests/IntervalTest.lean`.

## Conversions and literals (`Interval64/Conv.lean`)

No new runtime checks; existing operations are unchanged.

| Syntax | Meaning |
|---|---|
| `(2 : Interval64)` (`OfNat`) | `ofRat 2`: exact if representable, else tightest outward enclosure |
| `(0.1 : Interval64)` (`OfScientific`) | `ofRat (1/10)`, the *exact* decimal (two adjacent doubles), unlike `Float` `0.1` |
| `(n : Interval64)`, `(z : Interval64)` for `n : Nat`, `z : Int` | `NatCast` / `IntCast` → `ofNat n`, `ofInt z` (= `ofRat`) |
| `(q : Interval64)` for `q : Rat` | `Coe` → `ofRat q` (core Lean has no `RatCast`) |
| `(f : Interval64)` for `f : Float` | `Coe` → `point f = ⟨f, f⟩`; NaN → invalid, `±∞` → `⟨±∞, ±∞⟩` (encloses no real: empty `toSet`) |

`X + 2`, `X * 0.1`, `X + q`, `X + n`, `X + z`, `X + f` elaborate via `binop%`.
In compiled code a literal such as `0.1` inside a definition is a closed term,
computed once (lazily) by the generated C. `decide +kernel` evaluates literals
(e.g. the endpoints of `(0.1 : Interval64)`).

Mathlib layer (`RealFPMathlib/Conv.lean`): `Membership ℝ Interval64` with
`x ∈ X ↔ x ∈ X.toSet` (`RealFP.mem_iff`, simp); `ratCoe_mem`, `natCast_mem`,
`intCast_mem`, `ofNat_mem`, `zero_mem`, `one_mem`, `ofScientific_mem`
(`(0.1 : ℝ) ∈ (0.1 : Interval64)`), `floatCoe_mem`
(`f.toReal? = some r → r ∈ (f : Interval64)`); and `RealFP.Iv.{add,sub,exp,log,sin,cos}_mem`,
`RealFP.Iv.mem_{mul,div,sqrt}`, the enclosure theorems stated with `∈` (no finiteness
hypotheses; the older `Iv.{mul,div,sqrt}_mem`, which took them, are deprecated aliases).
Example (`RealFPMathlib/Examples/Conv.lean`):
`∀ x ∈ [0, 1], x * x - 0.1 * x + 2 ≤ 3` from one evaluation of `X * X - 0.1 * X + 2`.

## Display, exact endpoints, dot notation (`Interval64/Display.lean`)

`#eval`/`Repr`/`toString` print `[lo, hi]` with 17 significant digits per endpoint (round to
nearest; enough to read each double back exactly), `NaN`, `inf`, `-inf`, `-0`:
`(0.1 : Interval64)` shows `[0.099999999999999992, 0.10000000000000001]`. Rigorous values:
`X.exact : Option Rat × Option Rat` (exact endpoints, `none` for NaN/±∞) and
`X.widthRat : Option Rat` (exact `hi − lo`). `decimalOfRat q (sig := 17)` and
`decimalOfFloat f` are the formatters. Interval128 has the same (`Interval128/Display.lean`,
34 digits).

The type is the root-level structure `Interval64` (fields `lo hi : Float`) and its operations
live in the namespace `Interval64`, so dot notation works: `X.sqrt`, `X.width`,
`X.hiLe q`, `(X * X).exact`. The old name `Interval64.Interval64` is kept as an alias
(`export _root_ (Interval64)`), so downstream code that wrote it still compiles.

## Extended (split) division (`Interval64/Split.lean`)

`divSplit a b : Interval64Pair` encloses `{x / y | x ∈ a, y ∈ b, y ≠ 0}` as a union
of at most two intervals (IEEE 1788 `mulRevToPair` style). `/` is unchanged.
`Interval64Pair` is `empty | one I | two u l`, where `two u l` means
`[-∞, u] ∪ [l, +∞]`. Only the existing directed `divDown`/`divUp` kernels and
Float comparisons are used, with at most 2 directed divisions in the split cases.

| `a` | `b` | `divSplit a b` |
|---|---|---|
| NaN endpoint | any | `one invalid` |
| any | `0 ∉ b` | `one (a / b)` |
| any | `[0, 0]` | `empty` |
| `0 ∈ a` | `0 ∈ b ≠ [0, 0]` | `one whole` |
| `a > 0` | `[0, d]` | `one [a.lo/d ↓, +∞]` |
| `a > 0` | `[c, 0]` | `one [-∞, a.lo/c ↑]` |
| `a > 0` | `c < 0 < d` | `two (a.lo/c ↑) (a.lo/d ↓)` |
| `a < 0` | `[0, d]` | `one [-∞, a.hi/d ↑]` |
| `a < 0` | `[c, 0]` | `one [a.hi/c ↓, +∞]` |
| `a < 0` | `c < 0 < d` | `two (a.hi/d ↑) (a.hi/c ↓)` |

Example: `divSplit 5 [-2, 3] = two (-2.5) (5/3 ↓)`, i.e. `[-∞, -5/2] ∪ [5/3, +∞]`.
Helpers: `piece1`, `piece2` (absent piece = `invalid`, which contains no
reals), `toList`, `foldl`, and `hull` (`invalid` / `I` / `whole`). There is also a
coercion `Interval64Pair → Interval64` via `hull`, so
`let y : Interval64 := divSplit a b` works.

Proofs (`RealFPMathlib/Split.lean`): `Membership ℝ Interval64Pair`
(`x ∈ P ↔ x ∈ P.piece1 ∨ x ∈ P.piece2`, `pair_mem_iff`; `mem_toList`),
`mem_hull`/`mem_coe` (`x ∈ P → x ∈ P.hull`), and

```lean
theorem mem_divSplit {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) (hy0 : y ≠ 0) :
    x / y ∈ divSplit A B
```

(no finiteness hypotheses: half-lines and `whole` are allowed), plus `mem_divSplit_hull`.
The older `divSplit_mem` / `divSplit_hull_mem` (which also required the four endpoints
to be finite) still compile but are deprecated.
Example (`RealFPMathlib/Examples/Split.lean`): interval Newton in slope form.
Splitting `[-2, 2]` by `divSplit 2 [-2, 2]` and taking one Newton step per
piece proves that every root of `x² = 2` in `[-2, 2]` lies in `±[1.3999, 1.4286]`
(`sqrt_two_roots`; endpoints by `decide +kernel`). Tests: the case table, and
89165 random points `x ∈ A`, `y ∈ B` whose exact rational quotient lies in a
piece and in the hull (0 failures).

## Interval policy

- NaN endpoint → invalid `[NaN, NaN]`.
- Division by an interval containing `0` → whole line `[-∞, +∞]`.
- `sqrt` of `hi < 0` → invalid; `lo < 0 ≤ hi` clips to `[+0, hi]`; `sqrt(-0) = -0`.
- Multiplication: a `0 · ∞` corner is skipped; if all four are, the result is `whole`.
- Division: a `±∞ / ±∞` corner (NaN) is skipped. This is a slow path
  (`divNaNCorners`, `@[noinline]`) entered only when the usual `fmin`/`fmax`
  fold produced a NaN, so finite intervals pay nothing extra.

**Soundness fix (Nov 2026).** Before this fix, `div` and `feDiv` returned
`invalid` (the empty set) when a `∞/∞` corner was NaN and was not the first
corner in the fold, e.g. `[1, ∞] / [1, ∞]` and `whole / [1, ∞]`. That is an
unsound enclosure. They now give `[0, ∞]` and `whole`. `divSplit` had the same
problem through its `one (a / b)` branch and is fixed by the same change. The
membership theorems below now cover infinite endpoints, so this case is proved.

## More interval operations (`Interval64/Ops.lean`)

All are Lean code over the existing directed kernels and `Float` comparisons
(no new C), so `#eval`/compiled code use the C kernels and `decide +kernel`
sees the spec. Invalid (NaN) arguments give `invalid` (NaN for scalars).

| op | result |
|---|---|
| `-X` (`Neg` instance, `Interval64.neg`) | `[-hi, -lo]` (exact) |
| `Interval64.abs X` | `X` if `0 ≤ lo`, `-X` if `hi ≤ 0`, else `[0, max (-lo) hi]` |
| `square X` | dependency-aware `X²`, `⊆ [0, ∞]`: `square [-1, 2] = [0, 4]`, whereas `X * X = [-2, 4]` |
| `pown X n` | `n = 0`: `[1, 1]`; odd `n`: `[lo^n ↓, hi^n ↑]`; even `n`: the same on `abs X` (dependency-aware). Endpoint powers by binary exponentiation of point intervals (`ipow`, ≤ 2·log₂ n interval ops) |
| `Interval64.min X Y`, `Interval64.max X Y` (`Min`/`Max` instances) | pointwise, exact |
| `inv X` | `[1/hi ↓, 1/lo ↑]`; `whole` if `0 ∈ X` |
| `intersect X Y` | `[max lo, min hi]`; **empty → `invalid`** (`[NaN, NaN]`, the empty set) |
| `hull X Y` | `[min lo, max hi]`; an invalid argument is ignored |
| `mid X` | `lo/2 + hi/2` (infinite ends replaced by `∓maxFloat`, so `mid whole = 0` and half-lines give a finite point), clamped into `[lo, hi]` |
| `width X` | `hi - lo` rounded up |
| `mag X`, `mig X` | largest `abs x` on `X` (= `max (-lo) hi`); smallest `abs x` (`0` if `0 ∈ X`) |
| `bisect X` | `([lo, mid X], [mid X, hi])` |
| `subset X Y`, `contains X f` | `Y.lo ≤ X.lo ∧ X.hi ≤ Y.hi` (false if either is invalid); `lo ≤ f ≤ hi` |
| `X.hiLe q`, `X.loGe q` (`q : Rat`) | `hi` is finite and `≤ q`; `lo` is finite and `≥ q` (exact rational comparison, decidable by `decide +kernel`) |

Proofs (`RealFPMathlib/Ops.lean`; none needs finite endpoints): `mem_neg`, `mem_abs`,
`mem_square` (`x ^ 2 ∈ square X`), `mem_pown` (`x ^ n ∈ pown X n`), `mem_min`,
`mem_max`, `mem_inv` (`x⁻¹ ∈ inv X`, with Lean's `0⁻¹ = 0`), `toSet_intersect`
(`(intersect X Y).toSet = X.toSet ∩ Y.toSet`, exact), `mem_intersect`,
`union_subset_toSet_hull`, `toSet_subset_of_subset`, `mem_of_contains`,
`mid_spec` (`lo ≤ mid X ≤ hi`, not NaN, for nonempty `X`), `contains_mid`,
`bisect_cover`, `bisect_fst_subset`, `bisect_snd_subset` (for nonempty `X`),
`abs_le_mag`, `mig_le_abs`, `sub_le_width` (`x - y ≤ width X` for `x, y ∈ X`), and
`width_ge` (`hi - lo ≤ width X` for finite endpoints), and (in `RealFPMathlib/Basic.lean`)
`le_of_mem_hiLe : x ∈ X.toSet → X.hiLe q = true → x ≤ q` and `ge_of_mem_loGe`, the one-step
way to turn an evaluation into a real bound (no separate `bitsToRat?` side goal). Example
(`RealFPMathlib/Examples/Ops.lean`, `decide +kernel` only): `square [-1, 2] = [0, 4]`
versus `[-1, 2] * [-1, 2] = [-2, 4]`, and `sq_bounds : -1 ≤ x ≤ 2 → 0 ≤ x² ≤ 4`.
Tests (`opsTests` in `Interval64Test.lean`): 36000 random point pairs on random
intervals with `±∞`, `±0`, tiny and ordinary endpoints, checked against exact
rationals for unbounded `*`, `/`, `feMul`, `feDiv`, `divSplit`, `sqrt` and every op
above (`pown` for `n = 0 … 7`), plus the `∞/∞` regression cases; 0 failures with
both the AVX-512 and the `rnerr` backend.

## Proofs and trust

Theorems in `Interval64.Theorems` are about the **Lean spec** and are
kernel-checked (`decide` / `rfl`); they introduce no extra axioms. They
cover signed-zero rules, exact cases such as `1+1` and `1+2^{-53}`, NaN
propagation lemmas, and a concrete rational enclosure for `1+2^{-53}`.

The general directed-rounding enclosure is proved, about the **Lean spec**,
and depends only on `propext`, `Classical.choice` and `Quot.sound` (no
`sorry`). `Interval64Proofs.AddBits.add_encloses` states that if `a` and
`b` are finite or zero, with exact rational values `qa` and `qb`, then
round-down(`a+b`) ≤ `qa+qb` ≤ round-up(`a+b`). Overflow may round to
`±∞`, which is a valid bound. The same theorems exist for subtraction,
multiplication, division (`qb ≠ 0`) and square root:
`Sub.sub_encloses`, `Mul.mul_encloses`, `Div.div_encloses`,
`Sqrt.sqrt_mem_rat`. Interval versions are `add_mem_iv`, `sub_mem_iv`,
`mul_mem_iv`, `div_mem_iv` and `sqrt_mem_iv`. The Mathlib-layer lifts are
`RealFP.add_mem_toSet` / `sub_mem_toSet` and, with no finiteness
hypotheses, `mem_toSet_mul` / `mem_toSet_div` / `mem_toSet_sqrt`.

The compiled C path (AVX-512, or RN+err) is a trust assumption, checked
differentially against the Lean spec and against `fesetround`.

`Interval64.NativeDecide.demoHi_le` (`demoHi ≤ 3.75` for
`demoIv = [0.5, 1.5]`, `demoHi = (demoIv * demoIv + demoIv).hi`) is proved
by `native_decide`. In Lean 4.36 this introduces a generated axiom
`demoHi_le._native.native_decide.ax_1_1` (plus `propext`,
`Classical.choice`, `Quot.sound`), rather than the older name
`Lean.ofReduceBool`. A debug counter around that `native_decide` went
from 0 to 10, i.e. the compiled predicate called the AVX-512 C kernels
(8 directed muls + 2 directed adds). Runtime `addDown` is ~1.7 ns/op
versus ~2.9 µs/op for the software `addDownSpec`.

The capstone `Interval64Proofs.Capstone.sq_add_le` now uses the kernel-checked
`demoHi_le'` (= `Interval64.KF.demoHi_le_kernel`, via the Nat mirror below); the
`native_decide` theorem `demoHi_le` remains only as the native demo.

## Kernel fast path (`Interval64/Kernel/`, `Interval64Proofs/Kernel*.lean`)

`decide +kernel` on the Lean spec is slow (UInt64/Int/structure recursion; ~4 ms
per directed op). A **Nat mirror** evaluates the same IEEE bit patterns with
GMP-accelerated `Nat` operations, and is *proved equal* to the spec; runtime code,
the spec and every existing theorem are unchanged.

* `KF` (scalars, `Interval64/Kernel/Nat.lean`): `addDown … sqrtUp`, `lt/le/beq/cmp`.
  `KernelEq`: `add_eq … sqrt_eq : (Spec.op a b up).toNat = KF.op a.toNat b.toNat up`,
  `cmp_eq`. `KernelFloat`: the same at `Float` level via `toF n = Float.ofBits (UInt64.ofNat n)`
  (`addDown_toF`, `lt_toF`, `le_toF`, `beq_toF`, `neg_toF`, …).
* `KI` (intervals, `Interval64/Kernel/Interval.lean`): `add sub mul neg inv abs sqrt square
  pown hull exp log sin cos ofRat ofRatInterval`; `KernelInterval`: `toI (KI.op a b) = op (toI a) (toI b)`.
* Reflection (`Interval64/Kernel/Reflect.lean`): expression AST `IExpr`, Float evaluator
  `evalI`, kernel evaluator `evalK`, `evalK_toI`, bisection certificates `Cert` and the
  Bool checker `checkK`.

Kernel time per operation (`decide +kernel`, x86-64, Lean 4.36):

| op | spec (before) | KF / KI (after) |
|---|---|---|
| scalar `add/sub/mul/div/sqrt` (directed) | 3.5–4.5 ms | 0.16–0.31 ms |
| `Float` `<` / `≤` | 2.5 ms | ~0.2 ms |
| interval `+` / `*` / `inv` / `sqrt` / `square` | not measured (≥ 2 spec ops each) | 0.6 / 1.7 / 1.1 / 0.8 / 0.5 ms |
| `ofRat` constant | 5–6 ms | 5–6 ms (Rat-based, cached per check) |
| `exp` / `log` / `sin` / `cos` | 48 ms / 98 ms / 0.5 s / 0.37 s | same (spec is rational Ziv; gap) |

## `realfp`: one tactic for kernel-checked real numerics (Mathlib layer)

```lean
import RealFPMathlib   -- theorems and tactics (`import RealFPMathlib.Front`: tactics only)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp          -- interval
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≠ 2 * x := by realfp               -- exclusion
example : (0.74 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by realfp          -- integral
example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp                        -- unique root
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by realfp                    -- existence
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by realfp                            -- Krawczyk
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by realfp         -- PD
example : … := by realfp (trust := native) (depth := 30)
```

`realfp` (`RealFPMathlib/Front.lean`) looks at the goal and calls one backend; each backend is
also available on its own. Errors name the backend (`realfp (trust := kernel): via
`interval`: …`), the trust mode and what failed (the subgoal, the box, the contraction factor,
an approximate root or a counterexample, using your variable names) with a suggestion.

| Goal shape | Backend | Method |
|---|---|---|
| `∃! x, x ∈ Icc a b ∧ f x = 0`, `∃! x ∈ Icc a b, f x = g x` | `root_unique` | sign change at the ends (IVT) + derivative enclosure of one sign (strict monotonicity) |
| `∃! p : ℝ×ℝ / ℝ×ℝ×ℝ / Fin n → ℝ, box ∧ F p = 0` (n equations) | `root_unique` | Krawczyk operator on the whole box: inclusion + contraction ⇒ Banach fixed point ⇒ unique zero |
| `∃ x ∈ Icc a b, f x = 0` | `root_exists` | sign change on a 512-point grid (IVT on the sub-interval) |
| `∃ p, box ∧ F p = 0` (systems) | `root_exists` | Newton (multi-start) finds an approximate root, Krawczyk on a small box around it |
| `M.PosDef`, `M : Matrix (Fin n) (Fin n) ℝ` with rational entries | `pos_def` | binary64 congruence certificate (Rump/Gershgorin) → `posDef_of_ratMat` |
| anything containing `∫ x in a..b, f x` with numeral bounds | `integral_bound` | adaptive Taylor quadrature (orders 2–8) |
| `∃ m, ∀ …`, `sInf`/`sSup`, witnesses, argmin | optimisation (below) | branch-and-bound + multivariate centred forms |
| `≤ < ≥ > ≠`, `∈ Set.Icc`, `∧`, `∀ x ∈ box` | `interval` | bisection + derivative certificates; `≠` via `f - g < 0 ∨ f - g > 0` boxwise |

Box and bound syntax for root goals: each coordinate needs one numeral lower and one numeral
upper bound (`x ∈ Set.Icc a b`, or `a ≤ x` and `x ≤ b`, any order); equations are `f = g`
(moved to `f - g = 0`); the number of equations must equal the number of unknowns.

**Supported operations** (all backends share the reflected language `IExpr`):

| Operation | `interval` / `≠` | integrals, roots (need `domOK`: derivatives exist on the box) |
|---|---|---|
| `+ - *`, numerals (`0.1`, `1/3`, anything `norm_num` evaluates to ℚ) | ✓ | ✓ |
| `/`, `⁻¹` | ✓ | ✓ (denominator enclosure must exclude 0) |
| `^ n` (numeral `n : ℕ`) | ✓ | ✓ |
| `Real.sqrt`, `Real.log`, `Real.logb 2`, `Real.logb 10` | ✓ | ✓ (argument enclosure must be positive) |
| `Real.exp`, `Real.sin`, `Real.cos`, `Real.arctan`, `Real.sinh`, `Real.cosh`, `Real.tanh`, `Real.pi` | ✓ | ✓ |
| `Real.tan`, `Real.arcsin`, `Real.arccos` | ✓ | ✓ (strictly inside their domains) |
| `abs` (`\|x\|`), `Complex.arg (↑x + ↑y * I)` (atan2) | ✓ | ✗ (not differentiable everywhere) |
| variables | any number | integrals: 1; roots: `ℝ`, `ℝ×ℝ`, `ℝ×ℝ×ℝ`, `Fin n → ℝ` |

**Options** (any order): `(trust := kernel|native)`, `(depth := n)`, `(maxBoxes := n)`,
`(order := n)`, `(deriv := false)`, `(chunk := n)` for `interval`, the root backends and
optimisation. `(precision := 64|128)` (default 64) selects Interval64 or 128-bit dyadic
endpoints; 128 is implemented for `interval` goals only so far (see
[Precision 128](#precision-128-in-interval-interval128dyadiclean-realfpmathlibi128dyadiclean)),
and other backends reject it. `integral_bound` takes `trust`, `(order := n)` (fix the Taylor order: 2, 4, 6 or
8) and `(maxBoxes := n)` (maximum cells, default 512). `pos_def` takes only `trust`. The same
options work through `realfp`; an option the chosen backend cannot use is an error
(`pos_def: option `depth` does not apply …`).

**Trust.** `trust := kernel` is the default: every certificate check is closed by
`decide +kernel`, the Lean kernel re-runs the (Nat/Int) evaluator, and the theorem depends only
on `propext`, `Classical.choice`, `Quot.sound`. `trust := native` (or
`set_option realfp.native true`) closes the same checks with `native_decide` — faster on very
large certificates, but `#print axioms` then shows a `…native_decide.ax…` axiom and the proof
trusts the Lean compiler. The search (bisection, Newton, Krawczyk preconditioners, PD
congruences) always runs natively and is untrusted; only its output is checked.

**Soundness of the root tactics** (`RealFPMathlib/Roots.lean`, `RealFPMathlib/Krawczyk.lean`,
no `sorry`): `RealFP.Roots.prove_ne` (exclusion), `ivt_exists`/`ivt_exists_in` (IVT),
`unique_one` (IVT + strictly monotone from the derivative certificate), `kraw_exists`,
`kraw_existsUnique`, `kraw_exists_in` (Krawczyk). The Krawczyk check verifies, in interval
arithmetic with the kernel evaluator, that `G(x) = x − Y F(x)` maps the box into itself
(`m − Y F(m) + (I − Y J(X))(X − m) ⊆ X`, with `J(X)` an enclosure of the Jacobian over the box)
and that `‖I − Y J(X)‖∞ ≤ q < 1`; a second matrix `Z ≈ J(m)` with `‖I − Z Y‖∞ ≤ q` shows `Y` is
injective, so fixed points of `G` are exactly the zeros of `F`. Banach's theorem on the closed
box (`ContractingWith.fixedPoint`) gives existence and uniqueness; no Brouwer theorem is needed.

**Axiom audit.** `RealFPMathlib/AxiomAudit.lean` is part of the default `lake build`: it walks
every `RealFP.*` theorem (1418 at the time of writing, all examples included) and fails the
build if any uses an axiom beyond the standard three (`native_decide` axioms are allowed only in
`RealFP.Demo.*` / `RealFP.Examples.*`; `sorryAx` never). `RealFPMathlib/scripts/audit_axioms.sh`
prints the report. `lake build RealFPMathlib.AxiomAuditCore` is the same check without
Examples (used in the push CI).

Examples: `RealFPMathlib/RealFPMathlib/Examples/Roots.lean` (roots, exclusion, 2×2/3×3 and
transcendental systems, PD). Limitations: `∃!` for systems needs Krawczyk to contract on the
whole given box (no automatic splitting into exclusion + isolation boxes), so wide boxes need
`∃` or a smaller box (the error message prints an approximate root); boxes are closed with
numeral bounds; square systems only; `|·|` and atan2 are excluded from root goals.

### Optimisation over boxes (`RealFPMathlib/Opt.lean`, `RealFPMathlib/OptTactic.lean`)

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≥ -1/4 := by realfp                 -- exact min
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (-2 : ℝ) 2, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4 ≥ m := by realfp              -- discovery
example : sInf ((fun x : ℝ => x ^ 2 - x) '' Set.Icc 0 1) = -1/4 := by realfp      -- sInf = v
example : sSup ((fun x : ℝ => x * Real.exp (-x)) '' Set.Icc 0 3) ∈ Set.Icc 0.367879 0.36788 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x^2 - x ≤ y^2 - y := by realfp  -- argmin
#realfp_min (x ∈ Set.Icc (-2:ℝ) 2) (y ∈ Set.Icc (-1:ℝ) 1), 4*x^2 - 2.1*x^4 + x^6/3 + x*y - 4*y^2 + 4*y^4
```

| Goal shape | Method |
|---|---|
| `∀ x ∈ box…, f ≥ c` (`≤ < > ≥`, any number of variables) | bisection + monotonicity + multivariate nested centred forms (`MCert`, checked by `checkM_sound`); polynomials are also tried in Horner form (equality proved by `ring_nf`) |
| `∃ m : ℚ/ℝ, ∀ x ∈ box…, f ≥ m` (or `≤ M`) | best-first branch-and-bound finds the minimum natively; a rounded `m` slightly below it is proved as above |
| `∃ x ∈ box…, f ≤ c` (witness; `∧` of inequalities) | rational candidates (B&B minimiser, short grid points) checked at the point |
| `sInf (f '' S) ≥ / ≤ / = v`, `∈ Set.Icc a b`, `\|sInf … − v\| ≤ ε`, same for `sSup`; `S` an `Icc` or `Icc ×ˢ Icc` | `≥`: `le_csInf` + the ∀ bound; `≤`: a witness; `=`: both (exact `v` needs a point attaining it) |
| `∃ x ∈ S, ∀ y ∈ S, f x ≤ f y` (argmin/argmax) | `IsCompact.exists_isMinOn` + `fun_prop` continuity |
| `∃ x ∈ Icc a' b', ∀ y ∈ Icc a b, f x ≤ f y` (1D localisation) | min on the sub-box (compactness) + a value `q` with `f ≤ q` somewhere inside and `f > q` on the rest |

`#realfp_min` / `#realfp_max` print an enclosure of the minimum, the approximate minimiser and two
statements `realfp` should then prove; they produce no proof. On failure, `realfp` prints the B&B
estimate and says whether the bound is false (with a point value) or how small the margin is.
Options `trust`, `depth`, `maxBoxes`, `order` apply. Examples:
`RealFPMathlib/Examples/Optimization.lean` (Rosenbrock, camel, Himmelblau, 3 variables, sin/exp;
builds in ~100 s, kernel). Comparison with LeanCert: see [COMPARISONS.md](COMPARISONS.md).
Limitations: kernel cost ~0.1 s per box for a degree-6 polynomial, much more for multivariate
`sin`/`cos`/`exp` (use `trust := native` there); first-order (centred) forms only, no
Hessian/second-order or Taylor-model bounds; boxes only (no constraints); `sInf = v` needs `v`
attained at a rational point; localisation is one-dimensional; argmin needs `fun_prop` to prove
continuity.

### Adding a function (`RealFPMathlib/Registry.lean`, `RealFPMathlib/Extensions/*.lean`)

Real functions beyond the built-in ones are plugged into all realfp tactics through a registry,
without editing the library. The reflected expressions have a node `IExpr.ext k d a` (key `k`,
derivative template `d`, argument `a`); the evaluators, derivatives, domain checks and all
certificate checkers take an extension table `[ExtTbl]` (kernel enclosures, core) and the
soundness theorems additionally `[ExtSem]` (real functions and proofs). A user registers

* `f : ℝ → ℝ` (a constant),
* `F : ExtFn` — `evK : KI → KI` (kernel enclosure, optionally `@[implemented_by]` a faster
  native version), `domK` (differentiability test) and `deriv` (an ext-free `IExpr` template);
  `ExtFn.ofMono` builds `evK` for monotone functions from rational point bounds,
* a theorem `ExtSound f D F`, tagged `@[realfp_fn]`.

The tactics reify `f a` for registered `f`, run the native search with a runtime table of the
registered functions occurring in the goal, and state the proof for auxiliary definitions
`ExtTbl.ofList …` / `ExtSem.ofList …` built from the soundness theorems, so no axiom is added.
Goals without registered functions are unchanged (empty default table).

`RealFPMathlib/Extensions/Erf.lean` registers `erf x = 2/√π ∫₀ˣ e^{-t²}` (defined there, Mathlib
has none): monotone enclosure from the integrated alternating Taylor bounds of `e^{-t²}`
(input rounded to `2⁻³⁰`, odd symmetry, clamped at `|x| ≥ 6`), derivative `2/√π e^{-x²}`.
`RealFPMathlib/Examples/Erf.lean` has bounds, `erf x = 1/2` (∃ and ∃!), a 2×2 system,
`∫₀¹ erf`, and a maximum/argmax. Limitations: unary functions applied as `f a`; ext-free
derivative templates; no C tape for registered functions (Lean evaluation in the search);
`integral_bound` orders ≤ 4 for them; not supported by 2D quadrature or `Interval64.Quad`.

Further registered functions, using Mathlib's definitions (`import RealFPMathlib` includes all):

* `Real.arsinh` (`Extensions/Arsinh.lean`): `ExtFn.ofMonoK` (monotone, endpoint enclosures from a
  point evaluator `P : bits → KI`); for `|q| ≤ 2⁻¹²` the rational bounds
  `q - q³/6 ≤ arsinh q ≤ q - q³/6 + 3q⁵/40` (odd symmetry), else the kernel's
  `log (|q| + √(1 + q²))`. Derivative `1/√(1 + x²)` (Mathlib's `hasDerivAt_arsinh`), everywhere.
* `Real.artanh` (`Extensions/Artanh.lean`), domain `(-1, 1)`: `ofMonoK` guarded by
  `-1 < lo ∧ hi < 1` (exact endpoint values; boxes touching `±1` give `whole` and fail `domK`);
  `q + q³/3 ≤ artanh q ≤ q + q³/3 + q⁵/4` for small `q`, else `½ log ((1 + q)/(1 - q))`.
  Derivative `1/(1 - x²)`, proved here (Mathlib has no derivative lemma for `artanh`).
* `Real.sinc` (`Extensions/Sinc.lean`): on boxes in `[-3, 3]`, evenness and monotonicity in `|x|`
  (proved from `sin x - x cos x ≥ 0` on `[0, π]`) give the bounds from endpoint values (`1` at
  `0`, else `sin q / q`; upper bound `1` when `0 ∈ X`); away from `0`, interval `sin x / x`;
  otherwise `[-1, 1]`. Derivative `(x cos x - sin x)/x²` with `D x := x ≠ 0`: boxes containing
  `0` fail `domK`, so derivative-based modes (monotonicity, centred forms, Taylor quadrature,
  Newton/Krawczyk) are unavailable there and bounds tight at `0` cannot be proved.

Point enclosures have relative error of a few ulps except just above the series threshold
(`≲ 10⁻¹²` relative for `arsinh`/`artanh` near `2⁻¹²`), near zeros of `sinc` (as for `sin`) and
for `artanh` near `±1` (absolute error `~ ulp/(1 - |q|)`). Kernel checking is dominated by the
built-in `log`/`sin` evaluations (~0.1 s each), so tight bounds over many boxes may need
`(trust := native)`. Examples: `RealFPMathlib/Examples/{Arsinh,Artanh,Sinc}.lean` (bounds, `∃!`
roots, integrals, optimisation).

## `interval` tactic (Mathlib layer, `RealFPMathlib/IntervalTactic.lean`)

```lean
import RealFPMathlib   -- or RealFPMathlib.IntervalTactic

example : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * (1 - x) ≤ 1/4 + 1/100 := by interval
example (x : ℝ) (h₀ : 1 ≤ x) (h₁ : x ≤ 2) : Real.exp x < 8 := by interval
example (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : 0 ≤ y ∧ y ≤ 1) : x * y - x - y ≥ -1.01 := by
  interval
example (x : ℝ) (h0 : 2 ≤ x) (h1 : x ≤ 3) : Real.log x ∈ Set.Icc (0.69 : ℝ) 1.1 := by interval
example : 1.414 < Real.sqrt 2 := by interval
example … := by interval (depth := 30) (maxBoxes := 100000) (chunk := 32)
```

* **Goals**: `f ≤ c`, `f < c`, `c ≤ f`, `c < f`, `≥`, `>`, conjunctions, `f ∈ Set.Icc a b`;
  `f ≤ g` / `f < g` with no numeral side becomes `f - g ≤ 0`. Binders are introduced.
* **Terms**: `+ - * / ⁻¹`, `Real.sqrt`, `|·|`, `^ n` (numeral `n : ℕ`), `Real.exp`, `Real.log`,
  `Real.sin`, `Real.cos`, `Real.arctan`, `Real.pi`, `Real.sinh`, `Real.cosh`, `Real.tanh`,
  `Real.logb 2`, `Real.logb 10`, `Real.tan`, `Real.arcsin`, `Real.arccos`, `Complex.arg (↑x + ↑y * Complex.I)`, rational numerals (anything `norm_num` evaluates to a rational,
  e.g. `0.1`, `1/3`), any number of real variables.
* **Variables** need numeral bounds `a ≤ x`, `x ≤ b` (strict ones are weakened, `∧` and
  `Set.Icc`/`Ioo`/… hypotheses are split) in the context.
* **Method**: reify to `IExpr`; search a bisection certificate natively with the *same*
  evaluator the kernel runs (`evalK`; splits the widest variable at its float midpoint,
  up to `depth` levels / `maxBoxes` boxes); check it by `decide +kernel` on `checkK`
  (subtrees of `chunk` boxes per call, glued by `checkK_split_of`, keeps kernel memory
  bounded). Soundness once and for all: `RealFP.eval_sound` (`denote xs e ∈ evalI env e`),
  `checkK_sound`, `prove_le/lt/ge/gt` (`RealFPMathlib/IntervalSound.lean`).
* **Trust**: standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
* **Cost**: a few ms of kernel time per box for polynomial terms (2306 boxes, 2 variables: ~10 s), much more with
  transcendental functions (see table); trace with `set_option trace.interval true`.
* **Limits**: `log` of an interval not strictly positive gives `whole`;
  `sqrt` of a partly negative interval is hulled with `0` (matches `Real.sqrt`).

### Derivative certificates (`Interval64/Kernel/Deriv.lean`, `RealFPMathlib/IntervalDeriv.lean`)

Bounds that are *touching* (equality at a point of the box) are provable:

```lean
example (x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1) : 1 + x ≤ Real.exp x := by interval
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2) : Real.sin x ≤ x := by interval
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x - x^3/6 ≤ Real.sin x := by interval
```

* `IExpr.diff i`: symbolic partial derivative (all operations except `|·|`);
  `IExpr.deriv i := (diff i).dsimp` folds rational constants *exactly* (so e.g. `36·(1/36)`
  is `1`, not an interval of width 1 ulp). The derivative enclosure is the interval
  evaluation of `deriv` (the same interval operations as forward-mode AD, without sharing).
  `hasDerivAt_denote`: `HasDerivAt (fun t => e.denote (xs.set i t)) ((e.diff i).denote xs) _`
  wherever `Dom` holds (denominators ≠ 0, `sqrt`/`log` arguments > 0); `domOK_sound`
  checks `Dom` on a box.
* Certificates (`DCert`): `leaf`, `split`, `mono i inc dc c` (the sign of ∂f/∂xᵢ on the box is
  proved by the nested certificate `dc`, by any of these methods, i.e. higher derivatives;
  then `f` is only checked on the face `xᵢ = hi` or `lo`), `center i m` (centred form
  `f(m) + f′(X)·(X − m)` intersected with the naive enclosure). Soundness: `checkD_sound`
  (mean value theorem), `proveD_le/lt/ge/gt`, `checkD_split_of`.
* Search: leaf → monotone in a variable with a visible derivative sign → centred form at
  the split midpoint → monotone with the sign proved recursively up to `order`
  derivatives → bisection.
* Options: `(deriv := false)` (plain bisection, as before), `(order := n)` (default 3).
  Options can be given in any order.
* Box counts on the 33 earlier tests (deriv off → on), all others unchanged at 1–2:

  | test | off | on | | test | off | on |
  |---|---|---|---|---|---|---|
  | t02 | 18 | 4 | | t13 | 57 | 9 |
  | t05 | 294 | 17 | | t18 | 58 | 4 |
  | t06 | 402 | 17 | | t19 | 2 | 1 |
  | t08 | 86 | 4 | | t23 | 37 | 2 |
  | t09 | 280 | 28 | | t28 | 2306 | 3 |
  | t10 | 12 | 8 | | t31 | 64 | 4 |
  | t12 | 6 | 2 | | **total (33)** | **3645** | **126** |

  Per test 2.5–3.7 s including ~2 s Lean startup (before: up to 12.6 s).
* Tests: `RealFPMathlib/RealFPMathlib/Tests/IntervalTest.lean`.

### Precision 128 in `interval` (`Interval128/Dyadic.lean`, `RealFPMathlib/I128Dyadic.lean`)

`interval (precision := 128)` (also `realfp (precision := 128)` on interval goals) evaluates
the reified `IExpr` with 128-bit dyadic endpoints instead of Interval64:

```lean
example : Real.sqrt 2 - 1.4142135623730950488 < 1.7e-21 := by interval (precision := 128)
example : Real.pi < 3.14159265358979323846264338327951 := by interval (precision := 128)
example (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 2) : x ^ 2 - x / 3 ≤ 10 / 3 + 1e-30 := by
  interval (precision := 128) (depth := 110)
```

* **Numbers** (`Interval128/Dyadic.lean`, namespace `Interval128.Dy`, core, Mathlib-free).
  `Dy = ⟨m e : Int⟩` is `m · 2^e`; `rdn` / `rup` round to `prec = 128` significant bits
  (floor / ceiling division by a power of two), `addX` / `mulX` are exact, `ofRatDn` /
  `ofRatUp` round a rational, `invDnPos` / `invUpPos` bound `1 / (m · 2^e)`, `sqrtDn` /
  `sqrtUp` bound `√(m · 2^e)` from a Newton guess that the definition itself checks
  (`r * r ≤ n`, `n ≤ r * r`). Everything is `Nat`/`Int` arithmetic, which the kernel runs
  with GMP, and the same definitions are compiled for the search and `native_decide`.
* **Intervals** `DI = ⟨lo hi : Option Dy⟩` (`none` = unbounded). `evalQ`: `+ - *` (corner
  products), `/` and `⁻¹` (when the divisor's endpoints have one strict sign, else the whole
  line), `√`, `|·|`, `^ n` (even powers from `|X|`), rational constants, `π` from
  `[3.1415926535897932384626433832795028841971, …972]` (`RealFP.pi_gt_d40` / `pi_lt_d40` in
  `RealFPMathlib/PiBounds.lean`: Mathlib's `pi_lower_bound` / `pi_upper_bound` with 70 square
  roots, witnesses from `scripts/pigen.py 40 70`, standard axioms). **Everything else** (`exp`,
  `log`, `sin`, `cos`, `atan`, `atan2`, hyperbolic, `logb`, `tan`, `arcsin`, `arccos`,
  registered functions) goes through `lift1` / `lift2`: `KI.ofRatInterval` of the endpoints,
  the Interval64 kernel evaluator `evalK`, and the exact rational value of the result bits
  (`decLo` / `decHi`). Those results are only as tight as Interval64; the failure message
  lists them.
* **Goal predicates** `gLe c` / `gLt c` / `gGe c` / `gGt c` compare the exact rational value of
  an endpoint (`toRat`) with `c`.
* **Certificates** `Interval128.Dy.Cert`: bisection trees whose split points are dyadics (the
  rounded midpoint, strictly inside the box). The tactic emits a split point as
  `Interval128.Dy.ofLimbs neg limbs e` with base-`2^62` limbs: the kernel is much slower on
  terms that contain `Nat` literals of `2^63` or more (60 boxes: about 40 s with plain
  literals, under 1 s with limbs). `checkQ` walks the tree; `search` (compiled, untrusted)
  splits the widest variable. No derivative or centred-form certificates at 128 yet.
* **Soundness** (`RealFPMathlib/I128Dyadic.lean`, namespace `RealFP.I128Q`, no `sorry`,
  standard axioms): `val d = m · 2^e`, `val_rdn` / `val_rup` / `val_ofRatDn` / `val_ofRatUp` /
  `val_invDnPos` / `val_sqrtDn` …, `mem_add` / `mem_mul` / `mem_inv` / `mem_sqrt` /
  `mem_abs` / `mem_pow` / `mem_pi` / `mem_lift1` / `mem_lift2`, `evalQ_sound`,
  `checkQ_sound`, `checkQ_split_of`, `prove_le` / `prove_lt` / `prove_ge` / `prove_gt`.
* **Checking.** `trust := kernel` closes `checkQ … = true` with `decide +kernel`, `chunk`
  boxes per call; `trust := native` uses `native_decide`. Kernel cost is about 10–30 ms per
  box (`RealFPMathlib/Examples/Precision128.lean` has the timings; before this path, with the
  double-double `Float` specification, a box cost 0.1–0.3 s per operation).
* The double-double path (`Interval128.Refl.checkD`, `RealFPMathlib/I128Sound.lean`) is still
  in the library and proved, but the tactic no longer uses it.
* Not yet at 128: `≠` goals, `root_exists` / `root_unique`, optimisation (`#realfp_min`,
  `sInf`, witnesses), `integral_bound`, `pos_def`. `realfp (precision := 128)` on such goals is
  an error; `(precision := 64)` is accepted everywhere.
* When a precision-64 attempt fails with a margin at binary64 resolution, its message suggests
  `(precision := 128)`.

## Representability, `ofRat`, and tightness

`Interval64/OfRat.lean` defines `Spec.Representable q` (some bit pattern has
value `q`, decidable via `Spec.isRepresentable`), `Spec.ofRatDown` /
`Spec.ofRatUp` (directed rounding of a rational, with IEEE overflow to `±inf`
and `maxFinite`), and `Interval64.ofRat` / `ofRatInterval`.

Proved (kernel-checked, axioms `propext`, `Classical.choice`, `Quot.sound` only):

* `OfRat`: `ofRatDown q` is the greatest representable `≤ q` (`-inf` iff none),
  `ofRatUp q` the least `≥ q`; `Representable q ↔ value (ofRatDown q) = q`.
* `Tight`: `addDown/subDown/mulDown/divDown` (nonzero divisor) are the tight
  roundings of the exact result, hence equal `ofRatDown` of it at value level;
  same for `Up`. No representable value lies strictly inside the gap.
* `TightSqrt`: `sqrtDown a` is the greatest representable `ρ ≥ 0` with
  `ρ² ≤ qa`, `sqrtUp a` the least with `qa ≤ ρ²`.
* `TightIv`, `TightSqrt`: for finite-endpoint intervals, `X+Y`, `X-Y`, `X*Y`,
  `X/Y` (`0 ∉ Y`) and `sqrt X` (`hi ≥ 0`) have the greatest representable
  lower bound and least representable upper bound of the exact range.

## Mathlib layer (optional): theorems over `ℝ`

The core stays Mathlib-free. `RealFPMathlib/` is a **separate Lake package**
that requires the core by path (`require interval64 from ".."`) and Mathlib,
and restates the core theorems over Mathlib's real numbers. Users who only
want fast intervals never build or download Mathlib.

**Toolchain pinning.** Mathlib must be built for exactly the same Lean as the
core. `RealFPMathlib/lean-toolchain` is `leanprover/lean4:v4.36.0` (same as
the root) and the lakefile pins Mathlib tag `v4.36.0`. When you upgrade Lean,
bump the root `lean-toolchain`, `RealFPMathlib/lean-toolchain` and the Mathlib
tag together, then `lake update` in `RealFPMathlib/`.

```bash
cd RealFPMathlib
lake exe cache get        # prebuilt Mathlib oleans (~5 GB, a few minutes); never build Mathlib
lake build                # core (C kernels too) + the Mathlib layer, including Examples and the full axiom audit
lake build RealFPMathlib.AxiomAuditCore
                          # library + Demo + Tests and the axiom audit, without Examples
lake lean Examples.lean   # runnable examples (#eval uses the C kernels)
scripts/check_axioms.sh   # axiom report for every theorem of the layer
```

Use it from your own Mathlib project (same Lean and Mathlib versions) with
`require realfp_mathlib from "path/to/realfp/RealFPMathlib"` and
`import RealFPMathlib` (theorems, the tactics from `RealFPMathlib.Front`, and the short kernel
names from `RealFPMathlib.Kernel`). (A git requirement with subdirectory,
`... from git "https://github.com/schlafly1/realfp" @ "main" / "RealFPMathlib"`,
should also work but has not been tested.)

**What it provides** (namespace `RealFP`; files in `RealFPMathlib/RealFPMathlib/`):

* `Basic`: `Float.toReal? : Float → Option ℝ` (exact value, `none` for ±∞/NaN),
  `Float.toReal` (total, junk `0`), `Interval64.toSet : Interval64 → Set ℝ`
  (extended-real reading: a `-∞`/`+∞` end gives an unbounded set, NaN gives `∅`;
  `toSet_eq_Icc` for finite endpoints), `le_of_mem_hiLe` / `ge_of_mem_loGe` (real bounds from
  the Boolean checks `X.hiLe q` / `X.loGe q`), `RepresentableR`, `IsRoundDownR`,
  `IsRoundUpR` with transfer lemmas from the rational versions.
* `Mem` (enclosure for real inputs):
  `add_mem_toSet`, `sub_mem_toSet` (`x ∈ X.toSet → y ∈ Y.toSet → x + y ∈ (X + Y).toSet`,
  infinite endpoints allowed). The finite-endpoint `mul_mem_toSet`,
  `div_mem_toSet`, `sqrt_mem_toSet` are deprecated in favour of:
* `Unbounded`: `mem_toSet_mul` (`x * y ∈ (X * Y).toSet`), `mem_toSet_div`
  (`y ≠ 0`), `mem_toSet_sqrt` (`0 ≤ x`), with **no finiteness hypotheses**
  (half-lines and `whole` work, including the `0 · ∞` and `∞ / ∞` corners). They
  are built on `Ext` (`Float.toE : Float → EReal`, an order isomorphism on
  non-NaN floats: `float_le_iff_toE`, `mem_toSet_iff_toE`, `toE_fmin`, …) and
  `Corners` (which corner of the four bounds a product or quotient in `EReal`).
* `Ops`: the theorems for `Interval64/Ops.lean`
  ([above](#more-interval-operations-interval64opslean)).
* `Tight`: `addDown_isRoundDownR` … `divUp_isRoundUpR`, `sqrtDown_isRoundDownR`,
  `sqrtUp_isRoundUpR`: the directed result is the greatest representable real
  `≤` (least `≥`) the exact real result, so `IsRoundDownR.no_between`: no
  representable real lies strictly between. Interval level: `add/sub/mul/div_iv_optimalR`
  (`div` needs `containsZero Y = false`), `add/sub_iv_tightR`, `sqrt_iv_tightR`,
  `sqrt_iv_optimalR`; `ofRatDown_isRoundDownR`, `mem_toSet_ofRatInterval`.
* `Demo` (not imported by `RealFPMathlib`): `sq_add_le : ∀ x ∈ Set.Icc (1/10 : ℝ) (3/10), x * x + x ≤ 13/32`,
  `sqrt_two_bounds : 1.41421356 < √2 < 1.41421357`, `sqrt_le_on : ∀ x ∈ [2,3], √x ≤ 111/64`.

**Trust.** Everything outside `Demo`/`Examples` uses only `propext`,
`Classical.choice`, `Quot.sound` (the `Examples` and the `interval` tests do too).
Only the `Demo` theorems use `native_decide`
(one generated axiom each, and the compiled C kernels are trusted).
`scripts/check_axioms.sh` enforces this. Mathlib itself does not accept
`native_decide`, so proofs that use it are fine in your projects but cannot be
upstreamed; facts small enough for `decide +kernel` avoid the extra axiom.

### Worked examples (`RealFPMathlib/RealFPMathlib/Examples/`)

* `Cubic.lean` — `cubic_bound : ∀ x : ℝ, 0 ≤ x → 6x - x³ ≤ (6√2 - √2³) + 0.001`.
  On `[0, 5/2]` the bound `x * (6 - x*x) ≤ 5.6578` is closed by the `interval` tactic
  (adaptive bisection, 294 boxes instead of the former fixed 20480-box grid; kernel-checked,
  ~3 s, **no `native_decide`**); `c ≤ 4√2 + 0.001` is also `interval`. `x ≥ 5/2` is algebra.
  The old hand-written grid checker `allOK` / `allOK_sound` is kept for reference.
* `Jacobian.lean` — `F(x,y,z) = ((1+xy)³z + y²(1+xy)(4+3xy), y + 3x(1+xy)²z + 3xy²(4+3xy), 2x - 3x²y - x³z)`.
  Mathlib `HasDerivAt` partials, `jac_det : det = -2` everywhere, `F_not_injective`,
  `F_eq_iff` (all solutions of `F = (a,0,0)`, `a ≠ 0`), `solutions_quarter` /
  `ncard_solutions_quarter` (exactly the 3 given points), `solutions_026` /
  `ncard_solutions_026` (exactly 3 solutions: `(0,0,-0.26)`, `(±s, ∓3/(2s), 169/25)`,
  `s = √(25/26)`), with 10-digit enclosures `s_bounds`, `y_bounds` proved by `interval`.
  Nothing in this file uses `native_decide` any more.
* `Ops.lean` — `square` vs `*` on `[-1, 2]`, `pown`, and the other new operations,
  all by `decide +kernel`.

## Computer-assisted-proof toolkit: PD matrices, polynomials, quadrature

Aimed at proofs like Alpöge–Buckmaster (Navier–Stokes), which reduce to checking many matrix
positivity, polynomial-sign, and integral bounds. Interval64 only. The Lean definitions are the
specification. The PD kernel also has a C runtime (`@[implemented_by]`, bit-identical to the spec
and tested). Soundness theorems over `ℝ` are in the Mathlib layer.

### Positive definiteness (`Interval64/Matrix.lean`, `c/iv64_matrix.{h,c}`, `RealFPMathlib/Matrix.lean`, `MatrixPD.lean`)

`IMat` is an `n × n` interval matrix stored as row-major `lo`/`hi` `FloatArray`s. The certificate
works like this:

1. Compute an *untrusted* `X ≈ L⁻¹` from a float Cholesky of `mid M` (`approxX`).
2. Compute the lower triangle of the interval matrix `B = X M Xᵀ` with directed rounding.
3. Check that every Gershgorin margin `B_ii − Σ_{l≠i} |B_il|` has `lo > 0`, and that `X` is
   finite.

A strictly diagonally dominant symmetric `B` is PD. That forces `X` to be invertible, so `A` is
PD as well. The check is fast and sound: no validity checks are added to the basic interval ops.

| check | theorem (Mathlib conclusion, for every symmetric real `A ∈ M`) |
|---|---|
| `isPD M`, `pdCheck M X` | `posDef_of_isPD`, `posDef_of_pdCheck` : `A.PosDef` |
| `lamMinGt M s`, `lamMinCheck M X s` | `posDef_sub_of_lamMinGt` : `(A − s•1).PosDef`; `lt_eigenvalue_of_lamMinCheck` : `s < μ` for every eigenvalue `μ` |
| `isGt M N`, `gtCheck M N X` | `posDef_sub_of_isGt`, `posDef_sub_of_gtCheck` : `(A − B).PosDef` (Loewner `A > B`) |

The C kernel `iv64_pd_margins` costs `O(n³)`. On a KMS interval matrix
(`interval64_bench`, x86-64 box) it takes:

| n | 50 | 100 | 200 | 400 |
|---|---|---|---|---|
| `pdMargins` (C) | 0.65 ms | 5.6 ms | 44 ms | 363 ms |
| `approxX` (Lean, untrusted) | 0.33 ms | 2.1 ms | 13 ms | 90 ms |
| Lean spec (for comparison) | 18 ms | 141 ms | — | — |

### Polynomials (`Interval64/Poly.lean`, `RealFPMathlib/Poly.lean`)

`IPoly := Array Interval64` holds coefficients, low degree first. `Contains P p` means every
`p.coeff k ∈ P.coeff k`.

- **Constructors:** `ofFn`, and `ofRats` together with `ratPoly` (`contains_ofRats`).
- **Evaluation:**
  - `eval` (Horner), theorem `mem_eval`.
  - `evalMV` (Horner ∩ mean-value form), theorem `mem_evalMV`.
- **Arithmetic:** `add`, `sub`, `neg`, `smul`, `mul`, `deriv`, `integ`, `comp`, `shift`, with
  theorems `contains_add`, …, `contains_integ`, `contains_comp`, and `contains_shift`
  (`p.comp (X + C a)`).
- **Range enclosure by bisection:** `range`, theorem `mem_range`.
- **Sign certificates:**
  - `checkGe` / `checkGt` / `checkLe` / `checkLt`, theorems `le_of_checkGe`, `lt_of_checkGt`,
    `ge_of_checkLe`, `gt_of_checkLt`.
  - Bivariate: `IPoly2`, `eval2`, `checkGe2` / `checkGt2`, theorems `mem_eval2`,
    `le_of_checkGe2`, `lt_of_checkGt2` (for `eval2R x y p = (p.eval (C y)).eval x`).

### Quadrature (`Interval64/Quad.lean`, `RealFPMathlib/Quad.lean`)

- `polyIntegral P A B`: exact antiderivative. Theorem `integral_mem_polyIntegral`:
  `∫ x in a..b, p.eval x ∈ polyIntegral P A B`.
- `integrate (cell0 F) a b tol fuel`: adaptive bisection with cells `F([lo,hi])·(hi−lo)`.
  Theorem `integral_mem_integrate0`; `f` only needs to be continuous.
- `integrate (cell1 F D) a b tol fuel`: second-order cells
  `F(m)(hi−lo) + D(X)(hi−m)²/2 − D(X)(m−lo)²/2`, intersected with `cell0`. `D` encloses `f'`.
  Theorem `integral_mem_integrate1`.
- `IExpr` front ends `integrateE0` / `integrateE1` (derivative by `IExpr.diff`). Theorems
  `integral_mem_integrateE0` (needs continuity) and `integral_mem_integrateE1` (needs `Dom`).

All conclusions are statements about Mathlib's `intervalIntegral`. Measured widths for
`∫₀¹ e^{-x²}`: `cell1` gives 1.4e-4 with 2⁶ cells (2 ms), 1e-6 with 2¹⁰ (33 ms), and 2e-9 with
2¹⁴ (0.5 s). `cell0` gives 3.9e-5 with 2¹⁴ cells (14 ms).

### Kernel fast path for PD and quadrature (`Interval64/Kernel/{Matrix,Quad}.lean`)

**Short names.** `RealFPMathlib/Kernel.lean` (imported by `RealFPMathlib`) exports the names
below into `RealFP`, so after `open RealFP` you write `KI`, `IExpr`, `IExpr.denote`,
`ofRatFn`, `PDCert`, `pdCheckL`, `pdCheckK`, `ratMatOK`, `quadK`, `quadBound`,
`posDef_of_ratMat`, `posDef_of_pdCheckL`, `posDef_of_pdCheckK`, `lt_eigenvalue_of_posDef_sub`,
`integral_mem_quadK`, `integral_bounds_of_quadBound` instead of `Interval64.KF.KM.ofRatFn`,
`RealFP.KM.posDef_of_ratMat`, `Interval64.KF.KQ.quadBound`, `RealFP.KQ.…` (those long names
still work; the short ones are aliases).

The checks below run on the `KF`/`KI` Nat-bit-pattern kernel (the same evaluator the `interval`
tactic uses), so `decide +kernel` is much cheaper than running the Float specification.

- **PD** (`KF.KM`, soundness `RealFPMathlib/KMatrix.lean`):
  - `pdCheckK n A X` recomputes `T = X A`, `B = T Xᵀ` in the kernel.
  - `pdCheckL n A c` checks a literal certificate `c : PDCert` (`X`, `T`, `B` computed natively by
    the `pd_certs% n A` elaborator) entry by entry. The kernel does not share subterms, so this
    avoids recomputing `T`.
  - `ratMatOK n A f`: every entry of `A` (a literal from `ki_lit% (ofRatFn n f)`) contains the
    rational `f i j`.
  - Theorems: `posDef_of_pdCheckK`, `posDef_of_pdCheckL`,
    `posDef_of_ratMat : (Matrix.of fun i j => (f i j : ℝ)).PosDef`, and
    `lt_eigenvalue_of_posDef_sub`.
- **Taylor quadrature** (`KF.KQ`, soundness `RealFPMathlib/{TaylorBound,KQuad}.lean`):
  - Each cell `[lo, hi] ∋ m` gets `Σ_{j<K} f⁽ʲ⁾(m)·mom_j + f⁽ᴷ⁾([lo,hi])·mom_K`, with
    `mom_j = ((hi−m)^{j+1} − (lo−m)^{j+1})/(j+1)!`. Here `K > 0` is even and the derivatives come
    from `IExpr.deriv`. The error is `O(h^{K+1})` overall.
  - `quadK e K a b cells` returns the enclosure; `quadBound … qa qb ql qh` checks
    `ql ≤ ∫_qa^qb ≤ qh`.
  - Theorems:
    - `RealFP.Taylor.integral_mem_taylorCell`: Lagrange bounds by the MVT, proved against
      `intervalIntegral`.
    - `RealFP.KQ.integral_mem_quadK`
    - `RealFP.KQ.integral_bounds_of_quadBound`
  - Elaborators `cells% a b N` (uniform cells) and `bits% x`.

Native widths for `∫₀¹ e^{-x²}`:

| rule | width |
|---|---|
| K=4, 8 cells | 8.6e-7 |
| K=4, 16 cells | 2.7e-8 |
| K=6, 8 cells | 1.3e-9 |
| K=8, 4 cells | 7.9e-10 |
| K=8, 16 cells | 4e-15 |
| `cell1`, 2¹⁴ cells | 2e-9 |

**Kernel `decide +kernel` timings.** Wall time and peak memory of the `lean` process, x86-64 box.
"Core" means importing `Interval64` only (≈1.0 s / 1.1 GB); Mathlib files import ≈2.5 s / 3.4 GB.

| check | before (Float spec) | after (KF/KI path) |
|---|---|---|
| Hilbert 6 PD | 21.5 s / 4.9 GB | `pdCheckK`: 2.6 s / 1.8 GB (core) |
| Hilbert 8 PD | — (too slow) | `pdCheckL`+`ratMatOK`: 3.6 s / 1.9 GB (core) |
| Hilbert 10 PD | — | `pdCheckL`+`ratMatOK`: 6.7 s / 2.3 GB (core); theorem `hilbert10_posDef` 9.2 s / 4.2 GB |
| `1−x+x²/2−x³/6+x⁴/24 > 0` on [0,4] | `checkGt`: 14.8 s / 4.4 GB | `interval` tactic: ≈8 s for two goals incl. import, 3.1 GB; Bernstein `checkGtB`: 12.8 s / 4.5 GB |
| `∫₀¹ e^{-x²}` bounds | `cell1`, 16 cells, width 3e-3: 49.7 s / 7.1 GB | `quadBound` K=4, 4 cells, `[0.7468, 0.7469]`: 7.2 s / 3.9 GB |

### Bernstein range enclosures (`Interval64/Bernstein.lean`, `RealFPMathlib/Bern.lean`)

- **1D:** `bernCoeffF` computes `β_k = Σ_{i≤k} C(k,i)/C(n,i)·a_i`.
  - `bern01 P n` is the hull of the `β_k` on `[0,1]`. Choosing `n` above the degree gives degree
    elevation.
  - `bernOn P X n` maps the box `X` to `[0,1]` affinely.
  - `bernRange P n fuel X` subdivides; `checkGtB` / `checkGeB` are the sign checks.
  - Theorems: `pow_eq_sum_bern`, `eval_eq_sum_bern`, `mem_bern01`, `mem_bernOn`,
    `mem_bernRange`, `lt_of_checkGtB`, `le_of_checkGeB`.
- **2D tensor form:** `IPoly2.bern2On P X Y n m`.
  - Expand each `P_j(x(s))` in Bernstein form, then enclose `Σ_j β_{k,j} y^j` on `Y` with the 1D
    rule, and take the hull over `k`.
  - `checkGt2B` uses 4-way subdivision.
  - Theorems: `mem_bern2On`, `lt_of_checkGt2B`.
- Example: `1−x+x²/2−x³/6+x⁴/24` on [0,4]. Bernstein degree 12 gives `[0.168, 5]`; Horner gives
  `[−5.67, 5]`.

### 2D quadrature over rectangles (`Interval64/Quad2.lean`, `RealFPMathlib/Quad2.lean`)

- `integrate2 F a b c d tol fuel` is an iterated adaptive rule: the outer zeroth-order cells use
  the inner rule's enclosure as the integrand.
- `integrate2E0 e …` handles `IExpr` integrands in `x = var 0`, `y = var 1`.
- `integrate2E1 e …` uses second-order cells in `y` (from `e.diff 1`) and zeroth order in `x`.
- Theorems:
  - `integral2_mem_integrate2`, `integral2_mem_integrate2E0`, `integral2_mem_integrate2E1`:
    iterated `intervalIntegral`, `f` continuous on the rectangle.
  - `setIntegral_rect_eq` (Fubini):
    `∫_{[a,b]×[c,d]} f = ∫_a^b ∫_c^d f`.
- Native result for `∫∫_{[0,1]²} e^{-x²-y²}` = 0.5577…: E0 gives `[0.5504, 0.5651]`; E1 gives
  `[0.5559, 0.5596]`.

### Higher-order 2D quadrature (`Interval64/Quad2.lean`, `Interval64/Kernel/Quad2.lean`, `RealFPMathlib/{Taylor2,KTaylor2}.lean`)

`Quad.taylor2 e K a b c d xs ys` (even `K > 0`, grids `xs`, `ys` of cells `(lo, m, hi)`): on each
cell, Taylor of order `K` in `y` around `m_y` with the Lagrange remainder enclosed on the cell,
then Taylor of order `K` in `x` for each `y`-coefficient `∫ ∂ᵧⁱ f (x, m_y) dx`; cells are summed
over the grid. Per-cell error `O(h^{K+1})` per unit area. At runtime it runs in C over one
derivative tape (`iv64_quad_taylor2`, ×69 vs the Lean-compiled spec for `K=4`, 8×8 cells).
`KF.KQ.taylor2K` / `taylor2Bound` is the bit-pattern (`KI`) mirror for `decide +kernel`.

* `RealFP.Taylor2.integral2_mem_t2Cell` (one cell), `integral2_mem_taylor2` (grid, iterated
  Mathlib integral; `Dom` of all `∂ₓʲ∂ᵧⁱ e`, `i, j ≤ K`, and continuity on the rectangle),
  `integral_rect_mem_taylor2` (Bochner integral over `[a,b]×[c,d]`, Fubini),
  `integral2_mem_taylor2_smooth` (side conditions from `allSmooth e K = true`).
* `RealFP.KTaylor2.integral2_mem_taylor2K`, `integral2_bounds_of_taylor2Bound` (no side
  conditions: the certificate checks `allSmooth`).
* Example `RealFP.Examples.Taylor2.gauss2_bounds` / `gauss2_rect_bounds`:
  `0.5566 ≤ ∫₀¹∫₀¹ e^{-x²-y²} ≤ 0.5585` with `K = 4` on 2×2 cells (kernel ≈ 15 s, enclosure width
  1.7e-3). Slow lib: `gauss2_bounds_tight`, `[0.557715, 0.55777]`, 4×4 cells (≈ 65 s, 7 GB).

∫∫_{[0,1]²} e^{-x²-y²} (true 0.557746), enclosure widths:

| rule | cells | width | time (C) |
|---|---|---|---|
| `integrate2E1` (first order) | 2^4×2^4 | 3.2e-2 | 0.2 ms |
| `integrate2E1` | 2^8×2^8 | 1.9e-3 | 47 ms |
| `taylor2` K=2 | 16×16 | 8.8e-5 | 0.19 ms |
| `taylor2` K=4 | 2×2 | 1.7e-3 | 1.3 ms |
| `taylor2` K=4 | 4×4 | 4.9e-5 | 1.3 ms |
| `taylor2` K=4 | 8×8 | 1e-6 | 1.4 ms |
| `taylor2` K=6 | 4×4 | < 1e-6 | 51 ms |

Times are dominated by building the derivative tape (symbolic `∂ₓʲ∂ᵧⁱ`, no CSE in `dxy`); `K = 8`
takes ≈ 3.8 s. Limits: `allSmooth` covers polynomial operations, `exp`, `sin`, `cos`, `atan`,
`sinh`, `cosh` (other integrands use `integral2_mem_taylor2` with explicit `Dom`); C needs
`K ≤ 17`.

### C kernels for polynomials, Bernstein and quadrature (`c/iv64_poly.{h,c}`, `c/iv64_quad.h`)

The Lean definitions stay the specifications (the proofs and `decide +kernel` use them). At
runtime, these routines run as single C functions attached with `@[implemented_by]`:

- **Polynomials:** `IPoly.eval`, `evalMV`, `rangeAux` (so `range`), `checkGe`/`Gt`/`Le`/`Lt`,
  `IPoly2.eval2`, `checkGe2`/`Gt2`.
- **Bernstein:** `bernOn`, `bernRange`, `checkGtB`/`GeB`, `bern2On`, `checkGt2B`. These need
  Bernstein degree ≤ 56, so that the binomials are exact doubles and `ofRat (C(k,i)/C(N,i))`
  equals `[÷↓, ÷↑]`. Larger degrees run the Lean definition.
- **Quadrature:** `Quad.integrateE0`/`E1` and `integrate2E0`/`E1`. These run the whole adaptive
  rule in C.
- **Taylor quadrature:** `KQ.quadF`, the `Interval64` mirror of the kernel rule `quadK`, used by
  `integral_bound`'s search.

For the quadrature routines, the integrand `IExpr` is compiled to a *tape* (`Interval64/Tape.lean`):
straight-line code with shared subexpressions. The C evaluator does the arithmetic (`+ − × ÷`,
`inv`, `√`, `|·|`, `xⁿ`) with the same `Interval64` operations. Elementary functions call back
the Lean closures (`Interval64.exp`, `sin`, …), so they are the same functions.

The C code uses the existing backends: AVX-512 embedded rounding on x86-64, and RN + exact error
term on arm64. It performs the same `Interval64` operations in the same order, including the
literal `[0, 0]` padding of the spec, so the results are bit-identical. This is checked by the
differential tests (`interval64_tests`, section "C poly / Bernstein / quadrature kernels"). They
compare the C results with Lean-only copies of the specifications (`Interval64CSpec.lean`) on
400 random 1D and 150 random 2D polynomials (with special boxes), on 600 random expressions × 4
boxes for the tape evaluator, and on the quadrature routines. They also check `quadF` against
both `quadFSpec` and the kernel `quadK`.

Benchmarks (`interval64_bench`, x86-64 box, one call each):

| routine | C | Lean-compiled spec | speedup |
|---|---|---|---|
| `eval`, degree 20 | 0.20 µs | 3.3 µs | ×17 |
| `evalMV`, degree 20 | 0.53 µs | 10 µs | ×19 |
| `range`, 2⁸ boxes | 0.26 ms | 2.5 ms | ×10 |
| `checkGt` e4 on [0,4], fuel 12 | 31 µs | 54 µs | ×1.7 |
| `bernRange`, degree 20, 16 boxes | 0.32 ms | 7.2 s | ×2·10⁴ (the spec rounds rationals with `ofRat`) |
| `checkGtB` e4, degree 6, fuel 4 | 0.85 µs | 0.22 ms | ×260 |
| `bern2On`, 3×3, degree 6 | 4.7 µs | 2.2 ms | ×475 |
| `integrateE0` ∫₀¹e^(−x²), 2¹⁰ cells | 0.11 ms | 0.90 ms | ×8 |
| `integrateE1` ∫₀¹e^(−x²), 2¹⁰ cells | 0.33 ms | 34 ms | ×100 |
| `integrate2E1` ∫∫e^(−x²−y²), 2⁶×2⁶ | 3.0 ms | 295 ms | ×98 |
| Taylor `quadF`, K=4, 16 cells | 0.13 ms | 2.4 ms (KF Nat path natively: 202 ms) | ×19 (×1600) |
| Taylor `quadF`, K=8, 16 cells | 9.3 ms | 144 ms (KF Nat path natively: 10 s) | ×15 (×1000) |
| Taylor `quadF` ∫₀³ sin(x²), K=8, 64 cells | 13 ms | 1.7 s | ×136 |

### `integral_bound` tactic (`RealFPMathlib/IntegralTactic.lean`)

It proves `c ≤ ∫ x in a..b, f x`, `∫ … ≤ c`, `<`, conjunctions, and `∈ Set.Icc`.

- Options: `(trust := kernel|native)`, `(order := n)` (only that Taylor order, 2/4/6/8),
  `(maxBoxes := n)` (cell limit, default 512); anything else is an error.
- `a`, `b`, `c` must be rational numerals, with `a` and `b` exact floats. `f` may use the
  `interval` tactic's operations.
- **Search (native, C kernels).** For each `K ∈ {2,4,6,8}` it bisects the cells with the widest
  `cellF` enclosures (adaptive, at most 512 cells) until the Float enclosure meets the bounds,
  and picks the `K` with the lowest estimated kernel cost (cells × shared-let cost, a
  transcendental let counting 30).
- **Derivatives.** `diff` has a power-denominator quotient rule
  `(a/bⁿ⁺¹)' = (a'b - (n+1)ab')/bⁿ⁺²`, so the derivatives of `1/x`, `1/(1+x²)` … stay small.
- **Certificate.** The derivatives are hash-consed into shared `lets` (`shareDerivs`, untrusted;
  the kernel checks `shareOK`: expanding the roots gives exactly `derivs e K`). The values of
  every let in every cell (point and box environment) are passed as witnesses; each witness list
  is checked by its own small auxiliary theorem (`letsW … = true` by `rfl`, combined with
  `RealFP.KQS.cellsW_cons`), and the main `decide +kernel` checks `quadBoundW`, so every kernel
  operation runs on literal inputs and each `sin x`, `cos x` … is evaluated once per cell
  environment. Soundness: `RealFP.KQS.quadKW_some` (`quadKW = quadKS`), `quadKS_some`
  (`quadKS = quadK`), `integral_bounds_of_quadBoundW`.
- `example : (∫ x in (0:ℝ)..1, Real.exp (-x^2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by integral_bound`.

Timings (`lake build` of a one-example file, including ≈4 s import; before = `a17e605`):

| Goal | Before | After |
|---|---|---|
| `∫₁² 1/x ∈ [0.6931, 0.6932]` | 170 s | 6.0 s |
| `∫₀¹ sin x ∈ [0.4596, 0.4598]` | 8.1 s | 5.5 s |
| `∫₀¹ 1/(1+x²) ∈ [0.7853, 0.7854]` | > 600 s (timeout) | 12.5 s |
| `∫₁² sin x / x ∈ [0.6593, 0.6594]` | > 400 s (timeout) | 33.6 s |
| `∫₀¹ sin(10x) ∈ [0.1839, 0.1840]` | not measured | 83 s |
| `∫₀³ sin(x²) ∈ [0.7735, 0.7736]` | — | 60 s |

The remaining cost is `KI.sin`/`KI.cos` in the kernel (≈1 s per call: four rational Taylor
evaluations per interval), so trigonometric integrands needing many cells stay slow.

Polynomial sign goals are handled by the `interval` tactic, which reifies polynomials.

### Examples (kernel-checked with `decide +kernel`, standard axioms only)

- `Examples/MatrixPD.lean`:
  - `hilbert3_eigen_gt`: every eigenvalue of H₃ is `> 0.0026`.
  - `hilbert10_posDef`: H₁₀ is `PosDef` (kernel path; condition number ≈ 1.6e13).
  - `hilbert8_eigen_gt`: every eigenvalue of H₈ is `> 10⁻¹⁰`.
- `Examples/PolyQuad.lean`:
  - `taylor_exp_pos'` (`interval` tactic).
  - `gauss_integral_bounds_kq`: `0.7468 ≤ ∫₀¹ e^{-x²} ≤ 0.7469` (kernel Taylor quadrature).
- `Examples/Bernstein.lean`: `taylor_exp_pos_bern`, and `bilinear_pos` (2D, `[0,1]²`).
- `Examples/Quad2.lean`: `xy_rect_bounds`: `1/8 ≤ ∫_{[0,1]²} xy ≤ 1/2`, via Fubini.
- `Examples/IntegralTactic.lean`: `gauss_lower`, `gauss_icc`, `inv_icc` (`∫₁² 1/x`), `sin_icc`,
  `atan_icc`.

**Optional slow examples (not built by default).** The first-round Float-spec examples live in the
separate library `RealFPMathlibSlow` (`RealFPMathlib/RealFPMathlibSlow/`), which is not a default
Lake target and is not imported by `RealFPMathlib` or `RealFPMathlibAxioms.lean`:
- `RealFPMathlibSlow/PolyQuad.lean`: `taylor_exp_pos` (`checkGt`, Float spec) and
  `gauss_integral_bounds`: `763/1024 ≤ ∫₀¹ e^{-x²} ≤ 383/512` (`integrateE1`, Float spec).
- `RealFPMathlibSlow/MatrixPD.lean`: `hilbert_posDef`: H₆ is `PosDef` (`isPD`, Float spec).
- `RealFPMathlibSlow/IntegralTactic.lean`: `sinc_icc` (`∫₁² sin x/x`), `sin10_icc`, `sinsq_icc`
  (`integral_bound`, 30–90 s each).

Build and check them with (from `RealFPMathlib/`, ≈65 s and ≈7.7 GB peak on an 8-core box):

```
lake build RealFPMathlibSlow
../scripts/check_axioms.sh RealFPMathlib RealFPMathlibSlowAxioms.lean
```

Moving them out cut the default `Examples` files: `PolyQuad.lean` 77.7 s / 8.1 GB → 7.3 s / 4.0 GB
and `MatrixPD.lean` 31.6 s / 5.5 GB → 15.1 s / 4.2 GB (single `lean` process, wall / peak RSS).

For larger instances, the same checks can run compiled through `native_decide`. That adds the
`native_decide` trust assumption.

**Tests** (`interval64_tests`):
- `pdMargins` C vs Lean spec, bit-exact, on 120 random/special matrices.
- PD decisions on Hilbert 1–12, indefinite and singular matrices, λ_min, and Loewner.
- Kernel path: `pdCheckL` / `pdCheckK` agree with `isPD` on Hilbert 1–13. Taylor quadrature
  enclosures for K = 2–8 are checked, along with rejected certificates (odd K, broken chains).
- Polynomial ops, range enclosures, and Bernstein (1D/2D) vs exact rationals.
- 1D and 2D quadrature enclosures vs known values.

## Interval128: double-double intervals (`Interval128/`, `RealFPMathlib/I128*.lean`)

The tactics use it through `(precision := 128)`; see
[Precision 128 in `interval`](#precision-128-in-interval-interval128dyadiclean-realfpmathlibi128dyadiclean).

`Interval128` has endpoints that are double-doubles: `[lh + ll, uh + ul]`,
about 106 bits (relative width ≈ 2^-104 on point inputs). It uses the same
architecture as Interval64:

* **The spec is the definition.** The spec is `Interval128/DD.lean` (pair
  kernels) plus `Interval128/Interval.lean` (interval ops and conversions),
  built from core RN `Float` ops and Interval64's directed ops. Both have
  logical models.
* **One C kernel per op.** Each op is attached by `@[implemented_by]`; the
  kernels are in `c/interval128.h` and `c/interval128.c` and are
  bit-identical to the spec.
* **Directed FMA.** `fmaDown` / `fmaUp` are new (`Interval128/Fma.lean`).
  The spec feeds the exact product into Interval64's `addU`. At runtime the
  x86 path uses AVX-512 embedded rounding, and the arm64 path uses RN `fma`
  (exact in a guarded range) with an `fesetround` fallback.

**Soundness method.** Approximations (`s = a+b`, `q₁ = a/b`, `√a`, ...)
are plain RN results and are never trusted. Only the error terms use
directed ops. Each error term is a one-sided bound of an exact real
identity that holds for *any* value of the approximations. For example:

    ah + bh − s = (ah − (s − bb)) + (bh − bb)
    A/B = q₁ + q₂ + (A − (q₁+q₂)B)/B
    √A = s + (A − s²)/(√A + s)

So the proofs need only "directed rounding is one-sided". Nothing about
round-to-nearest is used. In the normal range the error terms are exact
(TwoSum, FastTwoSum, FMA TwoProd), so directed rounding loses no accuracy.

**Policy, per endpoint.** The double-double result is used when the
computed endpoint words are finite (and, for mul/div/sqrt, all input words
are finite). Otherwise that endpoint comes from the Interval64 op on the
outward hull `toInterval64`. There are no validity checks: a reversed
interval is the empty set.

* `div`: if the divisor contains 0, the result is `whole`.
* `sqrt`: an upper endpoint below 0 gives `invalid`; a negative lower
  endpoint is clipped to 0.

**Operations and conversions.**

* Ops: `+ - * /`, `sqrt`, `neg`, `width`.
* Conversions: `point`, `ofInterval64`, `toInterval64` (outward), and
  `ofRat`, `ofNat`, `ofInt`, `ofScientific`, each tight to about 2^-106.

**Tests.** Run `lake exe interval128_tests`. It checks:

* the C runtime against the Lean spec, bit-exact: 400k fma cases, plus
  20k random cases per op in four exponent regimes, specials, and reversed
  intervals;
* enclosure of exact rational points, about 160k per op;
* a tightness report.

On AVX-512 and on the RN+err backend: 0 mismatches and 0 enclosure
failures. Tightness, in units of 2^-106 relative to the result magnitude:

| op | max | mean |
|---|---|---|
| add | 3.0 | 0.68 |
| mul | 9.2 | 2.2 |
| div | 7.2 | 1.6 |
| sqrt | 7.9 | 1.5 |

**Proofs** (Mathlib layer, `RealFP.I128`, no `sorry`, only `propext`,
`Classical.choice`, `Quot.sound`).

* **Semantics.** The lower endpoint `(h, l)` admits `x` when both words are
  finite with `h + l ≤ x`, or when `l` is a zero and `h ≤ x` in `EReal`.
  The upper endpoint is symmetric. This set is `toSet`.
* **`I128Prims`.** "A finite directed result implies finite operands and a
  one-sided bound" for `add`/`sub`/`mul`/`fma`/`div`/`sqrt` Down/Up. Also
  directed-FMA enclosure at the bit level, exact negation, and
  comparisons.
* **`I128DD`.** Every pair kernel is one-sided: `addLo_le`/`addHi_ge`,
  `mulLo_le`/`mulHi_ge`, `divLo_le`/`divHi_ge` (B > 0), `sqrtLo_le`/
  `sqrtHi_ge` (A ≥ 0), `minLo_le`/`maxHi_ge`, `quotLo_le`/`quotHi_ge`,
  and the exact sign tests.
* **`I128Mem`.** The interval theorems:
  * `mem_add`, `mem_sub`, `mem_mul`, `mem_neg`;
  * `mem_div` (`y ≠ 0`), `mem_sqrt` (`0 ≤ x`);
  * `mem_point`, `mem_ofRat`, `mem_ofNat`, `mem_ofInt`, `mem_ofInterval64`,
    `mem_toInterval64`, `mem_whole`.

  Each is of the form `x ∈ toSet X → y ∈ toSet Y → x ⋆ y ∈ toSet (X ⋆ Y)`.

As with Interval64, the compiled C kernels are a trust assumption. They are
checked differentially against the spec that the theorems are about.

**Benchmark.** Run `bench/i128/run.sh`. It reports C-level throughput in
ns/op for independent random intervals. The machine is an x86 Xeon with
AVX-512. Arb is FLINT 3.1.3.

| op | Interval64 | Interval128 | Arb p=106 | Arb p=128 |
|---|---|---|---|---|
| add | 0.85 | 9.3 | 42 | 38 |
| mul | 5.2 | 12.6 | 21 | 21 |
| div | 13.1 | 29.5 | 61 | 62 |
| sqrt | 3.1 | 12.6 | 95 | 96 |
