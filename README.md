# Interval64

A small Lean 4 (v4.36.0) library for **binary64 interval arithmetic** with
**hardware directed rounding**, including correctly rounded directed `exp`
and `log` ([transcendentals](#transcendentals-exp-log)). The core has **no
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
cd /workspace/interval64_avx512
lake build
lake exe interval64_tests
lake exe interval64_native
taskset -c 0 nice -n 19 lake exe interval64_bench
```

A tiny downstream project lives at `/workspace/interval64_consumer`
(`require interval64 from "../interval64_avx512"`).

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

`lake -R -Kbackend=rnerr build interval64_tests` builds the arm64 backend on
x86_64, so the Lean-side tests (`.lake/build/bin/interval64_tests`, C runtime vs
Lean spec) can run against it; `lake -R build interval64_tests` switches back.
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

Proofs (`RealFPMathlib/Ops.lean`; none needs finite endpoints): `mem_neg`, `mem_abs`,
`mem_square` (`x ^ 2 ∈ square X`), `mem_pown` (`x ^ n ∈ pown X n`), `mem_min`,
`mem_max`, `mem_inv` (`x⁻¹ ∈ inv X`, with Lean's `0⁻¹ = 0`), `toSet_intersect`
(`(intersect X Y).toSet = X.toSet ∩ Y.toSet`, exact), `mem_intersect`,
`union_subset_toSet_hull`, `toSet_subset_of_subset`, `mem_of_contains`,
`mid_spec` (`lo ≤ mid X ≤ hi`, not NaN, for nonempty `X`), `contains_mid`,
`bisect_cover`, `bisect_fst_subset`, `bisect_snd_subset` (for nonempty `X`),
`abs_le_mag`, `mig_le_abs`, `sub_le_width` (`x - y ≤ width X` for `x, y ∈ X`), and
`width_ge` (`hi - lo ≤ width X` for finite endpoints). Example
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

A general theorem `round-down(a+b) ≤ a+b ≤ round-up(a+b)` for arbitrary
finite inputs is **not** proved in this revision (no `sorry` is left in
the tree). The compiled C path is a trust assumption, checked
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
lake build                # core (C kernels too) + the Mathlib layer
lake lean Examples.lean   # runnable examples (#eval uses the C kernels)
scripts/check_axioms.sh   # axiom report for every theorem of the layer
```

Use it from your own Mathlib project (same Lean and Mathlib versions) with
`require realfp_mathlib from "path/to/realfp/RealFPMathlib"` and
`import RealFPMathlib`. (A git requirement with subdirectory,
`... from git "https://github.com/schlafly1/realfp" @ "main" / "RealFPMathlib"`,
should also work but has not been tested.)

**What it provides** (namespace `RealFP`; files in `RealFPMathlib/RealFPMathlib/`):

* `Basic`: `Float.toReal? : Float → Option ℝ` (exact value, `none` for ±∞/NaN),
  `Float.toReal` (total, junk `0`), `Interval64.toSet : Interval64 → Set ℝ`
  (extended-real reading: a `-∞`/`+∞` end gives an unbounded set, NaN gives `∅`;
  `toSet_eq_Icc` for finite endpoints), `RepresentableR`, `IsRoundDownR`,
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

- `a`, `b`, `c` must be rational numerals, with `a` and `b` exact floats. `f` may use the
  `interval` tactic's operations.
- It searches natively for `K ∈ {4,6,8}` and `N ≤ 256` uniform cells, then makes one
  `decide +kernel` call on `quadBound`.
- `example : (∫ x in (0:ℝ)..1, Real.exp (-x^2)) ∈ Set.Icc (0.7468 : ℝ) 0.7469 := by integral_bound`
  takes 15.8 s including the import.
- Integrands whose derivative expressions grow quickly (e.g. `1/x`) are slower: about 50 s.

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
- `Examples/IntegralTactic.lean`: `gauss_lower`, `gauss_icc`.

**Optional slow examples (not built by default).** The first-round Float-spec examples live in the
separate library `RealFPMathlibSlow` (`RealFPMathlib/RealFPMathlibSlow/`), which is not a default
Lake target and is not imported by `RealFPMathlib` or `RealFPMathlibAxioms.lean`:
- `RealFPMathlibSlow/PolyQuad.lean`: `taylor_exp_pos` (`checkGt`, Float spec) and
  `gauss_integral_bounds`: `763/1024 ≤ ∫₀¹ e^{-x²} ≤ 383/512` (`integrateE1`, Float spec).
- `RealFPMathlibSlow/MatrixPD.lean`: `hilbert_posDef`: H₆ is `PosDef` (`isPD`, Float spec).

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
