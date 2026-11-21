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

`lake build -R -Kbackend=rnerr` builds the arm64 backend on x86_64, so the
Lean-side tests (`lake exe interval64_tests`, C runtime vs Lean spec) can run
against it; `lake build -R` switches back.

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

## Transcendentals (`exp`, `log`)

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
`Float.exp` ≈ 11.6 ns). `sin`/`cos` are vendored and exported
(`iv64_dir_sin_*`, `iv64_dir_cos_*`) but have no Lean spec yet.

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

## Interval policy

- NaN endpoint → invalid `[NaN, NaN]`.
- Division by an interval containing `0` → whole line `[-∞, +∞]`.
- `sqrt` of `hi < 0` → invalid; `lo < 0 ≤ hi` clips to `[+0, hi]`; `sqrt(-0) = -0`.

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
  infinite endpoints allowed); `mul_mem_toSet`, `div_mem_toSet` (`y ≠ 0`),
  finite endpoints; `sqrt_mem_toSet` (`Real.sqrt x ∈ (sqrt X).toSet` for `0 ≤ x`).
* `Tight`: `addDown_isRoundDownR` … `divUp_isRoundUpR`, `sqrtDown_isRoundDownR`,
  `sqrtUp_isRoundUpR`: the directed result is the greatest representable real
  `≤` (least `≥`) the exact real result, so `IsRoundDownR.no_between`: no
  representable real lies strictly between. Interval level: `add/sub/mul/div_iv_optimalR`
  (`div` needs `containsZero Y = false`), `add/sub_iv_tightR`, `sqrt_iv_tightR`,
  `sqrt_iv_optimalR`; `ofRatDown_isRoundDownR`, `mem_toSet_ofRatInterval`.
* `Demo` (not imported by `RealFPMathlib`): `sq_add_le : ∀ x ∈ Set.Icc (1/10 : ℝ) (3/10), x * x + x ≤ 13/32`,
  `sqrt_two_bounds : 1.41421356 < √2 < 1.41421357`, `sqrt_le_on : ∀ x ∈ [2,3], √x ≤ 111/64`.

**Trust.** Everything in `Basic`/`Mem`/`Tight` uses only `propext`,
`Classical.choice`, `Quot.sound`. Only the `Demo` theorems use `native_decide`
(one generated axiom each, and the compiled C kernels are trusted).
`scripts/check_axioms.sh` enforces this. Mathlib itself does not accept
`native_decide`, so proofs that use it are fine in your projects but cannot be
upstreamed; facts small enough for `decide +kernel` avoid the extra axiom.

### Worked examples (`RealFPMathlib/RealFPMathlib/Examples/`)

* `Cubic.lean` — `cubic_bound : ∀ x : ℝ, 0 ≤ x → 6x - x³ ≤ (6√2 - √2³) + 0.001`.
  `[0, 5/2]` is split into 20480 boxes of width `2^-13`; a Bool checker
  (`allOK`, evaluated by `native_decide` with the C kernels, ~0.4 s) bounds
  `X * (6 - X*X)` on each box, and `allOK_sound` turns that into the real bound.
  `x ≥ 5/2` is algebra. (Width `2^-12` is too coarse for the 0.001 slack.)
* `Jacobian.lean` — `F(x,y,z) = ((1+xy)³z + y²(1+xy)(4+3xy), y + 3x(1+xy)²z + 3xy²(4+3xy), 2x - 3x²y - x³z)`.
  Mathlib `HasDerivAt` partials, `jac_det : det = -2` everywhere, `F_not_injective`,
  `F_eq_iff` (all solutions of `F = (a,0,0)`, `a ≠ 0`), `solutions_quarter` /
  `ncard_solutions_quarter` (exactly the 3 given points), `solutions_026` /
  `ncard_solutions_026` (exactly 3 solutions: `(0,0,-0.26)`, `(±s, ∓3/(2s), 169/25)`,
  `s = √(25/26)`), with Interval64 enclosures `s_bounds`, `y_bounds`.
  The solution count is pure algebra (no `native_decide`); Interval64 is used
  only for the numeric enclosures.
