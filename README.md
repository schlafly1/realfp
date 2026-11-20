# Interval64

A small Lean 4 (v4.36.0) library for **binary64 interval arithmetic** with
**hardware directed rounding**. Transcendentals are out of scope. The core
has **no Mathlib / FloatLib dependency**.

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
