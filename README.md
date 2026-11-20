# Interval64

A small Lean 4 (v4.36.0) library for **binary64 interval arithmetic** with
**hardware directed rounding**. Transcendentals are out of scope. The core
has **no Mathlib / FloatLib dependency**.

Each directed scalar operation (`+`, `-`, `*`, `/`, `sqrt`, down and up) has:

- a **computable Lean specification** (`Interval64.Spec` / `addDownSpec`, …)
  that the kernel can unfold — a software IEEE 754 binary64 implementation
  built on Lean 4.36’s `Float.Model.UnpackedFloat`, with round-toward-±∞
  (including IEEE 754-2019 §6.3 signed zeros and overflow to ±∞ vs ±MaxFinite);
- an **AVX-512 C runtime** (`_mm_add_round_sd` and friends) attached with
  `@[implemented_by]`. Compiled code, `#eval`, and `native_decide` use the
  C kernel. The kernel itself sees the Lean body.

Interval operations (`Interval64.add`, `mul`, …) are defined in Lean on top
of those scalars, so they inherit both the spec and the fast path.

## Kernels

- **AVX-512 embedded rounding** (does not change MXCSR).
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
