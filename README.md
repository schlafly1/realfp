# Interval64

A small Lean 4 (v4.36.0) prototype for **binary64 interval arithmetic** with
**hardware directed rounding**. Transcendentals are out of scope.

The core library has **no Mathlib / FloatLib dependency**. Directed operations
are `@[extern]` C kernels; they do **not** call Lean’s `Float.add` (whose
logical model is round-to-nearest-even).

## Kernels

- **AVX-512 embedded rounding** (`_mm_add_round_sd` and friends, with
  `_MM_FROUND_TO_NEG_INF` / `_MM_FROUND_TO_POS_INF` and `_MM_FROUND_NO_EXC`).
  These do not change MXCSR.
- **fesetround fallback** (save / compute / restore), compiled with
  `-frounding-math -ffp-contract=off -fno-math-errno`.
- **RN + 1-ulp widening**, for speed comparison.
- A **batched `FE_UPWARD`** interval kernel using `-up(-x)` for lower bounds.

The C file is compiled with **gcc** (`cc`). The Lean 4.36 bundled clang on
this box is missing `immintrin.h`.

## Build and run

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /workspace/interval64_avx512
lake build
lake exe interval64_tests
taskset -c 0 nice -n 19 lake exe interval64_bench
```

## Interval policy

- NaN endpoint → invalid `[NaN, NaN]`.
- Division by an interval containing `0` → whole line `[-∞, +∞]`.
- `sqrt` of `hi < 0` → invalid; `lo < 0 ≤ hi` clips to `[+0, hi]`; `sqrt(-0) = -0`.

## Trust

Compiled AVX-512 / `fesetround` / libm `sqrt` under the flags above, plus the
CPU’s IEEE directed rounding. Not kernel-checked. Official tests compare the
two hardware paths bit-for-bit (all NaNs equal, signed zeros distinguished).
