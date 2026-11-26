# GPU experiment: Interval64-style interval arithmetic on an NVIDIA GPU

A deliberately GPU-friendly workload: prove a 2-D global bound by brute force on a
uniform grid of up to 2^26 boxes, with the same branch-free interval code for every
box. The GPU, one CPU core and all CPU cores run literally the same expression
source (`ivexpr.h`), and the GPU results are checked bit-for-bit against the CPU.

This directory is standalone. It is **not** part of `lake build` and does not
change any Lean or C code of the library. It only reuses `../c/iv64_rnerr.h`.

## Problem

| | function | domain | claim | true extremum |
|---|---|---|---|---|
| f0 | Motzkin x⁴y² + x²y⁴ − 3x²y² + 1, evaluated as x²y²(x²+y²−3)+1 | [−2,2]² | f0 ≥ −1/64 | 0 at \|x\|=\|y\|=1 |
| f1 | (x+y) / √(2(x²+y²+1)) | [−4,4]² | f1 ≤ 0.99 | 8/√66 = 0.98473… |

Each box is evaluated with outward-rounded binary64 interval operations: `+ − ×`
(4-corner min/max, branch-free), `x²` (sign-aware), `/` (4-corner, denominator
not containing 0) and `√`. A grid of 2^k × 2^k boxes is reduced to (min lo, max hi,
number of boxes that fail the claim). The claim is proved for a grid when 0 boxes fail.
Without derivative information, f0 needs 2^22 boxes and f1 needs 2^18.

Backends:

* **GPU fp64:** CUDA per-instruction rounding intrinsics `__dadd_rd/_ru`, `__dsub_*`,
  `__dmul_*`, `__ddiv_*`, `__dsqrt_*` (no rounding-mode state). One thread per box,
  grid-stride loop, warp-shuffle and block reduction. Built with `-fmad=false`.
* **CPU:** the repo's portable kernels `iv64r_*` (round-to-nearest + exact error term,
  the Interval64 runtime backend on aarch64), on 1 thread and on all cores with OpenMP.
* **Independent reference:** the same expressions with `fesetround` around every
  single operation (slow, used on samples).
* **GPU fp32 (contrast only, not Interval64):** the same code with `__fadd_rd`, etc.,
  on binary32 endpoints. It is checked against a CPU fp32 `fesetround` reference.

## Results: NVIDIA DGX Spark (GB10), measured 2026-11-21

NVIDIA GB10 (48 SMs, compute capability 12.1, CUDA 13.0, driver 580), CPU
10× Cortex-X925 + 10× Cortex-A725 (20 threads), 121 GB unified LPDDR5X, gcc 13.3.
The GPU was idle (desktop only) during the run. Full output is in
[`results_gb10.txt`](results_gb10.txt).

The table columns are:

* **GPU kernel:** device time from CUDA events.
* **GPU call:** wall time of the whole host call, including the launch, the copy-back
  of the per-block partial results and the host reduction.

All times are medians.

### Correctness: all bit-identical

* **Full grids:** f0 and f1 at 2^24 boxes each. GPU and CPU (`iv64r`) agree on every
  lo and hi endpoint of all 16,777,216 boxes, with 0 mismatches, and the reduced
  results are identical.
* **Random boxes:** 4,194,304 random boxes per function, of all widths from 2^-40·R
  to R, unaligned and zero-crossing, with 0 mismatches.
* **`fesetround` reference:** GPU vs the per-operation `fesetround` reference on 262,144
  sampled boxes per test, with 0 mismatches. That makes three independent
  implementations of directed rounding that agree.
* **fp32:** the fp32 GPU code matches the CPU fp32 `fesetround` reference on 2^20
  boxes per function, with 0 mismatches.
* **Every timing run:** the GPU's reduced result (min lo, max hi and failing count)
  equals the 1-thread and 20-thread CPU results bit for bit.

### f0 (Motzkin, add/sub/mul only)

| boxes | failing | GPU kernel | GPU call | CPU 1 thread | CPU 20 threads | GPU vs 1 thread | GPU vs 20 threads | GPU fp32 kernel |
|---|---|---|---|---|---|---|---|---|
| 2^10 | 120 | 0.009 ms | 0.028 ms | 0.040 ms | 0.008 ms | 1.4× | 0.29× | 0.007 ms |
| 2^12 | 224 | 0.010 ms | 0.028 ms | 0.155 ms | 0.020 ms | 5.6× | 0.73× | 0.006 ms |
| 2^14 | 408 | 0.015 ms | 0.034 ms | 0.608 ms | 0.061 ms | 18× | 1.8× | 0.007 ms |
| 2^16 | 696 | 0.036 ms | 0.056 ms | 2.41 ms | 0.238 ms | 43× | 4.3× | 0.014 ms |
| 2^18 | 928 | 0.113 ms | 0.133 ms | 9.58 ms | 1.58 ms | 72× | 12× | 0.032 ms |
| 2^20 | 20 | 0.371 ms | 0.390 ms | 38.2 ms | 4.20 ms | 98× | 11× | 0.068 ms |
| 2^22 | **0** | 1.40 ms | 1.42 ms | 153 ms | 14.5 ms | 108× | 10× | 0.214 ms |
| 2^24 | 0 | 5.52 ms | 5.54 ms | 611 ms | 51.6 ms | 110× | 9.3× | 0.793 ms |
| 2^26 | 0 | 22.0 ms | 22.0 ms | 2440 ms | 182 ms | 111× | 8.3× | 3.11 ms |

Peak throughput is 3.05 G boxes/s on the GPU, 27.5 M/s on 1 CPU thread and
368 M/s on 20 CPU threads.

### f1 (rational with √ and ÷)

| boxes | failing | GPU kernel | GPU call | CPU 1 thread | CPU 20 threads | GPU vs 1 thread | GPU vs 20 threads | GPU fp32 kernel |
|---|---|---|---|---|---|---|---|---|
| 2^10 | 126 | 0.017 ms | 0.036 ms | 0.048 ms | 0.008 ms | 1.3× | 0.23× | 0.007 ms |
| 2^12 | 260 | 0.017 ms | 0.036 ms | 0.189 ms | 0.023 ms | 5.3× | 0.65× | 0.007 ms |
| 2^14 | 348 | 0.029 ms | 0.048 ms | 0.752 ms | 0.072 ms | 16× | 1.5× | 0.009 ms |
| 2^16 | 159 | 0.076 ms | 0.096 ms | 3.00 ms | 0.270 ms | 31× | 2.8× | 0.013 ms |
| 2^18 | **0** | 0.256 ms | 0.276 ms | 12.0 ms | 1.73 ms | 43× | 6.3× | 0.034 ms |
| 2^20 | 0 | 0.918 ms | 0.939 ms | 47.9 ms | 4.90 ms | 51× | 5.2× | 0.072 ms |
| 2^22 | 0 | 3.57 ms | 3.59 ms | 191 ms | 17.3 ms | 53× | 4.8× | 0.226 ms |
| 2^24 | 0 | 14.2 ms | 14.2 ms | 765 ms | 62.3 ms | 54× | 4.4× | 0.848 ms |
| 2^26 | 0 | 56.7 ms | 56.7 ms | 3060 ms | 223 ms | 54× | 3.9× | 3.31 ms |

Peak throughput is 1.18 G boxes/s on the GPU, 21.9 M/s on 1 CPU thread and
301 M/s on 20 CPU threads.

### Arbitrary box list (f1; host → device 32 B/box, kernel, device → host 16 B/box)

This is the shape a tactic would use, where it sends a list of boxes and gets their
enclosures back.

| boxes | GPU call | GPU kernel | CPU 1 thread | CPU 20 threads | GPU vs 1 thread | GPU vs 20 threads |
|---|---|---|---|---|---|---|
| 1 | 23.4 µs | 9.5 µs | 0.27 µs | 2.5 µs | 0.01× | 0.11× |
| 2^8 | 23.7 µs | 15 µs | 11.7 µs | 3.2 µs | 0.49× | 0.14× |
| 2^10 | 23.5 µs | 12 µs | 46 µs | 6.1 µs | 2.0× | 0.26× |
| 2^12 | 25.5 µs | 14 µs | 188 µs | 18 µs | 7.4× | 0.72× |
| 2^14 | 52 µs | 27 µs | 817 µs | 69 µs | 16× | 1.3× |
| 2^16 | 126 µs | 64 µs | 3.3 ms | 287 µs | 27× | 2.3× |
| 2^18 | 437 µs | 217 µs | 13.5 ms | 1.6 ms | 31× | 3.7× |
| 2^20 | 1.68 ms | 0.84 ms | 54 ms | 5.1 ms | 32× | 3.1× |
| 2^24 | 27.5 ms | 13.2 ms | 863 ms | 68.5 ms | 31× | 2.5× |

### Lean FFI (`lean/IvGpu.lean`, Lean 4.36.0)

`@[extern]` functions call `libivgpu.so` from a compiled Lean program:

* **Grid call:** `gpuGrid 0 11` (f0, 2^22 boxes) returns min lo = −0.007835 and
  0 failing boxes, in 1.42 ms per Lean call. That is the same time as from C.
* **One box:** `gpuList` costs 22.7 µs per Lean call, which is the CUDA launch and
  synchronisation cost, not Lean.
* **2^20 boxes:** `gpuList` takes 10.1 ms per call (104 M boxes/s). The C benchmark
  takes 1.7 ms, because a Lean `FloatArray` is ordinary pageable memory and the
  copies are slower than from pinned buffers.

## What this shows

* **Break-even:** on one box the GPU is about 100× *slower* than a CPU core, because
  every call costs at least 20–25 µs. It overtakes one CPU core at about 1,000 boxes
  per call and all 20 cores at about 10^4–10^5 boxes. With millions of boxes, the GPU
  is 110× (f0) or 54× (f1) faster than one core and 4–10× faster than all 20 cores.
* **fp64 is the bottleneck on GB10.** The identical fp32 code runs 7× (f0) to 17× (f1)
  faster. fp64 directed division and square root are especially expensive, which
  is why f1 gains less than f0.
* **Directed rounding is exact on the GPU.** CUDA's `_rd`/`_ru` intrinsics give
  bit-identical results to the Interval64 CPU kernels and to `fesetround`, so GPU
  output can be cross-checked or replayed exactly.
* **Trust:** a GPU-only result is trusted the same way `native_decide` is, and
  additionally trusts nvcc, the driver and the GPU. These kernels are not proved
  equal to the Lean definitions. In the `interval` tactic, the GPU would only make the
  native box search faster, and the kernel would still check the result.
* **For comparison:** a derivative-aware tactic proves these bounds with far fewer
  boxes. This is a brute-force demonstration chosen to suit the GPU.

## Rerun

On a machine with CUDA (≥ 12) and gcc with OpenMP, from the repository root:

```sh
gpu/build.sh                 # -> gpu/build/libivgpu.so, gpu/build/bench (ARCH=sm_121 etc. to override native)
gpu/build/bench              # full run (2^10..2^26 boxes, ~1 min); `gpu/build/bench quick` for 2^10..2^22
gpu/lean/build.sh            # optional: Lean FFI demo (needs lean/leanc on PATH, toolchain v4.36.0)
gpu/build/ivgpu_lean
```

`bench` exits nonzero if any GPU result differs from the CPU.

## Caveats

* Only GB10 was measured. Thor and agx2 were not reachable over ssh from the
  benchmark host, and gx10 resolved to an unreachable address.
* CPU 1-thread numbers depend on whether the OS ran the thread on an X925 or an A725
  core (no pinning). The 20-thread runs use both core types, and the ARM kernels
  were compiled with gcc -O2 without SIMD, the same as the library.
* The interval code assumes finite endpoints and a denominator that does not
  contain 0, which is true for these problems. Unlike Interval64, it does not handle
  ±∞/NaN endpoints.
* GB10 memory is unified. Copies between host and device still cost about half of
  the list-mode call. Zero-copy mapped memory could remove that, but it is not
  measured here.

## Follow-up: adaptive many-box searches

See [`manybox/`](manybox/README.md): level-synchronous bisection (same tree on CPU and GPU) on
two problems needing 10^3-10^7 boxes, with the GPU tree checked by Lean as a certificate.
