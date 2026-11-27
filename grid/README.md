# realfp-grid: the search tool for `interval_grid`

This is an untrusted, standalone program. It finds bisection certificates for
`RealFP.Grid` and explores minima and maxima. Its output is only a hint; Lean re-checks
everything. See [docs/GPU.md](../docs/GPU.md) for when to use it, the trust base, and the
workflow.

```
grid/build.sh                    # CUDA if nvcc is on PATH, else CPU only → grid/build/realfp-grid
realfp-grid info
realfp-grid prove PROBLEM -o CERT [--engine auto|cpu|gpu|gpu32|gpu64] [--depth N]
                  [--max-boxes N] [--cap N] [--threads N] [--split K] [-v]
realfp-grid split PROBLEM CERT K -o SPLITCERT
realfp-grid minmax PROBLEM [--max] [--engine E] [--depth N] [--cap N] [--tol X] [--time S]
grid/showcase.sh NAME MODULE K [K1] [ENGINE]   # big certificates → Lean theorem (docs/GPU.md)
```

* **Problem files:** written by `interval_grid (export := "P.problem")` or by
  `#grid_export "P.problem" : statement`. The format is text: dimension, box (binary64
  bits), goal and constant, constants, and the tape. It is documented in
  `src/problem.cpp`.
* **Engines:**
  * `cpu`: binary64, all cores, the same arithmetic as the checker.
  * `gpu64`: CUDA binary64 with directed rounding (`__dadd_rd`, …).
  * `gpu32`: CUDA binary32, outward-rounded. It is faster, but its enclosures are wider, so
    a certificate may have more boxes. The certificate still has to pass the binary64
    checker.

  On the GPU, the tape is compiled with NVRTC into straight-line code. `RFG_NOJIT=1` uses
  the interpreter instead.
* **Identical certificates:** every engine walks the same tree as the checker (midpoint
  `lo·0.5 + hi·0.5` in binary64, split variable `level mod d`). `cpu` and `gpu64` give
  bit-identical certificates, and so does `gpu32` on R8.
* **Memory:** a level that does not fit in the frontier capacity (`--cap`, chosen from the
  GPU memory by default) is finished in chunks of its remaining boxes, without redoing work.
* **Sources:**
  * `src/ops.hpp`: the interval operations and tape evaluation (templated over policies);
  * `src/cpu.cpp`, `src/gpu.cu`, `src/gpu_pol.hpp`: the engines;
  * `src/main.cpp`: the drivers;
  * `gen_lean.py`: the Lean generator for split certificates.
