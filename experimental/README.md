# experimental/

Material from the prototype and from benchmarking. None of it is part of the
library: nothing here is imported by `Interval64`, `Interval128` or
`RealFPMathlib`, and none of it is needed to use realfp. It is kept for
reference and for reproducing measurements quoted in the docs.

| Path | What it is |
|---|---|
| `Interval64Bench.lean` | Micro-benchmarks of the C kernels against the Lean spec (`lake exe interval64_bench`). |
| `Interval64Native.lean` | The original `native_decide` demo (`lake exe interval64_native`). |
| `bench/i128/` | C-level benchmark of the Interval128 kernels against Interval64 and (if installed) Arb: `experimental/bench/i128/run.sh`. |
| `bench/leancert/` | The goal statements of the LeanCert comparison, each closed by `realfp`, and a rerun script (`run.sh`, needs a built `RealFPMathlib`). Results are summarised in [docs/COMPARISONS.md](../docs/COMPARISONS.md). |
| `gpu/` | CUDA prototype of interval evaluation on the GPU, with a Lean FFI demo; built by its own `build.sh`, not by Lake. See `gpu/README.md`. |

The two Lake executables are still declared in the top-level `lakefile.lean`
(with `srcDir := "experimental"`), but they are not default targets and CI does
not build them.
