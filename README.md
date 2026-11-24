# realfp

[![CI](https://github.com/schlafly1/realfp/actions/workflows/ci.yml/badge.svg)](https://github.com/schlafly1/realfp/actions/workflows/ci.yml)

**realfp** is a Lean 4 library for proving facts about real numbers with interval
arithmetic. It uses hardware directed rounding (IEEE 754 binary64), so bounds
are both fast and rigorous. By default the tactics are checked by the Lean
kernel and depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

Typical uses are inequalities over a box, existence or uniqueness of roots,
integral bounds, positive definiteness, and minima or maxima. The core library
(`interval64`) has no Mathlib dependency. The Mathlib layer (`realfp_mathlib`)
supplies theorems about `ℝ` and the tactics.

## Install

realfp targets Lean `leanprover/lean4:v4.36.0` and Mathlib `v4.36.0`. Your
project must use the same toolchain; copy `RealFPMathlib/lean-toolchain` into
the project.

In a Mathlib project, add this to the lakefile, then run `lake update`,
`lake exe cache get`, and `lake build`:

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

With a local clone, use `require realfp_mathlib from "path/to/realfp/RealFPMathlib"`
instead. To build this repository itself:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build                          # core library, proofs, and tests
lake exe interval64_tests
cd RealFPMathlib && lake exe cache get && lake build
```

**C compiler.** The core compiles C kernels with `cc`.

- **x86-64.** Use gcc as `cc` (Lean 4.36's bundled clang is missing `immintrin.h`).
  The default backend uses AVX-512 embedded rounding and needs a CPU with
  AVX-512F. On a machine without AVX-512, or to force the portable backend,
  build with `lake -Kbackend=rnerr` or set `IV64_BACKEND=rnerr`. The
  environment variable is required when another Lake package (such as
  `RealFPMathlib`) is the Lake root, because Lake does not forward `-K`
  options to required packages.
- **arm64.** The portable round-to-nearest + exact-error-term backend is
  selected automatically; any C compiler works.

Both backends produce bit-identical results; the theorems do not depend on
which one you use. GitHub Actions CI always builds the portable backend.

Run Lean through the editor, `lake build`, or `lake lean File.lean`. Plain
`lean` / `lake env lean` do not load the C kernels unless you pass
`--load-dynlib` and `--plugin`; the tactics print those flags if they are
missing. Do not set `precompileModules` in your own Mathlib project: the
core package already precompiles its modules.

## Usage

```lean
import RealFPMathlib

-- `realfp` looks at the goal and picks a backend. The default
-- `trust := kernel` is checked by the Lean kernel (standard axioms only).
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp

example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp

-- Faster on large certificates, but the proof then trusts the Lean
-- compiler and the C kernels:
--   example : … := by realfp (trust := native)
```

`import RealFPMathlib` brings in the theorems and the tactics. For exploration
you can also `#eval` interval expressions such as `Interval64.sqrt 2`.

## Documentation

- [Tutorial](docs/TUTORIAL.md) — hands-on guide; every snippet is compiled
- [Reference](docs/REFERENCE.md) — operations, theorems, kernels, and tactics
- [Comparisons](docs/COMPARISONS.md) — FloatLib, LeanCert, and two research showcases
- [Limitations](docs/LIMITATIONS.md) — known gaps
- [Philosophy](docs/PHILOSOPHY.md) — design rationale

An index of these files is in [docs/](docs/README.md).
