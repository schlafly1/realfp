# Changelog

All notable changes to realfp are listed here. Versions follow
[Semantic Versioning](https://semver.org/); before 1.0 the API may still change
between minor versions.

## Unreleased

- **Opt-in GPU / many-box proofs**: [docs/GPU.md](docs/GPU.md). Nothing is added to the default
  build, and the trust of existing proofs is unchanged.
  - New Lean libraries `RealFPGridNative`, `RealFPGrid` and `RealFPGridExamples`, plus
    `RealFPGridShowcase`, which is built by script.
  - `interval_grid` tactic: plain bisection certificates, checked by a multithreaded C
    checker (`c/grid_tape.c`) under one `native_decide`, with a soundness proof over `ℝ`.
  - Options: certificate cache files; `(explore := true)` for the extremum and a point
    where it is attained; `(export := …)`; `(use := thm)`. Also `#grid_export`.
  - Standalone search tool `grid/` (`realfp-grid`): CUDA binary32/binary64 with run-time
    compiled tapes, or multithreaded CPU. Modes `prove`, `split` and `minmax`.
  - `grid/showcase.sh` + `grid/gen_lean.py` for certificates with 10⁸–10¹⁰ boxes: split
    certificates, parallel Lean checks, and a checked glue proof.
  - The experiment it grew from stays in `experimental/gpu/manybox/`.

## [0.1.1] — 2026-11-25

Lean `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0` (unchanged).

- Beginner guide [docs/GETTING_STARTED.md](docs/GETTING_STARTED.md): Windows 11
  (WSL), Linux and macOS from nothing installed to the examples and a first
  theorem; troubleshooting. A `.devcontainer/` for GitHub Codespaces.
- Build portability: the C compiler is `$CC`, else the first of `cc`, `gcc`,
  `clang` found, with a clear error if there is none (Lean's bundled clang has no
  C library headers). On x86-64 the AVX-512 backend is chosen only if the
  compiler reports AVX-512F for the host, otherwise the portable backend.
  The C runtime compiles with clang (no function pointers to macro intrinsics,
  no nested function), on Windows/mingw (`aligned_alloc` fallback) and on
  macOS (the binary128 self-test oracle is used only where such a type exists).

- New showcase `Examples/TouchingPoints.lean`: `(touch := auto)`, exact rational
  touching points, near touching at an irrational point, and the impossible case of exact
  irrational touching. Kernel-checked; about 17 s.
- `(touch := auto)`: touching points are located by multistart Newton on
  `∇f = 0` (interior, Hessian definite, value near the bound) and snapped to small
  rationals when the gradient vanishes exactly there. The tactic falls back to the
  ordinary search if none are found or the certificate fails.
- Touch leaves are now tangent-plane leaves (`TCert.tan`, `tanOK_sound`): the goal is
  checked on `f(p) + ∇f(p)·(x − p)` over the box, using the general expansion
  `RealFP.touch_expand_gen`. As a result:
  - touching points may be any rationals (`1/3`): `f` and `∇f` are evaluated exactly
    in `ℚ` for `+ − × ÷ ⁻¹ |·| ^n` expressions (`evalQ`, `evalQ_sound`);
  - near touching at irrational points works (`… + 1/10^13 > 0` at `(√2, 1/√3)`, where
    plain bisection fails);
  - strict bounds are accepted (`proveT_lt`, `proveT_gt`).

  Bounds attained exactly at an irrational point remain out of reach of interval
  arithmetic (documented in LIMITATIONS).
- Touching points: `interval (touch := [p₁, …])` / `realfp (touch := …)` prove
  `f ≥ c` / `f ≤ c` when the bound is attained at interior points `pᵢ`
  (`RealFPMathlib/Touch.lean`). Around each point a kernel-checked touch leaf
  checks `f(p)`, an exactly zero gradient, and an interval Hessian whose
  matrix set is positive definite via an exact rational `LDLᵀ` certificate.
  Soundness comes from a coordinate-wise second-order Taylor expansion
  (`RealFP.touch_expand`, `checkT_sound`, `proveT_le/ge`; standard axioms).
  The rest of the box uses the usual search. New examples
  `Examples/{AMGM,Motzkin}.lean` (AM–GM, `log x ≤ x − 1`, `1 + x ≤ eˣ`,
  Motzkin polynomial) and tests `Tests/TouchTest.lean`.
- The exact `LDLᵀ` factoriser of `pos_def` moved to `RealFP.PDQ.ldlInv`
  (`PosDefQ.lean`). `RealFP.PosDefTactic.ldlInv` remains as an alias.
- doc-gen4 setup in `docbuild/` (pinned to Lean/Mathlib `v4.36.0`) for a
  browsable API reference of `Interval64`, `Interval128`, `Interval64Proofs`
  and `RealFPMathlib`. See [docs/README.md](docs/README.md#api-reference-doc-gen4).
- Polished, self-contained examples of famous inequalities and constants
  (`RealFPMathlib/Examples/{Constants,ExpPi,Gaussian,Jordan,LogIneq}.lean`),
  documented in `docs/EXAMPLES.md`. Each is kernel-checked (standard axioms
  only) and elaborates in well under 30 s.
- Additional docstrings on the user-facing Interval64/Interval128 operations,
  directed scalar rounding, dyadic (`DI`) constructors, tactic options, and
  the main `toSet` enclosure theorems.

## [0.1.0] — 2026-11-24

First tagged release. Lean `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.
Licensed under Apache-2.0.

### Core library (`interval64`, no Mathlib)

- `Interval64`: binary64 intervals with outward directed rounding. Every
  directed operation has a computable Lean specification (software IEEE 754
  rounding) and a C runtime attached with `@[implemented_by]`:
  AVX-512 embedded rounding on x86-64, or a portable round-to-nearest +
  exact-error-term backend (default on arm64, `-Kbackend=rnerr` /
  `IV64_BACKEND=rnerr` elsewhere). Both backends are bit-identical to the spec.
- Operations: `+ − × ÷`, `√`, `|·|`, integer and real powers, `exp`, `log`,
  `log2`, `log10`, `sin`, `cos`, `tan`, `atan`, `atan2`, `asin`, `acos`,
  `sinh`, `cosh`, `tanh`, `π`, extended (split) division, rational
  conversions. Transcendentals use correctly rounded CORE-MATH kernels at run
  time and a rational Ziv specification in the kernel.
- A kernel fast path: `Nat` mirrors of the scalar and interval operations
  (`KF`, `KI`), proved equal to the specification, so `decide +kernel` checks
  certificates quickly.
- Matrices (positive-definiteness certificates), polynomials, Bernstein range
  enclosures, and 1D/2D Taylor quadrature, each with a kernel path.
- `Interval128`: double-double intervals (about 106-bit endpoints), with the
  same spec + C runtime design, and the 128-bit dyadic intervals
  (`Interval128.Dy`) used by the tactics at `(precision := 128)`.
- `Interval64Proofs`: enclosure theorems for `+ − × ÷ √` on the specification
  (no Mathlib), exactness when the result is representable.

### Mathlib layer (`realfp_mathlib`)

- Theorems over `ℝ` for every operation and for the certificate checkers.
- Tactics, all kernel-checked by default (`trust := kernel`, standard axioms
  only) with an opt-in `trust := native`:
  - `realfp`: one front door that dispatches on the goal shape;
  - `interval`: inequalities and `≠` over boxes (bisection, derivative and
    monotonicity certificates);
  - `root_exists` / `root_unique`: roots in one variable (IVT + monotonicity)
    and square systems (Newton search + Krawczyk);
  - `integral_bound`: bounds on `∫ x in a..b, f x` by adaptive Taylor
    quadrature;
  - `pos_def`: positive definiteness of rational matrices;
  - optimisation: minima and maxima over boxes, `sInf` / `sSup`, witnesses,
    one-variable argmin/argmax, and the `#realfp_min` / `#realfp_max` commands.
- `(precision := 128)` for every tactic: 128-bit dyadic arithmetic (about 38
  digits), with 128-bit `exp`, `log`, `log2`, `log10`, `sin`, `cos`, `sinh`,
  `cosh`, `tanh`, π to about 1e-38, derivative-based search, and a fast
  per-product certificate for integrals.
- Extension registry (`@[realfp_fn]`) for adding functions, with `erf`,
  `Real.arsinh`, `Real.artanh` and `Real.sinc` as examples.
- Error messages that name the backend, the trust mode, the failing box and
  the user's variable names.

### Assurance

- No `sorry`. A build-time axiom audit checks every `RealFP.*` theorem: only
  `propext`, `Classical.choice` and `Quot.sound`, except named demo/example
  theorems that deliberately use `native_decide`.
- Differential tests of the C runtime against the Lean specification, an
  `fesetround` reference and mpmath oracles; kernel/native agreement
  regression tests.
- GitHub Actions CI (portable backend): core build, tests, axiom audits,
  tutorial snippet check; slow examples weekly.

### Documentation

- Short README; `docs/` with a tutorial (every snippet compiled), reference,
  comparisons, limitations, philosophy and soundness notes; CONTRIBUTING.

### API notes for earlier (untagged) users

- `Interval64` and `Interval128` are root-level structures. The old names
  `Interval64.Interval64` and `Interval128.Interval128` remain as aliases, so
  types written the old way still work. Operations that were in namespace
  `Interval128.Interval128` are now in `Interval128` (for example
  `Interval128.add`, `Interval128.ofRat`); dot notation is unchanged.
- The prototype benchmarks, the `native_decide` demo and the GPU prototype
  moved to `experimental/`.

[0.1.1]: https://github.com/schlafly1/realfp/releases/tag/v0.1.1
[0.1.0]: https://github.com/schlafly1/realfp/releases/tag/v0.1.0
