# GPU-assisted many-box proofs (`RealFP.Grid`, `interval_grid`, `realfp-grid`)

**Opt-in.** Nothing here is part of realfp's default `lake build`, and users without a GPU
or CUDA are unaffected. The Lean side builds on any machine. The search tool (`grid/`)
builds with or without CUDA; without CUDA it runs on all CPU cores.

Contents: [What it is](#what-it-is) · [When to use it](#when-to-use-it) ·
[Trust](#trust-what-a-proof-depends-on) · [Install](#install) ·
[Workflow](#workflow) · [Showcases and timings](#showcases-and-timings) ·
[Limitations](#limitations)

## What it is

Some inequalities are true but tight on large parts of the box, so they need millions or
billions of small boxes. Interval arithmetic proves the claim on each box, and no
cleverness, such as derivatives, brings the count down much. Typical cases:

* the minimum is attained, or nearly attained, on curves or surfaces;
* there are several variables;
* the margin is small.

The same few operations run on every box, which is the kind of work a GPU is good at.

`RealFP.Grid` splits the work into a **search** and a **check**:

1. **Search (untrusted).** `realfp-grid`, a standalone program (CUDA fp32/fp64, or
   multithreaded CPU), bisects the box and writes a *certificate*: one bit per node of the
   bisection tree, 1 = split, 0 = leaf.
2. **Check (trusted).** In Lean, a C checker (`RealFPMathlib/c/grid_tape.c`, multithreaded)
   walks the same tree. It recomputes every box and its binary64 outward-rounded enclosure
   itself, and confirms each leaf. It runs under one `native_decide`.

   A soundness theorem (`RealFP.Grid.prove_le`/`prove_ge`, in `RealFPGrid/Sound.lean`) turns
   a `true` result into `∀ x ∈ box, f x ≤ c` over `ℝ`. A wrong or forged certificate can only
   make the check return `false`.

Three Lean libraries, all outside the default build:

| library | contents |
|---|---|
| `RealFPGridNative` | expression compiler, tape builder (with common-subexpression elimination), the checker's Lean spec and its `@[extern]` C implementation, built-in search; Mathlib-free, precompiled |
| `RealFPGrid` | soundness over `ℝ` and the `interval_grid` tactic, `#grid_export` |
| `RealFPGridExamples` | quick-start theorems and the checker's C-versus-spec tests |

A fourth library, `RealFPGridShowcase`, holds the big showcases. Only `grid/showcase.sh`
builds it, because its proofs are generated (see [Showcases](#showcases-and-timings)).

## When to use it

Start with realfp's `interval` / `realfp`. Switch to `interval_grid` when all of the
following hold:

| question | `interval` / `realfp` | `interval_grid` |
|---|---|---|
| **Operations** | everything realfp supports, including `exp`, `log`, `sin`, `atan`, … | `+ − * /`, negation, `√`, natural powers only |
| **Trust** | `kernel` (default, standard axioms only) or `native` | always `native_decide` (+ the C checker) |
| **Boxes needed** | up to about 10⁴ to 10⁵. It ran at 20–60 boxes/s on the 6–8-variable showcases, faster in low dimension; each box also tries derivative tests, which often cut the count by orders of magnitude | 10⁵ to 10¹⁰ plain bisection boxes |
| **Dimension** | 1–3 comfortably; more if the margin is wide | 2–16 variables; it pays off most in 4–8 dimensions |
| **Margin** | comfortable or moderate | tight: the count grows like δ^-k as the margin δ shrinks |

Rules of thumb:

* **Try `interval` first.** If it fails within its default budget, run
  `interval_grid (explore := true)`. It reports how close the bound is (an enclosure of the
  minimum or maximum, and a point where it is attained). If the margin is small and the
  dimension is 4 or more, `interval_grid` is likely the right tool.
* **Low dimension, wide margin:** use `interval`. A few hundred boxes suffice, and `interval`
  can stay kernel-only.
* **Transcendental functions:** use `interval`. The grid checker only has the polynomial,
  rational and `√` operations.
* **Kernel-only proofs:** these cannot use `interval_grid`. The kernel checks about 15
  boxes per second, so a GPU certificate with millions of leaves is out of reach. For the
  kernel, use `interval`'s derivative certificates. The GPU can still help you explore.
* **The tool is optional.** Without `realfp-grid`, `interval_grid` uses its built-in
  single-threaded search. It managed about 1.6·10⁵ boxes/s on the x86 dev box (Nesbitt:
  282,013 boxes in 1.75 s), which is fine up to about 10⁷ boxes. With the tool on all CPU cores
  you get 10⁸–10¹⁰ boxes. A GPU makes the search another 5–12× faster (measured below).

## Trust: what a proof depends on

`#print axioms` on an `interval_grid` theorem shows `propext`, `Classical.choice`,
`Quot.sound`, and one `…native_decide.ax_…` axiom per check. No `sorry`.

* **The GPU is never trusted.** Nor is the CPU search, the certificate file, or the
  generated Lean files for big certificates. They are all hints. Everything is re-verified
  by the checker or by Lean.
* **Trusted under `native_decide`:**
  * the Lean compiler;
  * the C checker `c/grid_tape.c` (about 390 lines), which `@[implemented_by]` links to its
    Lean specification `checkGridSpec` without a proof;
  * realfp's existing binary64 interval kernels, which the checker calls.

  The checker is tested against the spec in `RealFPGridExamples/CheckerTests.lean`: mutation
  tests, plus 3000 random expressions, on x86-64 (AVX-512 backend) and aarch64 (RN + error
  term backend).
* **Not affected:** realfp's core, its default build, and the trust of every other realfp
  proof are unchanged. A file that does not import `RealFPGrid` cannot depend on the checker.

## Install

The Lean side needs no extra software:

```
cd RealFPMathlib
lake build RealFPGrid RealFPGridExamples     # also runs the checker tests
```

The search tool needs a C++17 compiler; CUDA is optional:

```
grid/build.sh                  # → grid/build/realfp-grid ("CPU only" if nvcc is not found)
grid/build/realfp-grid info    # engines and GPU
```

* **With CUDA:** `nvcc` must be on `PATH`. Tested with CUDA 13.0 on an NVIDIA GB10 (DGX
  Spark, compute capability 12.1). It needs the CUDA runtime, NVRTC and the driver API. The
  tape is compiled at run time into straight-line GPU code; set `RFG_NOJIT=1` to use the
  interpreter instead. No system-wide changes are made.
* **Finding the tool:** `interval_grid` looks for `$REALFP_GRID`, then `realfp-grid` on
  `PATH`, then `grid/build/realfp-grid` in the realfp checkout.
* **Platforms tested:** Linux x86-64 (CPU only), and Linux aarch64 (CPU and CUDA). The
  checker requires a little-endian host. macOS and Windows were not tested.

## Workflow

### 1. Explore: how much margin is there?

```lean
import RealFPGrid

example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, x * y - x ^ 2 ≤ 1 / 4 + 1 / 1000 := by
  interval_grid (explore := true)
```

This proves nothing and always fails. Its error message gives a rigorous enclosure of the
maximum (or minimum), a point where it is (nearly) attained, and the time taken. For a
quick, wide look on a GPU, add `(tool := gpu32)`.

The command-line tool does the same thing with a time limit:

```
realfp-grid minmax P.problem [--max] [--depth N] [--time S]
```

Get the problem file from `interval_grid (export := "P.problem")` or from
`#grid_export "P.problem" : statement`.

When a proof fails, the message shows the box where it got stuck and the enclosure there.
If the bound is false at that box's midpoint, the message says so: that is a
**counterexample**, checked rigorously.

### 2. Prove

```lean
theorem nesbitt (a b c : ℝ) (ha : 1 ≤ a) (ha' : a ≤ 3) (hb : 1 ≤ b) (hb' : b ≤ 3) (hc : 1 ≤ c)
    (hc' : c ≤ 3) : 3 / 2 - 1 / 64 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  interval_grid (cert := "certs/nesbitt.cert")
```

* **The search:** the tool runs if found (GPU if there is one, else all CPU cores).
  Otherwise the built-in search runs.
* **The cache:** `(cert := "file")` saves the certificate next to the Lean file, keyed by a
  hash of the problem. Later builds and other users skip the search, and the tool is not
  needed to re-check. Commit the file.
* **Options:**
  * `(tool := auto | none | cpu | gpu | gpu32 | gpu64)`;
  * `(depth := n)` (default 30 per variable);
  * `(maxBoxes := n)`.
* **Splitting is automatic.** The checker splits large certificates across threads
  (`RFG_THREADS`, default: all cores).

Examples: `RealFPMathlib/RealFPGridExamples/QuickStart.lean`.

### 3. Very large certificates (10⁸ boxes and more)

A certificate with billions of bits is too big to put in one Lean term, and too slow to
check in one process. `grid/showcase.sh` does the following:

1. It splits the certificate at depth `K` into a small top tree plus up to 2ᴷ
   sub-certificates (`realfp-grid prove --split K`).
2. `grid/gen_lean.py` writes one Lean module per group of sub-certificates, plus a glue
   module. Each group is proved by its own `native_decide`.
3. `lake build` checks the groups in parallel, one per core.
4. The glue proves that the top tree's leaves are exactly the groups' boxes (by `rfl` and a
   checked lemma). That gives `bound : ∀ xs, InBoxes xs bs → e.denote xs ≤ c`.
5. The final theorem states the inequality in ordinary notation and closes it with
   `interval_grid (use := …bound)`. That step checks that `bound` is about the same
   expression, box and constant.

```
grid/showcase.sh r8 R8 16 8 gpu64    # problem, split depth K, group depth K1, engine
```

The generated files are not trusted and are not committed (`.gitignore`); rerun the script
to rebuild them.

## Showcases and timings

All timings below were measured on 2026-11-27 on an NVIDIA DGX Spark:

* **GPU:** GB10 (48 SMs, CUDA 13.0).
* **CPU:** 10 Cortex-X925 + 10 Cortex-A725 cores (20 threads), aarch64. realfp's RN +
  error-term backend.

The tool's own reported times are shown, with the process wall time in parentheses. "Nodes"
counts the certificate's bits (splits plus leaves).

Another user's long job was running on the machine at the same time, so the CPU numbers are,
if anything, pessimistic.

### Search: `realfp-grid prove`

* **R8:** `Σᵢ T₄(xᵢ)T₄(xᵢ₊₁) ≥ c` on `[−1, 1]⁸` (a ring of 8 Chebyshev terms; the true
  minimum is −8, attained at irrational points).
* **M6:** Reznick's AM–GM form `x₆¹² + P·Σxᵢ² − 6x₆²P ≥ c` on `[−1, 1]⁶`, with
  `P = x₁²⋯x₅²` (the minimum is 0, attained).

| problem | nodes | GPU fp32 | GPU fp64 | CPU 20 threads | CPU 1 thread |
|---|---|---|---|---|---|
| R8, c = −12 | 3.9·10⁸ | 3.3 s (4.9) | 5.5 s (7.0) | 40.6 s | 290 s |
| R8, c = −10 | 2.0·10⁹ | 21.9 s (23.2) | 33.9 s (35.1) | 173 s | — |
| R8, c = −9 | 1.07·10¹⁰ | 112 s (116) | 176 s (180) | 914 s | — |
| M6, c = −1/2 | 3.2·10⁸ | 2.5 s (3.7) | 3.4 s (4.6) | 16.7 s | 115 s |
| M6, c = −3/8 | 1.5·10⁹ | 6.8 s (7.8) | 11.2 s (12.2) | 83.2 s | — |
| M6, c = −1/4 | 1.3·10¹⁰ | 90.0 s (93.6) | 129 s (133) | 817 s | — |

* **Speedups:** against all 20 CPU threads, GPU fp32 is 7–12× faster and GPU fp64 is 5–7×
  faster. Against one thread, the GPU is 46–87× faster.
* **Identical certificates:** `cpu` and `gpu64` produce bit-identical certificates in every
  row. `gpu32` matches them on R8. On M6 its wider enclosures give certificates about 0.002%
  larger. Use `gpu64` or `cpu` certificates for proofs: a `gpu32` certificate is not
  guaranteed to pass the binary64 checker.
* **Memory:** the c = −9 and c = −1/4 runs need about 42 GB of host memory.

### Proof: certificate to Lean theorem (`grid/showcase.sh … 16 8 gpu64`)

| step | R8 ≥ −9 (5.3·10⁹ leaves) | M6 ≥ −1/4 (6.5·10⁹ leaves) |
|---|---|---|
| problem files (`#grid_export`) | 11.4 s | 2.5 s |
| search, GPU fp64, with the split into sub-certificates | 207 s | 180 s |
| generate the Lean files | 4.1 s | 7.3 s |
| check 256 group modules in parallel (C checker, `native_decide`) | 379 s | 257 s |
| glue (`TopC.sound`) and final theorem | 9.0 s | 16.5 s |
| **total** | **611 s (10.2 min)** | **464 s (7.7 min)** |

The theorems are `RealFPGridShowcase/R8.lean` (`r8_ge`) and `RealFPGridShowcase/M6.lean`
(`m6_ge`). The generated files take 2.7 GB and 3.1 GB, and are not committed.

### Without the GPU

* **CPU tool:** the same searches on all 20 CPU threads take 914 s (R8 ≥ −9) and 817 s
  (M6 ≥ −1/4), with the same certificates. With the same Lean checking time, that gives
  about 22 and 18 minutes end to end (the sum of the measured steps).

  Most of the payoff over `interval` comes from plain bisection plus the multithreaded C
  checker; the GPU makes the search another 5–12× faster. On one CPU thread the searches
  would take hours (R8 at c = −12 alone takes 290 s).
* **realfp's `interval`:** `interval (trust := native)` was run on the easiest rows, R8 at
  c = −12 and M6 at c = −1/2. With a budget of 3000 boxes, it stopped after 145 s and 48 s,
  including imports.

  Those wall times include imports and elaboration, so the rates are about 20 boxes/s on R8
  and 60 boxes/s on M6 (each box also tries derivative certificates). Both runs reported
  that they could not certify. With a budget of 200,000 boxes, R8 had not finished after
  18 minutes on the Spark (stopped), nor within a 30-minute timeout on the x86 dev box.

  The plain bisection certificates have 1.9·10⁸ (R8) and 1.6·10⁸ (M6) leaves. At those
  rates, `interval` would need months for them. Its derivative tests might cut the count,
  but they do not help much here, because the minimum is attained in the interior on large
  sets. This is an extrapolation, not a measurement.
* **The kernel:** it checks about 15 boxes/s, so kernel-only proofs of these bounds are out
  of reach.

So with the GPU, R8 ≥ −9 and M6 ≥ −1/4 become Lean theorems in about 10 and 8 minutes. The
easier constants take seconds to search. With realfp's `interval`, the same bounds would
take months or more.

### Exploration: `realfp-grid minmax` (time-limited)

| problem | engine, limit | result |
|---|---|---|
| R8 | gpu32, 10 s | min ≤ −7.9126 (a point), 8·10⁷ boxes |
| R8 | gpu32, 60 s (finished at depth 80, 34 s) | min ≤ −7.99983 at (≈0, ±0.708, …), 2.5·10⁸ boxes |
| R8 | cpu 20 threads, 60 s (depth 80, 59 s) | min ≤ −7.99983, the same boxes |
| M6 | gpu32, 60 s (depth 80, 25 s) | min ∈ [−0.782, 0], attained at 0 |

* **What `minmax` is good at:** it quickly finds where the extremum is, and a rigorous
  value at a point. That value is a proof that no bound beyond it can hold.
* **What it is not good at:** in 8 dimensions its rigorous lower bound stays weak (−19.3 for
  R8), because the frontier it can keep is limited.
* **Finding the best provable constant:** bisect on `c` with `realfp-grid prove --engine
  gpu32`, which takes seconds per try (table above). For R8, c = −12, −10 and −9 succeed;
  the true minimum is −8.

## Limitations

* **Operations:** `+ − * /`, negation, `√`, and natural powers. There are no transcendental
  functions; use realfp's `interval`.
* **Goals:** `≤` and `≥` (and `f ≤ g`) over boxes with rational endpoints, and conjunctions
  of these. Strict `<` is not supported; prove a slightly tighter `≤`.
* **Method:** plain bisection (round-robin over variables), with no derivatives or Taylor
  models. Problems where `interval`'s derivative certificates shrink the count enormously
  are better done there.
* **Size limits:** at most 16 variables. The tape may have at most 4096 instructions in
  Lean, and at most 1024 in the tool. For certificates of about 10⁸ bits and more, use
  `grid/showcase.sh`: it keeps every Lean term small and checks in parallel.
* **Trust:** always `native_decide`; there is no kernel-only mode.
* **Platforms:** little-endian hosts only. Tested on Linux x86-64 and aarch64 (and CUDA on
  aarch64 GB10); macOS, Windows and other GPUs are untested.
* **Memory:** the tool keeps the frontier of each level on the device. When it overflows,
  it finishes the level's holes in chunks, so the memory stays bounded and no work is
  repeated. Certificates with 10¹⁰ bits still need tens of GB of host memory.
* **CI:** CI does not build these libraries (that would need a workflow change), so build
  them locally.
