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
| **Boxes needed** | up to about 10⁵ (kernel), or about 10⁶ native; the derivative certificates often cut the count by orders of magnitude | 10⁵ to 10¹⁰ plain bisection boxes |
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
  you get 10⁸–10⁹ boxes. A GPU adds a further 5–12× (measured below).

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

<!-- TIMINGS -->

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
