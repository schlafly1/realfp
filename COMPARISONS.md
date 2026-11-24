# Comparisons

Measured results already obtained for [realfp](https://github.com/schlafly1/realfp)
against [FloatLib](https://github.com/lean-dojo/FloatLib),
[LeanCert](https://docs.leancert.io/), the
[8-point Coulomb energy formalization](https://github.com/lukasliehr/Energy-Minimization-8-Points),
and the [four-body central-configuration proof](https://arxiv.org/abs/2609.35632).
Nothing here was re-run for this file. Every timing comes from an earlier
logged measurement. Different Lean versions and shared machines mean these are
not pure backend-only comparisons.

`em8-realfp` and `four-body-realfp` (both under `schlafly1`) are private
working repos. They are named only as the sources of the showcase builds.

## Method

Two machines, both on 2026-11-23, Pacific (America/Los_Angeles):

| Machine | Used for | Notes |
|---|---|---|
| Linux box, 8 CPUs, 15 GiB RAM | LeanCert vs realfp tactics (bounds, integrals, roots, optimisation) | Shared with other jobs; some samples are outliers. Timings are the wall time of one `lean` process, including startup and imports (~3–3.5 s). The 21 shared goals are the median of 3 isolated sequential runs. |
| DGX Spark (`spark-2251`, aarch64, 20 cores, 121 GB) | 8-point Coulomb and four-body clean builds | `/usr/bin/time -v` after wiping `.lake/build`. Mathlib and realfp were prebuilt and not timed. “Max RSS” is the largest single `lean` process. Summed RSS of concurrent processes overcounts shared mappings. |

**Trust modes.**

- *Kernel*: Lean kernel checking only (`decide +kernel`, `leancert (trust := kernel)`, or `realfp` with the default `(trust := kernel)`). Successful theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.
- *Native*: `native_decide`. LeanCert then trusts compiled Lean. realfp also trusts its compiled C interval kernels (AVX-512 or RN+error), CORE-MATH, and hardware rounding. Those kernels are tested against the Lean spec, not proved equal to it.

realfp is Lean/Mathlib 4.36.0. LeanCert was [alerad/leancert](https://github.com/alerad/leancert) `44b323a`, Lean/Mathlib 4.35.0. The 8-point original was Lean 4.33.

## FloatLib

[FloatLib](https://github.com/lean-dojo/FloatLib) is a Lean 4 library of software IEEE-754 models with proved rounding, status flags, and kernel-checked tools (`interval` tactic, `float_decide`). Its directed interval arithmetic uses software floats. It has no hardware directed rounding. A separate “NativeFPU.Unchecked” path calls host `Float` in round-to-nearest only; FloatLib excludes that path from its proofs.

realfp is a native-compute alternative: binary64 interval endpoints, hardware directed rounding (AVX-512 embedded rounding on x86_64, RN plus an exact error term on arm64), and C kernels attached with `@[implemented_by]`. The core has no Mathlib or FloatLib dependency. Enclosure theorems are proved from the Lean spec; compiled code, `#eval`, and `native_decide` use the C kernels.

A completed head-to-head timing of Interval64 against FloatLib’s software intervals was not found in the notes on disk, so no such speed ratio is reported here. For scale, realfp’s own micro-benchmarks (`interval64_bench`, x86-64 box) give a runtime `addDown` of about 1.7 ns/op versus about 2.9 µs/op for the software Lean spec `addDownSpec`. FloatLib’s own published kernel figure, recorded in an earlier review of the library, is a 1,000-term binary64 dot product in 0.159 s (about 160 µs per multiply-add).

## LeanCert

[LeanCert](https://docs.leancert.io/) is broader in goal shapes (roots, Krawczyk systems, optimisation, sums, eventual bounds, exact polynomial integrals), precision (rationals, adjustable dyadics, affine arithmetic), and tooling (extension registry, docs, Python SDK). realfp is faster and closes more of the shared bound and integral goals, including in kernel mode. Both default their high-level tactics to kernel checking now (`realfp` does; LeanCert’s `leancert` still offers a native default in the reviewed revision, with an explicit kernel switch).

Sources: `/workspace/leancert-bench/COMPARISON.md`, `problems/final.res`, `problems/final_realfp.res`, `problems/opt/{lc,realfp}.res`. LeanCert times are from the first complete run (realfp then called `interval` / `integral_bound`). realfp times below are the later rerun through the unified `realfp` tactic (realfp `4d58d43` and later). Baseline imports: LeanCert 3.48 s; realfp 3.43 s in the rerun.

### 21 shared goals

realfp proved **20/21** kernel-only. The only miss is p17, which LeanCert also misses.
LeanCert’s default `leancert` proved **9/21** in kernel mode (p01–p06, p10, p12, p14) and **10/21** natively (those plus p15). A dedicated subdivision tactic on a rewritten p07 brings those counts to **10 kernel / 11 native**. Earlier writeups used that 10/11 headline.

Times in seconds. “fails” means the tactic did not prove the goal (an abandoned elaboration shows `sorryAx` and is not counted as a success). These are automation failures on these statements, not claims that no manual LeanCert proof exists.

| # | Goal (all over ℝ) | LeanCert kernel | LeanCert native | realfp kernel |
|---|---|---:|---:|---:|
| p01 | log 2 < 7/10 | 3.44 | 3.38 | 3.34 |
| p02 | 0.6931471 < log 2 < 0.6931472 | 4.48 | 3.46 | 3.51 |
| p03 | 3.14159 < π < 3.1416 | 3.62 | 3.54 | 3.56 |
| p04 | 2.7182 ≤ e ≤ 2.7183 | 3.86 | 3.58 | 3.44 |
| p05 | ∀x∈[0,1], eˣ·cos x ≤ 3 | 3.97 | 3.56 | 4.22 |
| p06 | ∀x∈[0,1], x(1−x) ≤ 1/4+1/1000 | 3.75 | 3.70 | 3.36 |
| p07 | ∀x∈[0,1], sin x ≤ x+1/1000 | router fails; subdiv. on `sin x − x ≤ 1/1000`: 62.98 | router fails; subdiv.: 8.24 | 4.23 |
| p08 | ∀x∈[0,1], 1+x+x²/2 ≤ eˣ (equality at 0) | fails | fails | 3.52 |
| p09 | ∀x∈[0,2], sin x ≤ x (equality at 0) | fails | fails | 4.37 |
| p10 | ∀x,y∈[0,1], sin x·cos y ≤ 1.01 | 24.78 | 3.93 | 4.82 |
| p11 | ∀x,y∈[0,1], xy−x−y ≥ −1.01 | timeout (300 s) | fails | 3.57 |
| p12 | ∀x,y,z∈[0,1], xy+yz+zx ≤ 3 (equality at a corner) | 4.49 | 4.10 | 3.35 |
| p13 | ∀x,y∈[0,1], e^{xy}−x−y ≥ −0.01 (true min 0) | fails (38 s) | fails | 11.34 |
| p14 | 0.74 ≤ ∫₀¹ e^{−x²} | 89.54 | 4.37 | 4.67 |
| p15 | 0.7468 ≤ ∫₀¹ e^{−x²} (margin 2.4e-5) | fails (recursion depth) | 52.98 | 5.72 |
| p16 | ∫₁² 1/x ≤ 0.6932 | fails (reify) | fails | 4.77 |
| p17 | ∫₀¹ arctan ≤ 0.43882 (margin 4.6e-6) | fails | fails | fails |
| p18 | ∫₀¹ arctan ≤ 0.439 | fails (reify) | fails | 9.35 |
| p19 | ∫₁² 1/x ≤ 0.7 | fails | fails | 7.50 |
| p20 | ∀x,y∈[−1,1], x²+y²−xy ≥ −0.01 | fails (28.8 s) | fails | 5.57 |
| p21 | Rosenbrock ≥ −0.01 on [−2,2]×[−1,3] | fails (289 s) | fails | 4.59 |

Where both succeed with a non-trivial certificate, realfp’s kernel check is much faster than LeanCert’s kernel check, and is comparable to LeanCert native:

| Goal | realfp kernel | LeanCert kernel | LeanCert native |
|---|---:|---:|---:|
| p07 (LC subdivision form) | 4.23 | 62.98 | 8.24 |
| p10 | 4.82 | 24.78 | 3.93 |
| p14 | 4.67 | 89.54 | 4.37 |
| p15 | 5.72 | fails | 52.98 |

Observed reasons for LeanCert failures: no derivative or monotonicity certificates in the router (touching bounds p08, p09, p13); multivariate dependency (p11, p20, p21); first-order partition integration (p15); the integration front door did not reify `1/x` or `arctan` (p16, p18, p19). p17 is tight (margin about 4.6e-6); realfp found no certificate with Taylor order ≤ 8 and ≤ 512 cells.

### Roots

After the `realfp` front door and root tactics (`root_exists` / `root_unique`, including Krawczyk systems), measured on the same box, kernel-only, standard axioms:

| Goal | realfp | LeanCert kernel | LeanCert native |
|---|---:|---:|---:|
| x01 `∃! x ∈ [1,2], x² − 2 = 0` | 3.84 | 5.03 | 5.32 |
| x03 `∃! p : ℝ×ℝ` in `[0.9,1.1]²` with `x²+y=2`, `x+y²=2` (Krawczyk) | 4.46 | — | — |

x03 was not in the original LeanCert timing set. A 2×2/3×3 examples file (`RealFPMathlib/Examples/Roots.lean`, 17 theorems) builds in about 13 s.

### Optimisation

Same ten statements in both, kernel trust, one process per file (timeout 600 s LeanCert / 400 s realfp). realfp proved **10/10**; LeanCert proved **4/10**.

| Problem | LeanCert | realfp |
|---|---|---|
| o01 `∃ m : ℚ, ∀ x ∈ [0,1], x²+sin x ≥ m` | 37.2 s ✓ | 4.9 s ✓ (1 box) |
| o02 `x²−x ≥ −1/4 − 10⁻⁶` | 4.3 s ✓ | 3.4 s ✓ (4 boxes) |
| o03 `x²−x ≥ −1/4` (exact, f′=0 at the min) | 3.9 s ✓ | 3.6 s ✓ (4 boxes) |
| o04 six-hump camel `≥ −1.032` | timeout 600 s ✗ | 23.0 s ✓ (248 boxes) |
| o05 camel `∃ m : ℚ` | killed at 365 s ✗ | 17.8 s ✓ (168 boxes) |
| o06 argmin exists on [0,1] | fails (`sorryAx`) ✗ | 3.4 s ✓ |
| o07 `∃ M, x e^{−x} ≤ M` | 3.3 s ✓ | 6.2 s ✓ (10 boxes) |
| o08 Himmelblau `≥ −10⁻³` | fails 75 s ✗ | 3.3 s ✓ (1 box) |
| o09 Rosenbrock `∃ m : ℚ` | killed at 324 s ✗ | 3.7 s ✓ (1 box, m = 0) |
| o10 `sin x e^{−x} + x/10 ≥ 0` | fails ✗ | 3.9 s ✓ (1 box) |

All realfp successes: `propext`, `Classical.choice`, `Quot.sound` only. o08–o10 are easy for an evaluator that keeps squares as squares; LeanCert’s failures there are tactic-side, not interval-width limits.

realfp-only forms, same run: `sInf (f '' Icc 0 1) = −1/4` 3.5 s; `|sInf … − v| ≤ 10⁻⁶` 10.8 s; Himmelblau / Rosenbrock `sInf = 0` 3.7 s / 3.3 s; camel `sInf ∈ [−1.0317, −1.0316]` 40.6 s.

## 8-point Coulomb energy

Original formalization: [lukasliehr/Energy-Minimization-8-Points](https://github.com/lukasliehr/Energy-Minimization-8-Points) (Kryvonos–Liehr–Taylor, Coulomb / s = 1, N = 8). realfp re-verification is the private repo `schlafly1/em8-realfp`: branch `main` uses `native_decide`; branch `kernel-only` uses only `decide +kernel`.

Targets: `EM8` and `EM8Port.Coulomb8.WithCollisions` (plus `EM8Port.KernelAxioms` for kernel-only). Spark clean builds:

| Build | Cores | Wall | CPU (user+sys) | Max RSS (1 proc) |
|---|---:|---:|---:|---:|
| Theirs (KLT, kernel) | 20 | 37:35 | 42186 s (11.7 h) | 18.2 GB |
| Theirs (KLT, kernel) | 8 | 2:03:22 | 58437 s (16.2 h) | 18.2 GB |
| Ours, `native_decide` (`main`) | 20 | 0:54.7 | 254 s | 5.0 GB |
| Ours, `native_decide` (`main`) | 8 | 1:05.5 | 311 s | 5.0 GB |
| Ours, kernel-only | 20 | 6:49.8 | 4000 s (1.11 h) | 9.8 GB |
| Ours, kernel-only | 8 | 12:10.7 | 4735 s (1.32 h) | 9.8 GB |

The kernel-only build is about 5.5× faster in wall time and 10.5× cheaper in CPU than theirs on 20 cores, and about 7.5× slower in wall time than our `native_decide` build. Theirs was `50d14bc0` (20 September 2026 Coulomb release, Lean 4.33). Ours native was timed at `fdb64b9`; kernel-only timings are a clean build of `d34c900`.

**Axioms.** Kernel-only: both `EM8.phase1_certificate` and `Coulomb8.coulomb_energy_N8_solution_with_collisions` depend on `propext`, `Classical.choice` and `Quot.sound` only; no `native_decide` in the sources. The `main` native build uses those three plus 12 `native_decide` auxiliary axioms. Theirs reports the same three standard axioms.

**Size.** Theirs: 1195 modules, 357,958 lines (and up to 18.2 GB for a single `lean`). Ours native: 101 modules, 7,560 lines. Kernel-only certificate data is about 2.5 MB of untrusted literals (`Data.lean` 254 KB, `ColsData.lean` 1.6 MB, `NormData.lean` 0.67 MB), checked in the kernel (Kronecker substitution at base 2^160, and fixed-point intervals at 2^−160).

## Four-body central configurations

The theorem is Tomar, *Uniqueness of convex central configurations in the planar four-body problem*, [arXiv 2609.35632](https://arxiv.org/abs/2609.35632), formalized in lean4body. realfp re-verification is the private repo `schlafly1/four-body-realfp` (`main`, `7da88d7`): a fused branch-and-bound in Interval64, 16 `native_decide` chunks, no stored search certificates.

**Native result.** Theorems `C4.theoremA` and `C4.theoremB` compile with 0 `sorry`. Axioms: the three standard ones plus 16 `native_decide` axioms (`chChunk0–7`, `dirChunk0–7`). 63 modules, 13,134 lines. The two charts have 62,720 and 73,728 cells.

| Measurement | Wall | CPU | Max RSS (1 proc) |
|---|---|---|---|
| Spark, 20 cores, clean `lake build C4 C4Run` (Mathlib + realfp prebuilt) | 1:49.7 | 612 s (562 user + 50 sys) | 7.5 GB |
| Linux box, 8 cores shared, `LEAN_NUM_THREADS=4`, clean build | 213 s | 13.7 CPU-min (12m25 user + 1m17 sys) | 6.9 GB |

lean4body itself was not timed on these machines. Its published cost is 7.6 CPU-h of kernel replay of 2.7 MB of certificates from an unverified search.

**Kernel-only estimate (not built).** Direct kernel evaluation of the native search is infeasible: the native B&B used 307 CPU-s, about 6×10^10 interval operations, which at a measured ~0.3 ms per kernel KD operation is about **5000 CPU-h**. Replaying a recorded tree with KD slope jets (work counts from 1/64 of the cells, scaled by 64: about 716k Newton steps and 299k certifications; ~1.1 s and ~6.3 s per box in the kernel) is about **740 CPU-h** (certifications alone ~520 CPU-h), still far more than lean4body’s 7.6 CPU-h. Competing in kernel mode would need their design: low-precision fixed point tailored to the formulas, with search outputs stored as hints. four-body-realfp stays on `native_decide`.

## Sources

- LeanCert vs realfp: `/workspace/leancert-bench/COMPARISON.md` and `problems/*.res` (21 goals and o01–o10).
- 8-point timings and axioms: `em8-realfp` README (branch `kernel-only`) and `NOTES-kernel.md`; Spark log notes in `/workspace/showcase/NOTES.md`.
- Four-body native timings: `/workspace/showcase/NOTES.md`, `/workspace/showcase/fourbody/NOTES.md`; kernel estimates in `em8-realfp` README / `NOTES-kernel.md` and `/workspace/kernel-notes/PROGRESS.md`.
- FloatLib characterisation and the 0.159 s kernel dot-product figure: `/workspace/floatlib/COMPARE.md` (review of FloatLib docs and source). realfp `addDown` micro-benchmark: this repo’s README.
