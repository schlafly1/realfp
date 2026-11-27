# manybox: GPU payoff on bisection searches with 10³–10⁷ boxes

Standalone experiment (not part of `lake build`). It runs one adaptive bisection search
three ways: on one CPU core, on all CPU cores, and on the GPU. Then it hands the GPU's
bisection tree to Lean as an untrusted certificate. Measured 2026-11-26.

## Problems

| | claim | why plain bisection needs many boxes |
|---|---|---|
| **P1** | `T8(x) + T8(y) ≤ 2 + δ` on `[-1,1]²`, with `T8` given by its monomial expansion `128x⁸ − 256x⁶ + 160x⁴ − 32x² + 1` (Horner in `x²`) | The true maximum 2 is attained at 25 points, and `T8` is ≈ 1 on whole ridges. Evaluated in monomial form, the interval overestimate on a box of width `w` is ≈ `L·w`, with `L ≈ Σ k·|coeff| ≈ 2000`. Boxes near every near-maximal point must shrink to `w ≈ δ/L`, so the count grows like `1/δ`: 8.9·10³ at δ = 4, up to 1.6·10⁷ at δ = 1/1024. |
| **P2** | Choi–Lam quartic `x²y² + y²z² + z²x² + w⁴ − 4xyzw ≥ −δ` on `[-1,1]⁴` (nonnegative, not a sum of squares) | The minimum 0 is attained on whole lines: the x, y and z axes and the lines `t(±1,±1,±1,1)`. Near a line the `−4xyzw` term costs ≈ `4w²`, so boxes must shrink to `w ≈ √δ/2` along every line, and in 4-D the count grows like `δ^{-3/2}` or faster: 399 at δ = 2, up to 3.5·10⁷ at δ = 1/16. |

## Algorithm (identical on all backends)

* **Start and levels:** start from `[-1,1]^d` and work level by level. Every active box is
  evaluated with outward-rounded binary64 interval arithmetic (`mbexpr.h`).
* **Leaves and splits:** a box whose enclosure proves the claim becomes a leaf. Any other box
  is bisected at its midpoint in variable `level mod d`.
* **Box coordinates:** boxes are integer coordinates, so all endpoints are exact.
* **Expressions:** written once and compiled twice.
  * **GPU:** CUDA's per-instruction `__dadd_rd/_ru`, `__dmul_rd/_ru`, …, with `-fmad=false`.
  * **CPU:** realfp's portable RN + exact-error kernels (`c/iv64_rnerr.h`, the runtime backend
    on aarch64). OpenMP with dynamic chunks, because the GB10 CPU mixes fast and slow cores.
* **GPU level step:** an eval kernel, a CUB exclusive scan of the split flags, and a scatter
  kernel. Per level, only the split count (4 bytes) comes back to the host. The flags also come
  back if a certificate is wanted.
* **Agreement:** every timing run checked that CPU 1 thread, CPU 20 threads and GPU agree
  exactly: statistics and the full split-flag stream (FNV hash and memcmp).
* **Lean order:** the operation order matches the Lean `IExpr`s in `lean/ManyBoxCert.lean`, so
  the enclosures equal realfp's `evalK`. A GPU tree is accepted by Lean as is.

## Machine

* **System:** NVIDIA DGX Spark: GB10 GPU (48 SMs, cc 12.1, CUDA 13.0, driver 580.178)
  and 10× Cortex-X925 + 10× Cortex-A725 (20 threads), with gcc 13.3 -O2.
* **Lean checks:** run on the x86 dev box (AVX-512, 8 cores), Lean 4.36.0 with realfp's
  compiled code loaded.

## Search timings (medians; full output in `results_gb10.txt`)

"GPU" is the wall time of the whole host call: all launches, scans, per-level count readbacks
and synchronisation. The CUDA context is created once per process, which costs about 0.2 s
and is **not** included. "+cert" also copies all split flags back to the host.

**P1**

| δ | boxes evaluated | leaves | GPU | GPU +cert | CPU 1 thr | CPU 20 thr | GPU vs 1 thr | GPU vs 20 thr |
|---|---|---|---|---|---|---|---|---|
| 4 | 8,887 | 4,444 | 0.44 ms | 0.61 ms | 1.15 ms | 0.28 ms | 2.6× | 0.63× |
| 1 | 42,607 | 21,304 | 0.54 ms | 0.80 ms | 5.47 ms | 0.63 ms | 10× | 1.2× |
| 1/4 | 132,687 | 66,344 | 0.72 ms | 1.1 ms | 16.9 ms | 1.48 ms | 24× | 2.1× |
| 1/16 | 387,455 | 193,728 | 1.04 ms | 1.67 ms | 49.4 ms | 3.68 ms | 48× | 3.5× |
| 1/64 | 1,240,303 | 620,152 | 1.78 ms | 3.21 ms | 158 ms | 11.5 ms | 88× | 6.4× |
| 1/256 | 4,373,855 | 2,186,928 | 4.45 ms | 8.7 ms | 556 ms | 37.9 ms | 125× | 8.5× |
| 1/1024 | 16,407,431 | 8,203,716 | 14.5 ms | 28.8 ms | 2.08 s | 141 ms | 144× | 9.7× |

**P2**

| δ | boxes evaluated | leaves | GPU | GPU +cert | CPU 1 thr | CPU 20 thr | GPU vs 1 thr | GPU vs 20 thr |
|---|---|---|---|---|---|---|---|---|
| 2 | 399 | 200 | 0.43 ms | 0.52 ms | 0.047 ms | 0.18 ms | 0.11× | 0.42× |
| 1 | 4,815 | 2,408 | 0.56 ms | 0.77 ms | 0.43 ms | 0.32 ms | 0.77× | 0.56× |
| 1/2 | 54,271 | 27,136 | 0.65 ms | 0.99 ms | 4.54 ms | 0.70 ms | 7.0× | 1.07× |
| 1/4 | 512,463 | 256,232 | 1.14 ms | 1.87 ms | 42.4 ms | 3.43 ms | 37× | 3.0× |
| 1/8 | 4,424,415 | 2,212,208 | 4.64 ms | 8.75 ms | 365 ms | 27.7 ms | 79× | 6.0× |
| 1/16 | 34,603,103 | 17,301,552 | 32.5 ms | 69.7 ms | 2.86 s | 218 ms | 88× | 6.7× |

* **Throughput:** the GPU reaches 1.1 G boxes/s, against 8–12 M/s on 1 thread and 115–160 M/s
  on 20 threads.
* **Fixed cost:** every search has a floor of about 0.4 ms, which is about 25 µs of launches
  and synchronisation per level, times 16–41 levels.
* **Break-even:** about 5·10³ boxes against one core, and 4–5·10⁴ boxes against all 20 cores.
* **Large searches:** above 10⁶ boxes the GPU is 80–145× faster than one core and 6–10×
  faster than 20 cores.
* **Certificate copy:** copying the flags back roughly doubles the GPU time. Writing it as a
  preorder bit string costs another ≈ 0.1 s at 1.6·10⁷ nodes (`mbexport`).

## Closing the loop in Lean (`lean/`)

`lean/ManyBoxCert.lean` decodes a certificate file (preorder split bits in hex, written by
`mbexport`) into realfp's bisection certificate `Cert`. The theorems are stated over ℝ, for
example:

```lean
theorem p1_d1024_nativeF (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
    ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 2 + 1/1024
```

The GPU is an untrusted oracle. Lean re-evaluates every leaf, and a wrong bit or a wrong split
point only makes the check fail. There are three ways to check:

* **kernel:** `decide +kernel` on realfp's `checkK`, in chunks of 256 leaves (the `interval`
  tactic's proof shape). Standard axioms only.
* **native K:** `native_decide` on `checkK`. This is what realfp's `(trust := native)` runs:
  binary64 emulated on `Nat`, compiled.
* **native F:** new here. `native_decide` on `checkF`, which evaluates leaves with realfp's C
  interval runtime (`evalF`/`evalI`). `checkF_sound` (proved, no sorry) gives
  `checkF … = true → checkK … = true`, and then the normal `RealFP.prove_le` / `prove_ge`
  apply. Axioms: the standard three plus the `native_decide` axiom.

| certificate | tree nodes | leaves | kernel | native K | native F |
|---|---|---|---|---|---|
| P1 δ = 4 | 8,887 | 4,444 | ≈ 290 s alone (478 s with other jobs) | 10.1 s | 0.35 s |
| P2 δ = 1 | 4,815 | 2,408 | 187 s (with other jobs) | 4.3 s | < 0.1 s |
| P1 δ = 1 | 42,607 | 21,304 | – | – | 1.7 s |
| P1 δ = 1/64 | 1,240,303 | 620,152 | – | – | 49.7 s |
| P2 δ = 1/8 | 4,424,415 | 2,212,208 | – | – | 41.6 s |
| P1 δ = 1/1024 | 16,407,431 | 8,203,716 | – | – | 647 s (whole file 906 s) |

Every theorem compiled with no `sorry`. `#print axioms` shows `propext`, `Classical.choice`
and `Quot.sound`, plus one `native_decide` axiom for the native variants.

* **Checking costs far more than searching:** the trusted check costs 10⁴–10⁵ times the GPU
  search. For P1 at δ = 1/1024, the GPU search takes 29 ms and the native F check takes 647 s.
* **Rates:** the kernel checks about 15 leaves/s, native K about 450–550 leaves/s, and native F
  about 2.5·10⁴–1·10⁵ nodes/s. The last is limited by Lean's interpreter walking the tree,
  because `ManyBoxCert` is not precompiled; the C evaluation itself is about 0.1 µs/box.

## Precompiled checker (`lean/fast/`, `checkC3`)

`lean/fast/` is a small Mathlib-free Lake package that depends on the realfp core through a
path and is built with `precompileModules := true`. It contains the decoder and three
compiled checkers:

* **`checkC`:** `checkF`, compiled. Precompiling it alone changed nothing: P1 δ=1 took 1.62 s
  against 1.65 s. Profiling showed why. `evalI` rounds every rational constant with exact
  rational arithmetic (`ofRat q`) on every leaf, at about 73 µs per evaluation of P1 against
  about 1.3 µs for an expression without constants.
* **`checkC2`:** first applies `compile : IExpr → FExpr`, which rounds each `.rat q` to its
  interval once. Then it walks the tree with `evalFE`. `evalFE_compile` proves
  `evalFE env (compile e) = evalI env e`.
* **`checkC3`:** keeps the current box as `Interval64` (Float endpoints) during the walk, so a
  leaf needs no `Nat` ↔ `Float` conversion. `checkC3_map` proves it equals `checkC2` on the
  converted box list.

The proof chain is all proved, with no `sorry`. `checkC2_compile`, `evalFE_compile` and
`checkC3_map` are in `fast/ManyBoxFast.lean`; `checkC_sound` and `proveC3_le` / `proveC3_ge`
are in `ManyBoxCert.lean`:

`checkC3 (compile e) g cert ((boxes bs).map toIC) = true` → `checkC2 … = true` →
`checkC … = true` → realfp's `checkK … = true` → `RealFP.prove_le` / `prove_ge` → the real
theorem.

`lean/run.sh` loads the compiled library with `--plugin`. `native_decide` then calls
`decodeCertC` and `checkC3` as native code, and only the small auxiliary definition is
interpreted.

Timings were measured on the idle dev box, one file at a time, Lean 4.36.0. "eval" is the
`native_decide` evaluation as reported by the profiler. "total" is the wall time of the whole
file, including Lean start-up and imports (about 2.5 s).

| certificate | nodes / leaves | before: `checkF` eval | after: `checkC3` eval | after, total | speedup | after, leaves/s | GPU search +cert copy |
|---|---|---|---|---|---|---|---|
| P1 δ=4 | 8,887 / 4,444 | 0.35 s | 0.072 s | 0.22 s elab | 4.9× | 62 k | 0.61 ms |
| P1 δ=1 | 42,607 / 21,304 | 1.7 s | 0.245 s | 0.34 s elab | 6.9× | 87 k | 0.80 ms |
| P1 δ=1/64 | 1,240,303 / 620,152 | 49.7 s | 7.34 s | 9.9 s | 6.8× | 84 k | 3.2 ms |
| P1 δ=1/1024 | 16,407,431 / 8,203,716 | 644 s (647 s total) | 98.8 s | 101.6 s | 6.5× | 83 k | 28.8 ms |
| P2 δ=1/8 | 4,424,415 / 2,212,208 | 40.9 s | 25.6 s | 28.2 s | 1.6× | 86 k | 8.75 ms |
| P2 δ=1/16 | 34,603,103 / 17,301,552 | 320 s (327 s total) | 198 s | 201 s | 1.6× | 87 k | 69.7 ms |

* **Elaboration vs evaluation:** reading the certificate literal takes 0.07–0.1 s even at
  8.6 MB. The compiled decoder takes at most 3.5 s (P1 δ=1/1024) or 6.3 s (P2 δ=1/16), and those
  figures include an interpreted leaf count. Almost all of the time is leaf evaluation.
* **Where the remaining time goes:** realfp's Lean-level interval operations (`Interval64.add`,
  `mul`, `pown`). Each costs about 0.2–0.75 µs, because of Float boxing, tuples and one C call
  per endpoint. That makes about 12 µs per P1 leaf, against about 0.13 µs for the same
  evaluation in the C benchmark.
* **Why P2 gains less:** P2 has only one constant (`4`), so `compile` saves little.
* **Trust base:** unchanged from realfp's `(trust := native)`. `#print axioms` shows
  `propext`, `Classical.choice`, `Quot.sound` and the `native_decide` axiom; in Lean 4.36 that
  is the per-theorem `…_native.native_decide.ax_1_1`, which plays the role of
  `Lean.ofReduceBool`. Trusted are the Lean compiler and interpreter, realfp's
  `@[implemented_by]` C directed-rounding kernels (as for every realfp native proof), and the
  compiled `ManyBoxFast` shared library being the code Lake built from that module. No new
  C code was added.
* **Caveats:**
  * `--plugin` / `precompileModules` produce platform shared libraries. This was tested on
    Linux x86-64 only.
  * `lake env lean` does not load them by itself, so `run.sh` passes the flags. Without them
    the same proofs still check, but interpreted and slower.
  * Lake cannot precompile a module that imports Mathlib, which is why the compiled part is a
    separate Mathlib-free package and the soundness proof lives in `ManyBoxCert.lean`.

### Native only, or the kernel too?

The kernel cannot run compiled code. `decide +kernel` evaluates `checkK` itself at about 15
leaves/s, so a GPU certificate with 10⁶–10⁷ leaves is out of reach there: 8.2 M leaves would
take about 6 days. For kernel-only proofs the derivative certificates win (4,208 leaves for
P1 δ=1/1024, 17,056 for P2 δ=1/16). There the GPU helps only with the search and exploration,
or on problems where derivatives don't shrink the count.

Under `native_decide`, the precompiled checker now verifies the 16 M-node P1 δ=1/1024
certificate in about 100 s, at about 85 k leaves/s. That is in the same range as realfp's own
derivative *search* for that claim (≤ 160 s, from the earlier, parallel-loaded measurement;
the check of the derivative certificate itself was not timed). It is still about 3,500× the
GPU search time (29 ms).

The next step would be a batched C box evaluator: an `@[implemented_by]` routine with
specification `evalFE`, like realfp's Bernstein and quadrature routines. It could plausibly
gain another 30–100×, but it would add new trusted C code.

## The smarter alternative: realfp's own derivative search

`lean/Search*.lean` runs the `interval` tactic's certificate search (`findCertDM`:
monotonicity, centred forms, Horner) on the same claims. These ran 10 at a time on 8 cores, so
the times are upper bounds.

| claim | plain-bisection leaves (GPU) | realfp derivative cert leaves | its search time |
|---|---|---|---|
| P1 δ = 4 | 4,444 | 392 | 5–127 s |
| P1 δ = 1 | 21,304 | 1,032 | 137 s |
| P1 δ = 1/64 | 620,152 | 2,996 | 27–149 s |
| P1 δ = 1/1024 | 8,203,716 | 4,208 | 160 s |
| P2 δ = 1 | 2,408 | 304 | 4 s |
| P2 δ = 1/4 | 256,232 | 3,120 | 32 s |
| P2 δ = 1/8 | 2,212,208 | 7,816 | 76 s |
| P2 δ = 1/16 | 17,301,552 | 17,056 | 159 s |

`(deriv := false)` still tries the multivariate centred form, which is why it gives the same
certificate. The derivative certificates are 10–2000× smaller. Their growth is mild for P1,
where the maxima are isolated, and stronger for P2, where the minima lie on lines. Checking
them (MCert, centred forms) was not timed here.

## Assessment

* **GPU for the search:** on any search above about 10⁵ boxes the GPU is 3–10× faster than all
  20 CPU cores and about 100× faster than one core. With the same algorithm it never gives a
  different answer.
* **For a formal proof today the bottleneck is Lean, not the search.** Even the new
  C-runtime checker takes 10⁴× longer than the GPU search. With the derivative tricks, a
  smarter certificate is 10³× smaller and usually wins end to end.
* **Where a GPU does pay:**
  1. exploration: finding the right δ, the right splitting, or counterexamples over 10⁷–10⁹
     boxes in milliseconds;
  2. problems where derivative methods don't collapse the count: many near-extremal
     points, degenerate (line or surface) minima in 4D and above, or families of many
     independent instances;
  3. combined with a faster trusted checker. The precompiled `checkC3` (above) cut the gap
     from about 10⁴× to about 3·10³×. A batched C evaluator could shrink it further.

## Rerun

```sh
manybox/build.sh                # needs nvcc + gcc with OpenMP; -> build/mbbench, build/mbexport
manybox/build/mbbench           # full table (about 40 s on GB10); `quick` for the small sizes
manybox/make_certs.sh           # certificates for lean/ (p1_d1024 4 MB and p2_d16 8.6 MB are not committed)
(cd manybox/lean/fast && lake build +ManyBoxFast:dynlib)   # precompiled checker
manybox/lean/run.sh FastSmall.lean FastP1d1024.lean    # needs RealFPMathlib built; also Check*.lean (before)
```
