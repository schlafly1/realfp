# manybox: GPU payoff on bisection searches with 10³–10⁷ boxes

> **Now supported (opt-in):** this experiment grew into `RealFP.Grid`: the `interval_grid`
> tactic, the C checker `RealFPMathlib/c/grid_tape.c`, and the search tool `grid/`
> (`realfp-grid`, CUDA or CPU). See [docs/GPU.md](../../../docs/GPU.md). The files here are
> kept as the original experiment and its measurements.

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

### C batch checker (`lean/fast/ManyBoxTape.lean`, `lean/fast/c/mbtape.c`, `checkHex`)

The whole certificate check runs in C. It is attached the way realfp attaches its Bernstein
checker (`checkGeB` / `checkGeBImpl` / `iv64_bern_check`):

* **Spec:** `checkHex fe upper c d hex env := checkC3 fe (if upper then gLe c else gGe c)
  (decodeCertC d hex) env`. `checkHex_le` / `checkHex_ge` are `rfl`. `proveT_le` / `proveT_ge`
  (in `ManyBoxCert.lean`) then go through `proveC3_le/ge` → `checkK` → `RealFP.prove_le/ge`.
* **Runtime:** `@[implemented_by checkHexImpl]`. `checkHexImpl` compiles the expression once to
  a flat tape: 12-byte instructions `var/const/add/sub/mul/neg/pow` plus a constant pool. It
  then calls `@[extern "mb_check_tape"]`. The C loop decodes the hex preorder bits, keeps the
  box as doubles, interprets the tape at every leaf and applies `gLe`/`gGe`. If the expression
  has another node (div, sqrt, transcendental), if `d ∉ [1,16]`, or if `env.length ≠ d`, it
  falls back to `checkC3`.
* **Exactness:** the C mirrors realfp's definitions operation by operation: `Interval64.add`,
  `sub`, `mul`/`accCorner`, `neg`, `abs`, `square`, `ipow`/`ipowAux 64`, `powLo`/`powHi`,
  `pown`, and `KF.cmp`/`le` on bit patterns. It also mirrors `decC`/`midBitsC`/`bitAtC`,
  including `get!`'s 0 past the end of the string. For rounding it calls realfp's own
  `iv64_dir_*` kernels, so it uses whichever backend the core was built with (AVX-512 or
  RN + error term). It is compiled with no backend flags, `-ffp-contract=off -frounding-math`.
* **Fails safe:** anything outside the range the C handles exactly (a coordinate ≥ 2⁵¹, a
  shift > 1000, a bad tape, a big-endian host, a failed allocation or thread) returns `false`.
* **Threads:** subtrees below a cut depth are checked by pthreads (`MB_THREADS`, default all
  CPUs, at most 64; `MB_THREADS=1` is serial). The spec's value is the conjunction of
  pure midpoint and leaf tests, so the order of evaluation does not change it.

Timings were taken on the idle dev box (x86-64, AVX-512 backend, 8 CPUs), one file at a time.
They are `native_decide` evaluations as reported by the profiler and include decoding. Each
file's wall time also includes about 2.5 s of Lean start-up.

| certificate | leaves | before: `checkC3` | after, 8 threads | after, 1 thread | speedup (8 / 1) | leaves/s (8 / 1) | GPU search + cert copy |
|---|---|---|---|---|---|---|---|
| P1 δ=4 | 4,444 | 0.072 s | 1.9 ms | 4.1 ms | 38× / 18× | 2.4 M / 1.1 M | 0.61 ms |
| P1 δ=1 | 21,304 | 0.245 s | 3.8 ms | 18.1 ms | 64× / 14× | 5.6 M / 1.2 M | 0.80 ms |
| P1 δ=1/64 | 620,152 | 7.34 s | 0.081 s | 0.509 s | 91× / 14× | 7.7 M / 1.2 M | 3.2 ms |
| P1 δ=1/1024 | 8,203,716 | 98.8 s | 1.13 s | 7.01 s | 87× / 14× | 7.3 M / 1.2 M | 28.8 ms |
| P2 δ=1/8 | 2,212,208 | 25.6 s | 0.246 s | 1.49 s | 104× / 17× | 9.0 M / 1.5 M | 8.75 ms |
| P2 δ=1/16 | 17,301,552 | 198 s | 1.77 s | 11.9 s | 112× / 17× | 9.8 M / 1.5 M | 69.7 ms |

* **Whole files:** the P1 δ=1/1024 theorem file takes 3.6 s wall and the P2 δ=1/16 file 4.6 s,
  against 101.6 s and 201 s before.
* **The gap to the GPU search** shrinks from about 3,500× to about 40× (P1 δ=1/1024) and 25×
  (P2 δ=1/16).
* **DGX Spark** (aarch64, so realfp's RN + error-term backend; 10 X925 + 10 A725 cores), via
  `lean/fast/bench.sh` (Mathlib-free, compiled C vs compiled spec):
  * P1 δ=1/1024: 3.91 s on 1 thread, 0.82–0.88 s on 20 threads; the compiled spec took 68.9 s.
  * P2 δ=1/16: 6.99 s on 1 thread, 1.07–1.21 s on 20 threads; the compiled spec took 139 s.
  * Scaling beyond 8 threads is weak, because the bisection trees are very unbalanced.
* **Agreement tests (C vs Lean spec):** `lean/TapeTest.lean` on the box and `bench.sh` on the
  Spark.
  * Passing and failing bounds, plus truncated certificates.
  * Every hex digit (or every k-th) of the small certificates replaced by `0`/`7`/`f`:
    10,329 mutated certificates on the box (240 of them pass) and 17,040 on the Spark.
  * 0 disagreements, and all six certificates are `true` in both.
* **Axioms:** `#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` and the
  per-theorem `native_decide` axiom. No `sorry`.
* **Trust:** this adds new trusted code, but only under `native_decide` for these proofs.
  * `c/mbtape.c`: 344 lines, 283 of them non-comment.
  * The Lean side of `checkHexImpl`: tape builder, box packing, the dispatch (about 50 lines).
    `implemented_by` replaces the spec with it without proof.
  * realfp's core and its default `lake build` are unchanged, and so is the trust of every
    other realfp proof.
* **Caveats:**
  * Polynomial-type nodes only.
  * Little-endian hosts only (otherwise the check returns `false`).
  * At most 16 variables and 4,096 tape instructions.
  * Tested on Linux x86-64 (AVX-512 backend) and Linux aarch64 (RN + error-term backend). The
    RN + error-term backend on x86 (`IV64_BACKEND=rnerr`) and macOS were not tested.

### The derivative certificate, checked (P1 δ=1/1024, 4,208 leaves)

realfp's `interval` tactic was run on the same goal, on the box, alone:
`lean/DerivKernel1024.lean`, `DerivNative1024.lean` and `DerivSearch1024.lean`.

| | search | check | file total |
|---|---|---|---|
| `interval` (kernel, default) | 150 s | 592 s kernel type checking | 746 s |
| `interval (trust := native)` | 153 s | 30.3 s interpreted + about 9 s compiling | 196 s |
| `findCertDM` + `checkM` in `#eval` | 150.6 s | 28.7 s | 183 s |
| GPU + C checker (`checkHex`, 8 threads) | 0.029 s (GPU) | 1.13 s | 3.6 s |

Under `native_decide`, the GPU certificate (8.2 M leaves) is now checked about 25× faster than
realfp checks its own 4,208-leaf derivative certificate natively. Counting the search too, the
GPU path is about 50× faster end to end. In the kernel the derivative certificate is the only
option, at 592 s.

### Native only, or the kernel too?

The kernel cannot run compiled code. `decide +kernel` evaluates `checkK` itself at about 15
leaves/s, so a GPU certificate with 10⁶–10⁷ leaves is out of reach there: 8.2 M leaves would
take about 6 days. For kernel-only proofs the derivative certificates win (4,208 leaves for
P1 δ=1/1024, 17,056 for P2 δ=1/16). There the GPU helps only with the search and exploration,
or on problems where derivatives don't shrink the count.

Under `native_decide`, the C batch checker (above) verifies the 16 M-node P1 δ=1/1024
certificate in 1.13 s, at 7.3 M leaves/s with 8 threads (1.2 M on one). The precompiled
`checkC3` took about 100 s. The C checker is faster than realfp's own derivative search
(150 s) and than its native check of the 4,208-leaf derivative certificate (30 s). It is still
about 40× the GPU search time (29 ms).

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

## v2: division and square roots, fp32 search, 6–8 variables, split and weaker certificates

New pieces (all experimental; the realfp core is unchanged):

* `v2/`: one generic search engine (C++ templates over a rounding policy) for GPU fp64
  (`__dadd_rd`/`__dmul_ru`…), GPU **fp32** (`__fadd_rd`/`__fmul_ru`/`__fdiv_r*`/`__fsqrt_r*`)
  and CPU fp64 (round-to-nearest + error bound, OpenMP). Breadth-first forest with a memory
  cap (levels above 2²⁷ boxes are processed depth-first in chunks). Modes `search`, `export`,
  `split`, `refute`, `sample` (see `v2/mb2.cpp`). Operations: + − × integer powers, **÷ and √**
  with realfp's exact semantics (÷ by an interval containing 0 → whole line; √ clips at 0,
  `hi < 0` → invalid).
* fp32 soundness: box endpoints are dyadic (−1 + k·2⁻ˢ), exact in binary32 while
  s ≤ 23 (the engine stops at 23·d+1 levels); constants are checked to be exact in binary32;
  every operation is directed-rounded, so fp32 enclosures are sound, only wider. The certificate
  format is the same (split bits only), and it is still checked in fp64 by the Lean/C checker.
* `lean/fast/c/mbtape.c`: tape ops 7 (÷ = a·inv b, realfp's `inv`) and 8 (√, realfp's
  `sqrtI` = hull with 0 when lo < 0), via realfp's `iv64_dir_div_*`/`iv64_dir_sqrt_*` kernels;
  new entry point `checkHexAt` (a sub-tree starting at depth l0 and coordinates cs0).
  Agreement with the Lean spec (`fast/bench.sh v2` and `rand`): 0 disagreements on all
  single-bit mutations of the NES/PM certificates (312+312, 1083+1083, 210, 201 cases) and on
  200,000 random expressions using every operation, constants up to 10^±200, boxes up to 10^±300
  (each through both `checkHex` and `checkHexAt`).
* `Top`/`Top.sound` (fast, proved) + `proveTop_le/ge` (ManyBoxCert): a certificate split into
  independent sub-checks, each proved in its own file (own process, possibly another machine),
  glued by kernel computation (`midsOK`, `decide +kernel`) and `rfl` (job list).

### Search times (spark GB10; later repetitions; boxes = evaluated nodes)

| problem (d) | δ | boxes fp64 | fp32 extra | GPU fp64 | GPU fp32 | CPU 20 thr | CPU 1 thr |
|---|---|---|---|---|---|---|---|
| P1 T8+T8 (2) | 1/1024 | 1.64e7 | +1.1% | 26 ms | 14 ms | 0.19 s | 2.0 s |
| P2 Choi–Lam (4) | 1/16 | 3.46e7 | +0.001% | 60 ms | 34 ms | 0.32 s | 3.1 s |
| NES Nesbitt, ÷ (3) | 0.001 | 8.18e7 | +0.04% | 0.128 s | 0.072 s | 0.58 s | 6.1 s |
| PM power means, √ (3) | 0.001 | 4.35e8 | +0.08% | 0.64 s | 0.38 s | 2.53 s | 20.4 s |
| R8 T4 ring (8) | 8 | 3.59e7 | 0 | 0.134 s | 0.053 s | 1.08 s | 11.8 s |
| R8 | 4 | 3.90e8 | 0 | 1.44 s | 0.56 s | 10.7 s | 124 s |
| R8 | 2 | 2.04e9 | 0 | 8.0 s | 3.5 s | 59.9 s | 638 s |
| R8 | 1 | 1.07e10 | 0 | 41.4 s | 17.8 s | 312 s | (~3300 s) |
| M6 Reznick AM–GM (6) | 0.5 | 3.29e8 | 0 | 0.67 s | 0.40 s | 3.95 s | 38.7 s |
| M6 | 0.375 | 1.54e9 | +0.001% | 3.67 s | 2.34 s | 26.0 s | 189 s |
| M6 | 0.25 | 1.33e10 | +0.002% | 30.4 s | 19.1 s | 200 s | |
| C6 Σ T8 (6) | 32 | 2.61e9 | 0 | 9.8 s | 3.8 s | 87.5 s | |

R8 = Σᵢ T4(xᵢ)T4(xᵢ₊₁ mod 8) ≥ −8 − δ; M6 = x₆¹² + P·Σxᵢ² − 6x₆²P ≥ −δ (P = x₁²⋯x₅²);
C6 = Σ T8(xᵢ) ≤ 6 + δ (naive interval T8 is very loose, so C6 needs δ = 32 to stay ≤ 1e10).
The CPU 1-thread R8 δ=1 entry is extrapolated (3.2e6 boxes/s), not run.
fp32 is 1.6–2.6× faster than fp64 on the GB10 (whose fp64 rate is low) and costs at most ~1%
more boxes here; for the polynomial problems with dyadic data the counts are identical. The
fp32 GPU is 7–23× faster than 20 CPU threads (spark: 10 performance + 10 efficiency cores)
and 54–220× faster than one.

### Checking in Lean (box: 8-core x86, AVX-512)

| claim | leaves | how | Lean time | axioms |
|---|---|---|---|---|
| Nesbitt ≥ 3/2 − 1/64 (÷) | 141,007 | `proveT_ge`, C checker | ~6 ms native | std + native_decide |
| power means ≤ 1/64 (√) | 673,837 | `proveT_le`, C checker | 14.6 ms (C, `bench.sh`) | std + native_decide |
| (same two, fp32-searched certificates) | | | same | same |
| R8 ≥ −12 (δ=4) | 1.95e8 | split: 256 jobs in 16 files | 128.5 s (1 proc × 8 thr), 100 s (8 procs × 1 thr) + 4.2 s glue | std + 16 native_decide |
| R8 ≥ −10 (δ=2) | 1.02e9 | split: 4096 jobs in 32 files | 499 s (8 procs × 1 thr) + 29.7 s glue | std + 32 native_decide |
| R8 ≥ −9 (δ=1) | 5.34e9 | split: 65,536 jobs in 256 files, two-level glue; **on the Spark** | 941.6 s (20 procs × 1 thr) + 55.9 s (256 group files) + 3.0 s (final) | std + 256 native_decide |

(`lean/V2DivSqrt.lean`, `lean/split/R8d4/Main.lean`, `lean/split/R8d2/Main.lean`,
`lean/split/R8d1/Hier.lean`; R8 δ=1 log in `results/r8d1_spark.txt`.) The C
checker does about 2·10⁶ R8 leaves/s on 8 cores (the R8 tape has ~70 operations), so checking
is 150–250× slower than the fp32 GPU search: 1e10 leaves ≈ 1.4 h, 1e11 ≈ 14 h on this box. The
practical limit was moving certificates, not checking them: 1 bit per node is 1.3 GB of hex for
R8 δ=1, and the spark → box link ran at ~0.25 MB/s. Splitting removes every other limit: the
sub-files are Mathlib-free, independent, and can be compiled on any number of machines; the
glue (Mathlib) only imports their `ok` theorems.

### R8 ≥ −9 on [−1,1]⁸, proved on the Spark (5.34·10⁹ leaves)

`ManyBox.Split.R8d1.bound2 : ∀ xs, InBoxes xs (cube 8) → (−9 : ℝ) ≤ R8(xs)`; `#print axioms`:
`propext, Classical.choice, Quot.sound` + 256 `…G**.ok._native.native_decide.ax_1_1`; no `sorry`.
Run entirely on the Spark (aarch64, realfp's RN+err kernels; Mathlib copied from an existing
build of the same revision), so the 1.3 GB certificate never moved:

| step | what | wall |
|---|---|---|
| GPU split search | `mb2 split R8 64 1 16` (fp64), 65,536 sub-certificates | 233 s |
| 256 sub-files G** (Mathlib-free) | 256 jobs / 2.09e7 leaves each, `native_decide` → C checker, 20 lean processes × 1 thread | 941.6 s |
| 256 group files H** | subtree term, `midsOK` (kernel), `t.jobs env = G.jobs` (`rfl`), `Top.sound` | 55.9 s |
| Hier.lean (Mathlib) | `TopC.sound` over the 256 groups + realfp `proveC_ge` | 3.0 s |

Checking rate: 5.34e9 leaves / 941.6 s = 5.7·10⁶ leaves/s on 20 cores (2.8·10⁵ per process; 8
cores of the x86 box: ~2·10⁶). The one-level glue (`Main.lean` from gen_split.py: one `Top`
term and one `rfl` over all 65,536 jobs) does not scale: the term took 71 s and 42 GB, and the
`rfl` hit `maxRecDepth`. The two-level glue (`split/TopC.lean`, `split/gen_hier.py`) reuses the
compiled sub-files unchanged. Reproduce (on the machine holding the certificate):

```sh
v2/build/mb2 split R8 64 1 16 certs/split/r8_1
cd lean/split && python3 gen_split.py ../../certs/split/r8_1 R8d1 V2.eR8 false -9 256 \
  && python3 gen_hier.py ../../certs/split/r8_1 R8d1 V2.eR8 false -9 256
./run_split.sh R8d1 20 1          # G files (its one-level Main step fails at this size; ignore)
# then compile split/TopC.lean and R8d1/H*.lean to ../build/olean/split/… and run R8d1/Hier.lean
```

### Weaker than proof (`lean/Weak*.lean`)

* **Counterexample** (`WeakRefute.lean`, standard axioms only): `mb2 refute P1 64 1.9921875`
  finds in 0.3 s a box `[−1/128, 0]²` on which T8(x)+T8(y) > 2 − 1/128 everywhere; Lean checks
  that one box with the kernel (`decide +kernel`) and proves `¬ (∀ x y ∈ [−1,1], T8 x + T8 y ≤
  2 − 1/64)`. Refutations are always cheap to verify: one box, any dimension.
* **Labeled assumption** (`WeakAxiom.lean`): `axiom gpu_R8_ge_neg9` states the δ=1 R8 result,
  with its certificate hash (fnv 893675208e4e9f33) and reproduction command in the docstring;
  `ring_ge'` uses it, and `#print axioms` shows `gpu_R8_ge_neg9`. The gap is explicit and
  machine-visible; anything downstream is "proved modulo this search".
* **Sampled check** (`WeakSample.lean`, standard axioms only, 21 s): 64 leaves drawn uniformly
  from the 5.3e9 leaves of the R8 δ=1 certificate (`mb2 sample`), each re-checked by the
  kernel. What it proves: the bound on the union of those 64 boxes (volume 5.6e−9 of the cube) —
  mathematically almost nothing. What it supports: if a fraction p of the GPU's leaf claims
  were wrong at random, passing 64 samples has probability (1−p)⁶⁴, so p < 4.6% at 95%
  confidence. It cannot detect systematic faults (wrong expression or rounding mode, a
  coverage bug), which only the full check rules out.

(The R8 δ=1 axiom demo is now also proved outright, above; `WeakAxiom.lean` stays as the demo.)

Is a search that cannot be checked worthless? No: (1) a refutation is a proof as soon as one box
is checked; (2) a successful search is strong evidence that pins down the right margin, the
splitting, or where the hard region is, and as a labeled axiom it makes the dependence explicit;
(3) splitting makes the full check embarrassingly parallel, so "infeasible" usually means
"needs N machines for T hours", and the search tells you N and T in advance.

### Trust base (changes in this round)

`native_decide` theorems now also trust: the larger `mbtape.c` (÷, √, `mb_check_tape_at`), the
Lean-side tape builder (`toTape`, with the new ops 7/8) and `checkHexAtImpl`'s guard, plus
realfp's `iv64_dir_div/sqrt` kernels (already trusted by realfp). `Top.sound`, `proveTop_*`, the
refutation and the sampled check are ordinary proofs. The GPU/CPU search code (`v2/`) is never
trusted: its certificates are re-checked, except in `WeakAxiom.lean`, where that is the point.

## Assessment

* **GPU for the search:** on any search above about 10⁵ boxes the GPU is 3–10× faster than all
  20 CPU cores and about 100× faster than one core. With the same algorithm it never gives a
  different answer.
* **With `native_decide` and the C batch checker, GPU bisection now wins end to end** on these
  problems. P1 δ=1/1024 takes 3.6 s per file, against 196 s for `interval (trust := native)`.
  The check is still 25–40× the GPU search.
* **With kernel-only trust, the derivative certificates win.** They are 10³× smaller, and the
  kernel cannot run C (592 s for P1 δ=1/1024).
* **Where a GPU does pay:**
  1. exploration: finding the right δ, the right splitting, or counterexamples over 10⁷–10⁹
     boxes in milliseconds;
  2. problems where derivative methods don't collapse the count: many near-extremal
     points, degenerate (line or surface) minima in 4D and above, or families of many
     independent instances;
  3. combined with a fast trusted checker. The precompiled `checkC3` cut the gap from about
     10⁴× to about 3·10³×, and the C batch checker cuts it to 25–40×. This costs new trusted
     C code under `native_decide`.

## Rerun

```sh
manybox/build.sh                # needs nvcc + gcc with OpenMP; -> build/mbbench, build/mbexport
manybox/build/mbbench           # full table (about 40 s on GB10); `quick` for the small sizes
manybox/make_certs.sh           # certificates for lean/ (p1_d1024 4 MB and p2_d16 8.6 MB are not committed)
(cd manybox/lean/fast && lake build +ManyBoxFast:dynlib +ManyBoxTape:dynlib)   # precompiled + C checker
manybox/lean/run.sh TapeSmall.lean TapeP1d1024.lean    # C checker; Fast*.lean = checkC3, Check*.lean = older
MB_THREADS=1 manybox/lean/run.sh TapeP1d1024.lean      # serial C checker
manybox/lean/run.sh TapeTest.lean                      # C vs Lean spec agreement tests
manybox/lean/fast/bench.sh                             # Mathlib-free bench + agreement (any platform)
manybox/lean/run.sh DerivKernel1024.lean               # realfp `interval` on P1 δ=1/1024 (~12 min)
manybox/v2/build.sh                                    # v2 engine (CXX=g++, NOGPU=1 for CPU only)
manybox/v2/build/mb2 search R8 32 1 gpu                # fp32 GPU search; `cpu20`, `cpu1`; 64 = fp64
manybox/v2/build/mb2 split R8 64 4 8 certs/split/r8_4  # split certificate (not committed: 94 MB)
manybox/lean/split/gen_split.py ../../certs/split/r8_4 R8d4 V2.eR8 false -12 16   # (run in lean/split)
manybox/lean/split/run_split.sh R8d4 8 1               # 8 lean processes × 1 C thread, then Main
manybox/lean/run.sh V2DivSqrt.lean WeakRefute.lean WeakAxiom.lean WeakSample.lean
```
