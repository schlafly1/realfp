# How realfp stays sound

A theorem proved with realfp should be exactly as trustworthy as any other
Lean + Mathlib theorem, unless you ask for more speed with `trust := native`.
This page explains how that is arranged and what each mode trusts.

## The design: spec in Lean, speed in C, checking in the kernel

Every directed-rounding operation (`addDown`, `mulUp`, `sqrtDown`, the
transcendental bounds, …) is a **plain Lean definition**: a computable software
implementation of IEEE 754 binary64 rounding toward −∞ or +∞
(`Interval64/Spec.lean`, built on Lean's `Float.Model`). The C kernels in `c/`
are attached to these definitions with `@[implemented_by]`, so **compiled code**
(`#eval`, the certificate search inside the tactics, `native_decide`) runs the C
version, while the **kernel** only ever sees the Lean definition.

The tactics split each proof in two:

1. **Search (untrusted).** Compiled code, using the fast C kernels, looks for a
   certificate: a bisection tree, derivative signs, a Krawczyk box, a
   quadrature partition, an `LDLᵀ` factor, and so on. A bug here can only make
   the tactic fail; it cannot produce a false theorem.
2. **Check (trusted).** A Boolean checker, proved sound in Lean/Mathlib, is run
   on the certificate. By default the check is `decide +kernel` (or an
   equivalent `eagerReduce` term), so the Lean kernel evaluates it.

To make kernel checking fast, the kernel uses `Nat`-level mirrors of the
operations (`KF` for scalars, `KI` for intervals, `Interval128.Dy` for 128-bit
dyadic intervals). These are **proved equal** to the specification
(`Interval64Proofs/KernelEq.lean`, `KernelFloat.lean`, `KernelInterval.lean`,
and `RealFPMathlib/I128*.lean`), so speed costs nothing in trust.

## Kernel mode (the default)

`realfp`, `interval`, `root_exists`, `root_unique`, `integral_bound`,
`pos_def` and the optimisation tactics default to `trust := kernel`. The
resulting theorem depends only on Lean's three standard axioms:

```
propext, Classical.choice, Quot.sound
```

**What you trust:** the Lean kernel (including its GMP-accelerated `Nat`
arithmetic, which every Lean user already trusts), and that Mathlib's
definitions (`Real.exp`, `∫`, `Matrix.PosDef`, …) mean what you think they
mean. You do **not** trust the C code, the C compiler, the Lean compiler, the
CPU's floating-point unit, or realfp's search code.

## Native mode (`trust := native`, opt in)

`realfp (trust := native)` (or `set_option realfp.native true`) closes the
same Boolean check with `native_decide` instead. The check then runs as compiled
code, which can be much faster on large certificates. `#print axioms` shows the
extra axiom that `native_decide` generates (`…._native.native_decide.ax_…` in
Lean 4.36). The proof then additionally trusts:

- **The Lean compiler** and the **C compiler** (gcc, with
  `-frounding-math -ffp-contract=off -fno-math-errno`) that build the checker.
- **`@[implemented_by]` correctness:** that each C kernel returns exactly
  what its Lean specification returns. Lean does not check this. realfp
  tests it (below), but it is not proved.
- **The C runtime's environment:** correctly rounded hardware `+ − × ÷ √` and
  `fma`; for the portable backend, round-to-nearest as the thread's default mode
  and no flush-to-zero (the Linux defaults; Lean never changes them).
- **CORE-MATH** (`c/coremath/`, unmodified upstream code): that its functions
  are correctly rounded in the current rounding mode. realfp's transcendental
  bounds run them with the rounding mode set toward −∞ or +∞
  (`c/iv64_transc.c`).
- That the shared library Lake loads is the one built from these sources.

Native mode is meant for very large certificates (for example the four-body
showcase). Everything in the library itself, and every tactic default, is
kernel-checked.

## The axiom audit

Every build checks axioms mechanically:

- **Mathlib layer.** `RealFPMathlib/AxiomAudit.lean` is part of the default
  `lake build`. It walks **every** `RealFP.*` theorem and fails the build if one
  depends on anything other than `propext`, `Classical.choice` and
  `Quot.sound`. `sorryAx` is never allowed. Only theorems under `RealFP.Demo.*`
  and `RealFP.Examples.*` may also use `native_decide`, and the report counts
  them. `RealFPMathlib/AxiomAuditCore.lean` is the same check without the slow
  example files; CI runs it on every push.
- **Core library.** `scripts/check_axioms.sh` runs every `#print axioms` in
  `Interval64Axioms.lean`, checks the count, and fails on `sorryAx` or any
  non-standard axiom other than generated `native_decide` axioms. In the core,
  only the two demo theorems in `Interval64/NativeDecide.lean` use
  `native_decide`; everything else, including the kernel-mirror equalities,
  uses the standard axioms only.

To check a theorem of your own, use `#print axioms myTheorem`.

## Testing what is not proved

The C runtime is a trust assumption only in native mode, but it is tested
heavily because the search depends on it for completeness and because native
mode depends on it for soundness:

- `lake exe interval64_tests` and `lake exe interval128_tests` compare the C
  kernels with the Lean specification **bit for bit** on random, special
  (signed zeros, subnormals, overflow, NaN, infinities) and hard cases, and
  check enclosures against exact rationals.
- `tests/test_rnerr.c` compares the portable backend with AVX-512 and with an
  `fesetround` reference; `scripts/test_arm64_qemu.sh` runs it for aarch64
  under qemu.
- `tests/test_transc.c` and `tests/test_func.c` check the transcendental bounds
  against high-precision mpmath oracles (`tests/*_oracle.txt`, generated by
  `scripts/gen_*_oracle.py`).
- `RealFPMathlib/Tests/KernelNativeAgree.lean` is a regression test that the
  kernel and compiled evaluations of a checker agree, and that a bound just past
  the true enclosure is rejected in both modes.

## Continuous integration

GitHub Actions (`.github/workflows/ci.yml`) runs on every push and pull request
to `main`: it builds the core library and proofs, runs both test executables,
runs `scripts/check_axioms.sh`, builds `RealFPMathlib.AxiomAuditCore` (which
elaborates the whole library, Demo and Tests), and checks that every tutorial
snippet compiles. `.github/workflows/examples.yml` builds all examples and the
full axiom audit weekly and on demand. GitHub's runners may lack AVX-512, so CI
builds the portable backend; both backends are bit-identical to the
specification.

## What realfp does not protect against

- A theorem statement that does not say what you meant. Read the statement.
- Bugs in the Lean kernel or in Mathlib's definitions (shared by all Lean
  users).
- In native mode only: the items listed under *Native mode* above.

If you find a theorem that realfp proves but that is false, please report it
as a soundness bug; see [CONTRIBUTING](../CONTRIBUTING.md).
