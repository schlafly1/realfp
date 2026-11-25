# Contributing to realfp

Thanks for your interest. Bug reports, examples, new functions and
performance work are all welcome. Soundness comes first: a change that could
let the library prove a false statement will not be merged, however fast it is.
[docs/SOUNDNESS.md](docs/SOUNDNESS.md) explains how soundness is maintained;
please read it before changing a checker, a kernel mirror or the C runtime.

## Reporting a bug

Open an issue with a minimal `.lean` file, the output, `lean --version`, your
CPU architecture and the backend (AVX-512 or portable `rnerr`).

**Soundness bugs** (realfp proves something false, or a kernel-mode proof
depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`)
are the highest priority. Please say so in the title.

## Building and testing

Requirements: [elan](https://github.com/leanprover/elan), `git`, and a C
compiler (`gcc` as `cc` on x86-64; the AVX-512 backend needs AVX-512F, or
build the portable backend with `IV64_BACKEND=rnerr`).

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build                                   # core library, proofs
lake build interval64_tests interval128_tests
lake exe interval64_tests && lake exe interval128_tests
scripts/check_axioms.sh                      # core axiom check
cd RealFPMathlib
lake exe cache get                           # prebuilt Mathlib
lake build                                   # Mathlib layer, examples, full axiom audit
cd .. && python3 scripts/check_tutorial_snippets.py
```

The full `RealFPMathlib` build compiles all examples and takes a while; for a
quicker loop use `lake build RealFPMathlib.AxiomAuditCore` (the library, tests,
and the short showcase examples in `docs/EXAMPLES.md`, but not the slower
feature examples), which is what CI runs on every push.

To generate the browsable API reference (doc-gen4):

```bash
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4   # first time, or after a Lean/Mathlib bump
lake build Interval64:docs Interval128:docs Interval64Proofs:docs RealFPMathlib:docs
```

The HTML is written to `docbuild/.lake/build/doc/` (gitignored). Serve it with
`python3 -m http.server` from that directory; see [docs/README.md](docs/README.md).

## Rules for changes

- **No `sorry`, no new axioms.** The default build runs the axiom audit and
  fails otherwise. Theorems that use `native_decide` belong under
  `RealFP.Demo.*` or `RealFP.Examples.*` only.
- **Tactics default to kernel checking.** A new tactic or backend must close its
  goals with `decide +kernel` (or an equivalent kernel term) unless the user
  passes `trust := native`.
- **Untrusted search, trusted check.** Heuristics and search may do anything;
  the checker that the proof relies on must be a plain Lean function with a
  soundness theorem.
- **C kernels must match their Lean specification bit for bit.** If you add or
  change an `@[implemented_by]` kernel, add cases to `Interval64Test.lean` or
  `Interval128Tests.lean`, and test both backends (`-Kbackend=rnerr`).
- **Kernel mirrors must be proved equal to the specification** (see
  `Interval64Proofs/KernelEq.lean`).
- **Tutorial snippets are compiled.** If you edit `docs/TUTORIAL.md`, update
  `RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean` to match, and run
  `scripts/check_tutorial_snippets.py`.
- The short showcase examples in `RealFPMathlib/Examples/` are listed in
  `docs/EXAMPLES.md`. New ones should be self-contained, kernel-checked, and
  elaborate in well under 30 s.
- New functions for the tactics go through the extension registry
  (`RealFPMathlib/Registry.lean`); see "Adding a function" in the tutorial.
- Keep prototypes and benchmarks out of the library; `experimental/` is the
  place for them.

## Pull requests

Keep each pull request to one topic, describe what it changes and how you
tested it, and make sure CI is green. By contributing you agree that your
contribution is licensed under the Apache License 2.0, the license of this
project (see [LICENSE](LICENSE)).
