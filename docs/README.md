# realfp documentation

- [Getting started](GETTING_STARTED.md) — install Lean, a C compiler and realfp on Windows 11 (WSL), Linux or macOS from scratch; run the examples; first theorem
- [Tutorial](TUTORIAL.md) — hands-on guide from setup to tactics and certificates; every snippet is compiled
- [Examples](EXAMPLES.md) — five short, self-contained proofs of famous inequalities and constants
- [Reference](REFERENCE.md) — operations, theorem names, kernels, backends, tactics, and [Precision 128](REFERENCE.md#precision-128-precision--128)
- [Comparisons](COMPARISONS.md) — measured comparisons with FloatLib, LeanCert, and two research showcases
- [Limitations](LIMITATIONS.md) — known gaps (not soundness bugs), including the limits of precision 128
- [Soundness](SOUNDNESS.md) — what kernel and native mode trust; axiom audit, tests and CI
- [Philosophy](PHILOSOPHY.md) — design rationale
- [API reference](#api-reference-doc-gen4) — how to generate the browsable doc-gen4 HTML locally

The short project overview and install instructions are in the
[top-level README](../README.md).

## API reference (doc-gen4)

The Lean API docs are generated with [doc-gen4](https://github.com/leanprover/doc-gen4)
from a nested `docbuild/` Lake project, so a normal `lake build` of realfp does not
depend on the documentation generator. `doc-gen4` is pinned to `v4.36.0`, the same
Lean/Mathlib revision as this repository.

```bash
export PATH="$HOME/.elan/bin:$PATH"
# First time, and after changing Lean or Mathlib:
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
# Public libraries: Interval64, Interval128, Interval64Proofs, RealFPMathlib
lake build Interval64:docs Interval128:docs Interval64Proofs:docs RealFPMathlib:docs
```

The site root is `docbuild/.lake/build/doc/index.html`. Opening the files
directly in a browser is only partly functional (same-origin policy); serve
them instead:

```bash
cd docbuild/.lake/build/doc && python3 -m http.server
```

`doc-gen4` also builds HTML for the Lean core (`Init`, `Std`, `Lake`, `Lean`)
and, when documenting `RealFPMathlib`, for Mathlib and the other imported
packages. That output is large and is not committed (`.lake` is gitignored).
On GitHub Actions, a workflow that builds this site and deploys it to GitHub
Pages is kept as a draft until it can be pushed with a `workflow`-scoped
token. The repository is public, so GitHub Pages is available on the free plan.
