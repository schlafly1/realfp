# docbuild

Nested Lake project that generates the realfp API reference with
[doc-gen4](https://github.com/leanprover/doc-gen4). It is separate from the
core and `RealFPMathlib` packages so ordinary users do not have to download
doc-gen4.

doc-gen4 is pinned to `v4.36.0` in `lakefile.toml`, matching
`lean-toolchain` and Mathlib. The `packagesDir` is
`../RealFPMathlib/.lake/packages`, so Mathlib is shared with the Mathlib
layer rather than cloned a second time.

```bash
export PATH="$HOME/.elan/bin:$PATH"
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4   # first time, or after a Lean/Mathlib bump
lake build Interval64:docs Interval128:docs Interval64Proofs:docs RealFPMathlib:docs
```

The site root is `.lake/build/doc/index.html`. Serve that directory with
`python3 -m http.server`. See also [docs/README.md](../docs/README.md#api-reference-doc-gen4).
