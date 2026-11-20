import Lake
open Lake DSL

/-! Optional Mathlib layer for Interval64 (realfp).

The core package (`..`) stays Mathlib-free. This package depends on both the
core and Mathlib and restates the core theorems over `ℝ`.

Mathlib must be built for exactly the same Lean version as the core
(`lean-toolchain` here and in `..` must agree); the Mathlib tag below matches
`leanprover/lean4:v4.36.0`. Upgrade both together. -/

package «realfp_mathlib» where
  moreLeanArgs := #["-DautoImplicit=false"]
  -- No `precompileModules` here: that would compile Mathlib to native code.
  -- The core package precompiles its own modules, so importing `Interval64`
  -- still loads the C kernels for `#eval` / `native_decide`.
  moreLinkArgs := #["-lm"]
  -- Our files are not `module`s (the core is not), so silence Lake's
  -- "imports Mathlib, which is designed for the module system" warning.
  allowNonModules := true

require interval64 from ".."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

/-- `import RealFPMathlib` gives `Basic`, `Mem`, `Tight`. `RealFPMathlib.Demo`
    (uses `native_decide`) is built and checked but not imported by the root. -/
@[default_target]
lean_lib RealFPMathlib where
  globs := #[.andSubmodules `RealFPMathlib]
