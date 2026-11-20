import Lake
open System Lake DSL

package «interval64» where
  -- Core library has no Mathlib dependency.
  moreLeanArgs := #["-DautoImplicit=false"]
  -- So `#eval` / the editor / `native_decide` load compiled modules
  -- (and therefore the `@[implemented_by]` C kernels).
  precompileModules := true
  moreLinkArgs := #["-lm"]

/-- C kernels: AVX-512 embedded rounding + fesetround fallback.
    Compiled with gcc (cc). The Lean 4.36 bundled clang is missing immintrin.h. -/
target interval64.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "interval64.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "interval64.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let args := #[
    "-fPIC", "-O2",
    "-mavx512f", "-mavx512vl",
    "-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  buildO oFile srcJob weakArgs args "cc"

/-- Static library of the C kernels. Lake links this into executables and
    dependents, and builds a shared object for `precompileModules` / `#eval`.
    (`extern_lib` is deprecated in Lake 4.36 but is still the supported way to
    expose a C library to module dynlibs; `moreLinkObjs` is not linked into
    per-module dynlibs.) -/
extern_lib libleaninterval64 pkg := do
  let oFile ← interval64.o.fetch
  let name := nameToStaticLib "leaninterval64"
  buildStaticLib ((pkg : Package).staticLibDir / name) #[oFile]

@[default_target]
lean_lib Interval64

-- C code comes from `extern_lib libleaninterval64`, so executables must not
-- also list `moreLinkObjs` (that would duplicate symbols).
lean_exe interval64_tests where
  root := `Interval64Test
  moreLeancArgs := #["-O3"]

lean_exe interval64_bench where
  root := `Interval64Bench
  moreLeancArgs := #["-O3"]

lean_exe interval64_native where
  root := `Interval64Native
