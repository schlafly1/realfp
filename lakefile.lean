import Lake
open System Lake DSL

package «interval64» where
  -- Core library has no Mathlib dependency.
  moreLeanArgs := #["-DautoImplicit=false"]

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

@[default_target]
lean_lib Interval64

-- moreLinkObjs only on the executables (not also on the lib) so the
-- C object is linked once.
lean_exe interval64_tests where
  root := `Interval64Test
  moreLinkObjs := #[interval64.o]
  moreLeancArgs := #["-O3"]
  moreLinkArgs := #["-lm"]

lean_exe interval64_bench where
  root := `Interval64Bench
  moreLinkObjs := #[interval64.o]
  moreLeancArgs := #["-O3"]
  moreLinkArgs := #["-lm"]
