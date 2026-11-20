import Lake
open System Lake DSL

package «interval64» where
  -- Core library has no Mathlib dependency.
  moreLeanArgs := #["-DautoImplicit=false"]
  -- So `#eval` / the editor / `native_decide` load compiled modules
  -- (and therefore the `@[implemented_by]` C kernels).
  precompileModules := true
  moreLinkArgs := #["-lm"]

/-- True when Lake runs on x86_64 (the C kernels are built for the host). -/
def isX86_64 : Bool := System.Platform.target.startsWith "x86_64"

/-- Backend selection. Default: AVX-512 on x86_64, RN + exact error term elsewhere
    (aarch64). `lake build -Kbackend=rnerr` forces the portable backend on x86_64
    (for testing it against the Lean spec). -/
def forceRnErr : Bool := (get_config? backend) == some "rnerr"

def cArchArgs : Array String :=
  if isX86_64 then
    -- AVX-512 kernels are compiled on x86 even with -Kbackend=rnerr (used by tests).
    #["-mavx512f", "-mavx512vl"] ++ (if forceRnErr then #["-DIV64_FORCE_RNERR"] else #[])
  else #[]

/-- C kernels: AVX-512 embedded rounding (x86_64) or RN + exact error term
    (aarch64 / other), plus fesetround fallbacks. Compiled with gcc (cc).
    The Lean 4.36 bundled clang is missing immintrin.h. -/
target interval64.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "interval64.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "interval64.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let args := #["-fPIC", "-O2"] ++ cArchArgs ++
    #["-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  -- Headers are part of the trace, so editing them rebuilds the object.
  buildO oFile srcJob weakArgs args "cc" (extraDepTrace := do
    let h1 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_rnerr.h"))
    let h2 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "interval64.h"))
    return h1.mix h2)

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

/-- Enclosure theorems about the Lean spec. Separate from the runtime library
    so the core stays light (and Mathlib-free). -/
lean_lib Interval64Proofs

lean_exe interval64_axioms where
  root := `Interval64Axioms
