import Lake
open System Lake DSL

package «interval64» where
  version := v!"0.1.0"
  description := "Binary64 interval arithmetic with hardware directed rounding (realfp core)"
  license := "Apache-2.0"
  homepage := "https://github.com/schlafly1/realfp"
  -- Core library has no Mathlib dependency.
  moreLeanArgs := #["-DautoImplicit=false"]
  -- So `#eval` / the editor / `native_decide` load compiled modules
  -- (and therefore the `@[implemented_by]` C kernels).
  precompileModules := true
  moreLinkArgs := #["-lm"]

/-- True when Lake runs on x86_64 (the C kernels are built for the host). -/
def isX86_64 : Bool := System.Platform.target.startsWith "x86_64"

/-- Backend selection. Default: AVX-512 on x86_64 machines that support it (asked from
    the C compiler, see `hostHasAvx512`), RN + exact error term elsewhere (aarch64, and
    x86_64 without AVX-512). `lake build -Kbackend=rnerr` or `IV64_BACKEND=rnerr` forces the
    portable backend on x86_64 (for testing it against the Lean spec, and for CI
    on machines without AVX-512). The env var is required when a downstream
    package such as RealFPMathlib builds this one: Lake `-K` options are not
    forwarded to required packages. -/
def forceRnErr : Bool := (get_config? backend) == some "rnerr"

def cArchArgsOf (force : Bool) : Array String :=
  if isX86_64 then
    if force then
      -- No -mavx512f: the object file must not contain AVX-512 instructions,
      -- so the binary runs on any x86_64 (GitHub-hosted runners included).
      -- AVX-512 kernels are therefore not compiled in this configuration;
      -- the default `lake build` on an AVX-512 machine is unchanged.
      #["-DIV64_FORCE_RNERR"]
    else
      #["-mavx512f", "-mavx512vl"]
  else #[]

def cArchArgs : Array String := cArchArgsOf forceRnErr

/-- The C compiler: `$CC` if set, else the first of `cc`, `gcc`, `clang` that runs
    (an error with installation hints if there is none).
    Lean's bundled `clang` cannot be used: the toolchain ships no C library headers
    (`math.h`, `fenv.h`, …), so a system C compiler is required. -/
def cCompiler : IO String := do
  if let some c ← IO.getEnv "CC" then
    if !c.isEmpty then return c
  for c in ["cc", "gcc", "clang"] do
    try
      let out ← IO.Process.output { cmd := c, args := #["--version"] }
      if out.exitCode == 0 then return c
    catch _ => pure ()
  throw <| IO.userError <|
    "realfp needs a C compiler with the C library headers (Lean's bundled clang has none), " ++
    "but none of cc, gcc, clang was found. Install one: Debian/Ubuntu/WSL `sudo apt install " ++
    "build-essential`; Fedora `sudo dnf install gcc`; macOS `xcode-select --install`; or set " ++
    "the CC environment variable. See docs/GETTING_STARTED.md."

/-- Whether the build machine supports AVX-512F, asked from the C compiler
    (`cc -march=native -dM -E`). If the probe fails, answer `false`, so the portable
    backend is used: an AVX-512 build would crash on a CPU without AVX-512.
    `IV64_BACKEND=avx512` skips the probe. -/
def hostHasAvx512 (cc : String) (dir : FilePath) : IO Bool := do
  if !isX86_64 then return false
  if (← IO.getEnv "IV64_BACKEND") == some "avx512" then return true
  try
    IO.FS.createDirAll dir
    let f := dir / "iv64_avx512_probe.c"
    IO.FS.writeFile f "\n"
    let out ← IO.Process.output { cmd := cc, args := #["-march=native", "-dM", "-E", f.toString] }
    return out.exitCode == 0 && (out.stdout.splitOn "__AVX512F__").length > 1
  catch _ => return false

/-- `true` when the portable RN + error-term backend must be used: `-Kbackend=rnerr`,
    `IV64_BACKEND=rnerr`, or an x86_64 machine without AVX-512. -/
def usePortable (cc : String) (dir : FilePath) : IO Bool := do
  if forceRnErr || (← IO.getEnv "IV64_BACKEND") == some "rnerr" then return true
  return isX86_64 && !(← hostHasAvx512 cc dir)

/-- C kernels: AVX-512 embedded rounding (x86_64) or RN + exact error term
    (aarch64 / other), plus fesetround fallbacks. Compiled with gcc (cc).
    The Lean 4.36 bundled clang is missing immintrin.h. -/
target interval64.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "interval64.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "interval64.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let cc ← cCompiler
  let force ← usePortable cc (pkg.buildDir / "c")
  let args := #["-fPIC", "-O2"] ++ cArchArgsOf force ++
    #["-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  -- Headers are part of the trace, so editing them rebuilds the object.
  buildO oFile srcJob weakArgs args cc (extraDepTrace := do
    let h1 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_rnerr.h"))
    let h2 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "interval64.h"))
    return h1.mix h2)

/-- Interval128 C kernels (double-double; same backend selection as Interval64). -/
target interval128.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "interval128.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "interval128.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let cc ← cCompiler
  let force ← usePortable cc (pkg.buildDir / "c")
  let args := #["-fPIC", "-O2"] ++ cArchArgsOf force ++ (if isX86_64 then #["-mfma"] else #[]) ++
    #["-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  buildO oFile srcJob weakArgs args cc (extraDepTrace := do
    let h1 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_rnerr.h"))
    let h2 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "interval128.h"))
    return h1.mix h2)

/-- Interval64 matrix / polynomial kernels (same backend selection). -/
target iv64_matrix.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "iv64_matrix.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "iv64_matrix.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let cc ← cCompiler
  let force ← usePortable cc (pkg.buildDir / "c")
  let args := #["-fPIC", "-O2"] ++ cArchArgsOf force ++ (if isX86_64 then #["-mfma"] else #[]) ++
    #["-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  buildO oFile srcJob weakArgs args cc (extraDepTrace := do
    let h1 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_rnerr.h"))
    let h2 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "interval128.h"))
    let h3 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_matrix.h"))
    return (h1.mix h2).mix h3)

/-- Polynomial / Bernstein / quadrature kernels (`c/iv64_poly.{h,c}`, `c/iv64_quad.h`). -/
target iv64_poly.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "iv64_poly.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "iv64_poly.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let cc ← cCompiler
  let force ← usePortable cc (pkg.buildDir / "c")
  let args := #["-fPIC", "-O2"] ++ cArchArgsOf force ++ (if isX86_64 then #["-mfma"] else #[]) ++
    #["-ffp-contract=off", "-frounding-math", "-fno-math-errno"]
  buildO oFile srcJob weakArgs args cc (extraDepTrace := do
    let h1 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_rnerr.h"))
    let h2 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "interval128.h"))
    let h3 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_matrix.h"))
    let h4 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_poly.h"))
    let h5 : BuildTrace ← computeTrace (TextFilePath.mk (pkg.dir / "c" / "iv64_quad.h"))
    return (((h1.mix h2).mix h3).mix h4).mix h5)

/-- Flags for the CORE-MATH objects (correctly rounded in the current rounding
    mode; must not be contracted or constant-folded across mode switches). -/
def coreMathArgs : Array String :=
  #["-fPIC", "-O2", "-frounding-math", "-ffp-contract=off", "-fno-math-errno"] ++
    (if isX86_64 then #["-mfma"] else #[])

/-- Compile one C file of the transcendental part (CORE-MATH or its wrapper). -/
def transcObj (pkg : Package) (src : String) (obj : String) : FetchM (Job FilePath) := do
  let oFile := pkg.buildDir / "c" / obj
  let srcJob ← inputTextFile <| pkg.dir / "c" / src
  buildO oFile srcJob #["-I", (← getLeanIncludeDir).toString] coreMathArgs (← cCompiler)
    (extraDepTrace := computeTrace (TextFilePath.mk (pkg.dir / "c" / "coremath" / "dint.h")))

target cm_exp.o pkg : FilePath := transcObj pkg "coremath/exp.c" "cm_exp.o"
target cm_log.o pkg : FilePath := transcObj pkg "coremath/log.c" "cm_log.o"
target cm_sin.o pkg : FilePath := transcObj pkg "coremath/sin.c" "cm_sin.o"
target cm_cos.o pkg : FilePath := transcObj pkg "coremath/cos.c" "cm_cos.o"
target cm_atan.o pkg : FilePath := transcObj pkg "coremath/atan.c" "cm_atan.o"
target cm_atan2.o pkg : FilePath := transcObj pkg "coremath/atan2.c" "cm_atan2.o"
target cm_tan.o pkg : FilePath := transcObj pkg "coremath/tan.c" "cm_tan.o"
target cm_asin.o pkg : FilePath := transcObj pkg "coremath/asin.c" "cm_asin.o"
target cm_acos.o pkg : FilePath := transcObj pkg "coremath/acos.c" "cm_acos.o"
target cm_sinh.o pkg : FilePath := transcObj pkg "coremath/sinh.c" "cm_sinh.o"
target cm_cosh.o pkg : FilePath := transcObj pkg "coremath/cosh.c" "cm_cosh.o"
target cm_tanh.o pkg : FilePath := transcObj pkg "coremath/tanh.c" "cm_tanh.o"
target cm_log2.o pkg : FilePath := transcObj pkg "coremath/log2.c" "cm_log2.o"
target cm_log10.o pkg : FilePath := transcObj pkg "coremath/log10/log10.c" "cm_log10.o"
target cm_pow.o pkg : FilePath := transcObj pkg "coremath/pow/pow.c" "cm_pow.o"
target iv64_transc.o pkg : FilePath := transcObj pkg "iv64_transc.c" "iv64_transc.o"

/-- Static library of the C kernels. Lake links this into executables and
    dependents, and builds a shared object for `precompileModules` / `#eval`.
    (`extern_lib` is deprecated in Lake 4.36 but is still the supported way to
    expose a C library to module dynlibs; `moreLinkObjs` is not linked into
    per-module dynlibs.) -/
extern_lib libleaninterval64 pkg := do
  let oFile ← interval64.o.fetch
  let objs := #[oFile, ← cm_exp.o.fetch, ← cm_log.o.fetch, ← cm_sin.o.fetch, ← cm_cos.o.fetch,
    ← cm_atan.o.fetch, ← cm_atan2.o.fetch,
    ← cm_tan.o.fetch, ← cm_asin.o.fetch, ← cm_acos.o.fetch, ← cm_sinh.o.fetch, ← cm_cosh.o.fetch,
    ← cm_tanh.o.fetch, ← cm_log2.o.fetch, ← cm_log10.o.fetch, ← cm_pow.o.fetch,
    ← iv64_transc.o.fetch, ← interval128.o.fetch, ← iv64_matrix.o.fetch,
    ← iv64_poly.o.fetch]
  let name := nameToStaticLib "leaninterval64"
  buildStaticLib ((pkg : Package).staticLibDir / name) objs

@[default_target]
lean_lib Interval64

@[default_target]
lean_lib Interval128

-- C code comes from `extern_lib libleaninterval64`, so executables must not
-- also list `moreLinkObjs` (that would duplicate symbols).
lean_exe interval64_tests where
  root := `Interval64Test
  moreLeancArgs := #["-O3"]

lean_lib Interval128Tests

lean_lib Interval128DyTests

/-- Lean-only reference copies of the C-backed specifications (tests, benchmarks). -/
lean_lib Interval64CSpec

lean_exe interval128_tests where
  root := `Interval128Test
  moreLeancArgs := #["-O3"]

/-- Micro-benchmarks (experimental; not part of the library). -/
lean_exe interval64_bench where
  srcDir := "experimental"
  root := `Interval64Bench
  moreLeancArgs := #["-O3"]

/-- `native_decide` demo from the prototype (experimental; not part of the library). -/
lean_exe interval64_native where
  srcDir := "experimental"
  root := `Interval64Native

/-- Enclosure theorems about the Lean spec. Separate from the runtime library
    so the core stays light (and Mathlib-free). -/
lean_lib Interval64Proofs

lean_exe interval64_axioms where
  root := `Interval64Axioms
