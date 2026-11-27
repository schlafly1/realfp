import Lake
open System Lake DSL

/-! Compiled part of the manybox Lean check: the certificate decoder, the precompiled
checker `checkC3`, and the C batch checker `checkHex` (`c/mbtape.c`). Mathlib-free (it
depends only on the realfp core), so it can be built with `precompileModules := true`:
`native_decide` then runs these functions as native code. Not part of realfp's `lake build`;
build here with `lake build +ManyBoxFast:dynlib +ManyBoxTape:dynlib`. The soundness proofs
are in `../ManyBoxCert.lean` (needs Mathlib). -/

package «manyboxfast» where
  moreLeanArgs := #["-DautoImplicit=false"]
  precompileModules := true
  moreLinkArgs := #["-lm"]

require interval64 from "../../../../.."

/-- The C batch checker. No backend flags: it calls realfp's `iv64_dir_*` kernels (from
    `libleaninterval64`), so it uses whatever backend the core was built with. -/
target mbtape.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "mbtape.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "mbtape.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs
    #["-fPIC", "-O2", "-ffp-contract=off", "-frounding-math", "-fno-math-errno"] "cc"

extern_lib libmbtape pkg := do
  let o ← fetch <| pkg.target ``mbtape.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "mbtape") #[o]

@[default_target]
lean_lib ManyBoxFast where
  roots := #[`ManyBoxFast, `ManyBoxTape]

