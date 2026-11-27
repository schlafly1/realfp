import Lake
open Lake DSL

/-! Compiled part of the manybox Lean check: the certificate decoder and the C-runtime
checker `checkF`. Mathlib-free (it depends only on the realfp core), so it can be built with
`precompileModules := true`: `native_decide` then runs `checkF` as native code instead of in
Lean's IR interpreter. Not part of realfp's `lake build`; build with `lake build` here. The
soundness proof (`checkF_sound`) is in `../ManyBoxCert.lean` (needs Mathlib). -/

package «manyboxfast» where
  moreLeanArgs := #["-DautoImplicit=false"]
  precompileModules := true
  moreLinkArgs := #["-lm"]

require interval64 from "../../../../.."

@[default_target]
lean_lib ManyBoxFast
