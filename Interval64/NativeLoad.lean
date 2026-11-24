/-
Diagnostics for running realfp outside Lake.

`lake build`, `lake lean` and the editor start `lean` with realfp's compiled code loaded
(`--load-dynlib …/libleaninterval64.so --plugin …/libinterval64_Interval64.so`). Plain `lean`
and `lake env lean` do not, and the first call of a C kernel fails with
"Could not find native implementation of external declaration …" (inside a tactic this can
abort the whole process). `nativeOk` is a cheap probe the tactics evaluate first (through
`evalConst`, which turns the failure into an ordinary error), and `loadFlags` prints the
exact flags that make plain `lean` work. Display/diagnostics only; nothing here affects proofs.
-/
import Interval64.Directed

namespace Interval64.NativeLoad

/-- Calls a C kernel; evaluating it fails if the compiled code is not loaded. -/
def nativeOk : Bool := Interval64.Directed.backendOk ()

/-- Shared-library file name on this platform. -/
def sharedLib (stem : String) : String :=
  if System.Platform.isWindows then s!"{stem}.dll"
  else if System.Platform.isOSX then s!"lib{stem}.dylib"
  else s!"lib{stem}.so"

/-- The `lean` flags that load realfp's compiled code, found next to the `LEAN_PATH` entries
(`<pkg>/.lake/build/lib/lean` → `<pkg>/.lake/build/lib/`). `none` if not found. -/
def loadFlags : IO (Option String) := do
  let some lp ← IO.getEnv "LEAN_PATH" | return none
  let sep := if System.Platform.isWindows then ";" else ":"
  for entry in lp.splitOn sep do
    if entry.isEmpty then continue
    let some dir := (System.FilePath.mk entry).parent | continue
    let ext := dir / sharedLib "leaninterval64"
    let p64 := dir / sharedLib "interval64_Interval64"
    if (← ext.pathExists) && (← p64.pathExists) then
      return some s!"--load-dynlib={ext} --plugin={p64}"
  return none

end Interval64.NativeLoad
