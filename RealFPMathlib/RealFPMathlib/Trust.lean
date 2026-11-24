/-
Trust switch shared by realfp's tactics.

By default every Boolean certificate check is closed by `decide +kernel`: the Lean kernel
evaluates the check, and the theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`. With `set_option realfp.native true` (or `realfp (trust := native)`), the checks
are closed by `native_decide` instead: faster for large certificates, but the proof then also
trusts the Lean compiler and the compiled code (`#print axioms` shows a `native_decide` axiom).
-/
import Lean
import Interval64.NativeLoad

open Lean Elab Tactic

register_option realfp.native : Bool := {
  defValue := false
  descr := "realfp tactics: close certificate checks with `native_decide` (trusts the compiler) \
    instead of `decide +kernel` (default, kernel-only)" }

namespace RealFP

/-- Close the main goal `check = true` with `decide +kernel`, or `native_decide` when
`realfp.native` is set. -/
def closeCheck : TacticM Unit := do
  if realfp.native.get (← getOptions) then
    evalTactic (← `(tactic| native_decide))
  else
    evalTactic (← `(tactic| decide +kernel))

/-- Run `k` with the trust option given by an identifier (`kernel` or `native`); `inherit`
(the tactics' default when no `trust` option is given) keeps the current `realfp.native`. -/
def withTrust {α} (v : Name) (k : TacticM α) : TacticM α := do
  if v == `inherit then return ← k
  let native ← match v with
    | `kernel => pure false
    | `native => pure true
    | _ => throwError "trust must be `kernel` (default) or `native`, got `{v}`"
  withOptions (fun o => realfp.native.set o native) k

open Meta in
unsafe def requireNativeImpl : MetaM Unit := do
  match (← getEnv).evalConst Bool (← getOptions) ``Interval64.NativeLoad.nativeOk with
  | .ok _ => pure ()
  | .error err =>
    let flags ← Interval64.NativeLoad.loadFlags
    let how := match flags with
      | some f => s!" With plain `lean` / `lake env lean`, pass: {f}"
      | none => ""
    let first := (toString err).splitOn "\n" |>.headD ""
    throwError m!"realfp: the compiled realfp code (C kernels) is not loaded in this Lean \
      process, so the certificate search cannot run ({first}). Run Lean through Lake: the \
      editor, `lake build`, or `lake lean File.lean`.{how}"

/-- Fail with a clear message (instead of aborting the process) if realfp's compiled code is
not loaded, e.g. under plain `lean` or `lake env lean`. -/
@[implemented_by requireNativeImpl]
opaque requireNative : MetaM Unit

end RealFP
