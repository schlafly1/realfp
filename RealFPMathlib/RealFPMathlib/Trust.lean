/-
Trust switch shared by realfp's tactics.

By default every Boolean certificate check is closed by `decide +kernel`: the Lean kernel
evaluates the check, and the theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`. With `set_option realfp.native true` (or `realfp (trust := native)`), the checks
are closed by `native_decide` instead: faster for large certificates, but the proof then also
trusts the Lean compiler and the compiled code (`#print axioms` shows a `native_decide` axiom).
-/
import Lean

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

/-- Run `k` with the trust option given by an identifier (`kernel` or `native`). -/
def withTrust {α} (v : Name) (k : TacticM α) : TacticM α := do
  let native ← match v with
    | `kernel => pure false
    | `native => pure true
    | _ => throwError "trust must be `kernel` (default) or `native`, got `{v}`"
  withOptions (fun o => realfp.native.set o native) k

end RealFP
