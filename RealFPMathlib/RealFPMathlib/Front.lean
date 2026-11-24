/-
`realfp`: one front-door tactic for realfp's kernel-checked numerics.

It looks at the goal and routes to the matching backend:

| goal shape                                              | backend         |
|---------------------------------------------------------|-----------------|
| `∃! x ∈ box, f x = 0` / `∃! p, box ∧ equations`         | `root_unique`   |
| `∃ x ∈ box, f x = 0` / `∃ p, box ∧ equations`           | `root_exists`   |
| `M.PosDef` (concrete real matrix, rational entries)     | `pos_def`       |
| anything mentioning `∫ x in a..b, f x`                  | `integral_bound`|
| `f ≤ g`, `f < g`, `f ≠ g`, `f ∈ Icc a b`, `∧`, `∀ x ∈ box` | `interval`   |

Options (any order): `(trust := kernel|native)` (default `kernel`: `decide +kernel`, only the
standard axioms; `native` uses `native_decide` and adds a compiler-trust axiom), and for
`interval`/root goals `(depth := n)`, `(maxBoxes := n)`, `(order := n)`, `(deriv := false)`,
`(chunk := n)`.
-/
import RealFPMathlib.IntervalTactic
import RealFPMathlib.IntegralTactic
import RealFPMathlib.RootTactic
import RealFPMathlib.PosDefTactic

open Lean Meta Elab Tactic

namespace RealFP.Front

/-- `realfp` with options `(trust := kernel|native)`, `(depth := n)`, `(maxBoxes := n)`,
`(order := n)`, `(deriv := false)`, `(chunk := n)`. -/
syntax (name := realfpTac) "realfp" (ppSpace intervalOpt)* : tactic

inductive Route | unique | exists | posDef | integral | interval

def Route.name : Route → String
  | .unique => "root_unique" | .exists => "root_exists" | .posDef => "pos_def"
  | .integral => "integral_bound" | .interval => "interval"

def route (t : Expr) : MetaM Route := do
  let t ← instantiateMVars t
  if t.isAppOf ``ExistsUnique then return .unique
  if t.isAppOf ``Exists then return .exists
  if t.isAppOf ``Matrix.PosDef then return .posDef
  if (t.find? fun e => e.isConstOf ``intervalIntegral).isSome then return .integral
  return .interval

@[tactic realfpTac] def evalRealfp : Tactic := fun stx => withMainContext do
  let opts := stx[1].getArgs
  let mut trust : Name := `inherit
  let mut rest : Array (TSyntax `intervalOpt) := #[]
  for o in opts do
    if o[1].getId == `trust then
      let v := o[3].getId
      unless v == `kernel || v == `native do
        throwErrorAt o "realfp: (trust := {v}) — expected `kernel` (default) or `native`"
      trust := v
    else rest := rest.push ⟨o⟩
  let r ← route (← getMainTarget)
  let run : TacticM Unit := match r with
    | .unique => do evalTactic (← `(tactic| root_unique $rest*))
    | .exists => do evalTactic (← `(tactic| root_exists $rest*))
    | .posDef => do
      unless rest.isEmpty do throwError "pos_def takes only the `trust` option"
      evalTactic (← `(tactic| pos_def))
    | .integral => do
      unless rest.isEmpty do throwError "integral_bound takes only the `trust` option"
      evalTactic (← `(tactic| integral_bound))
    | .interval => do evalTactic (← `(tactic| interval $rest*))
  try
    RealFP.withTrust trust run
  catch ex =>
    let nat := realfp.native.get (← getOptions)
    let tr := if trust == `inherit then (if nat then `native else `kernel) else trust
    throwError "realfp (routed to `{r.name}`, trust := {tr}): {ex.toMessageData}"

end RealFP.Front
