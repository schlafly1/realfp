import RealFPMathlib.IntervalTactic
import RealFPMathlib.IntegralTactic
import RealFPMathlib.RootTactic
import RealFPMathlib.PosDefTactic
import RealFPMathlib.OptTactic

/-!
`realfp`: one front-door tactic for realfp's kernel-checked numerics.

It looks at the goal and routes to the matching backend:

| goal shape                                              | backend         |
|---------------------------------------------------------|-----------------|
| `P ∧ Q`                                                 | each side       |
| `∃! x ∈ box, f x = 0` / `∃! p, box ∧ equations`         | `root_unique`   |
| `∃ x ∈ box, f x = 0` / `∃ p, box ∧ equations`           | `root_exists`   |
| `∃ m : ℚ, ∀ x ∈ box, m ≤ f x` (or `f x ≤ m`, `m : ℝ`)   | discovery (B&B) |
| `∃ x ∈ box, ∀ y ∈ box', f x ≤ f y` (argmin/argmax)      | compactness     |
| `∃ x ∈ box, f x ≤ c` (inequalities, no equations)       | witness (B&B)   |
| `m ≤ sInf (f '' box)`, `sInf … ≤ M`, `sSup …`, `|sInf … - v| ≤ ε` | `sInf` lemmas + the above |
| `M.PosDef` (concrete real matrix, rational entries)     | `pos_def`       |
| anything mentioning `∫ x in a..b, f x`                  | `integral_bound`|
| `f ≤ g`, `f < g`, `f ≠ g`, `f ∈ Icc a b`, `∧`, `∀ x ∈ box` | `interval`   |

See `RealFPMathlib/OptTactic.lean` for the optimisation forms and `#realfp_min`/`#realfp_max`.

Options (any order): `(trust := kernel|native)` (default `kernel`: `decide +kernel`, only the
standard axioms; `native` uses `native_decide` and adds a compiler-trust axiom), and for
`interval`/root/optimisation goals `(depth := n)`, `(maxBoxes := n)`, `(order := n)`,
`(deriv := false)`, `(chunk := n)`, `(precision := 64|128)` (128: 128-bit dyadic
endpoints), and for `≤`/`≥` bounds `(touch := [p₁, …])` (interior touching points). Integrals take `order` (Taylor order 2/4/6/8; at precision 128 the Taylor-model
order 8–30), `maxBoxes` (cells) and `precision` (128: fixed-point Taylor models with a per-product certificate, `I128TMF.lean`); `pos_def` takes `trust` and `precision` (128: exact rational check). An option a backend cannot use is an error.
-/

open Lean Meta Elab Tactic

namespace RealFP.Front

/-- `realfp` with options `(trust := kernel|native)`, `(depth := n)`, `(maxBoxes := n)`,
`(order := n)`, `(deriv := false)`, `(chunk := n)`, `(precision := 64|128)`, `(touch := [p₁, …])`. -/
syntax (name := realfpTac) "realfp" (ppSpace intervalOpt)* : tactic

/-- Which backend `realfp` should call for the current goal. -/
inductive Route | conj | unique | exists | witness | discover | argmin | infsup | posDef | integral
  | interval

/-- Short name of a route, used in error messages (`interval`, `root_unique`, …). -/
def Route.name : Route → String
  | .conj => "∧" | .unique => "root_unique" | .exists => "root_exists" | .witness => "witness"
  | .discover => "discovery" | .argmin => "argmin" | .infsup => "sInf/sSup"
  | .posDef => "pos_def" | .integral => "integral_bound" | .interval => "interval"

/-- Does `t` contain an equation between reals? -/
def hasRealEq (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  return (t.find? fun s => s.isAppOfArity ``Eq 3 && s.appFn!.appFn!.appArg!.isConstOf ``Real).isSome

def existsRoute (t : Expr) : MetaM Route := do
  let (``Exists, #[ty, p]) := t.getAppFnArgs | return .exists
  let tyW ← whnfR ty
  if tyW.isConstOf ``Rat || tyW.isConstOf ``Real then
    let isPi ← withLocalDeclD `m ty fun m => do
      let b ← whnfR (← instantiateMVars (p.beta #[m]))
      return b.isForall
    if isPi then return .discover
  if ← hasRealEq t then return .exists
  if (← RealFP.Opt.argGoal? t).isSome then return .argmin
  return .witness

def route (t : Expr) : MetaM Route := do
  let t ← instantiateMVars t
  if t.isAppOf ``And then return .conj
  if t.isAppOf ``ExistsUnique then return .unique
  if t.isAppOf ``Exists then return ← existsRoute t
  if t.isAppOf ``Matrix.PosDef then return .posDef
  if (t.find? fun e => e.isConstOf ``intervalIntegral).isSome then return .integral
  if RealFP.Opt.mentionsInfSup t then return .infsup
  return .interval

partial def realfpCore (rest : Array (TSyntax `intervalOpt)) : TacticM Unit := withMainContext do
  let r ← route (← getMainTarget)
  let each : TacticM Unit := do
    let gs ← getGoals
    let mut acc := #[]
    for g in gs do
      setGoals [g]
      realfpCore rest
      acc := acc ++ (← getGoals)
    setGoals acc.toList
  -- `(precision := 128)` is passed on to every backend (all of them implement it)
  let rest := if r matches .interval | .unique | .exists then rest else
    rest.filter fun o => !(o.raw[1].getId == `precision && o.raw[3].isNatLit? == some 64)
  if !(r matches .interval | .conj | .infsup) &&
      rest.any (fun o => o.raw.getKind == ``RealFP.IntervalTactic.touchOpt) then
    throwError "(touch := _) applies to `≤` / `≥` bounds (the `interval` backend), not to a \
      `{r.name}` goal"
  try
    match r with
    | .conj =>
      let main ← getMainGoal
      let others := (← getGoals).tail
      setGoals [main]
      evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
      each
      setGoals ((← getGoals) ++ others)
    | .unique => evalTactic (← `(tactic| root_unique $rest*))
    | .exists => evalTactic (← `(tactic| root_exists $rest*))
    | .witness => RealFP.Opt.proveWitness (rest.any fun o => o.raw[1].getId == `precision &&
        o.raw[3].isNatLit? == some 128)
    | .discover => RealFP.Opt.proveDiscover rest
    | .argmin => RealFP.Opt.proveArg rest
    | .infsup =>
      let main ← getMainGoal
      let others := (← getGoals).tail
      setGoals [main]
      RealFP.Opt.reduceInfSup
      each
      setGoals ((← getGoals) ++ others)
    | .posDef => evalTactic (← `(tactic| pos_def $rest*))
    | .integral => evalTactic (← `(tactic| integral_bound $rest*))
    | .interval => evalTactic (← `(tactic| interval $rest*))
  catch ex =>
    match r with
    | .conj | .infsup => throw ex
    | _ =>
      -- the backend's own message usually starts with its name; say it once
      let msg ← ex.toMessageData.toString
      let pre := r.name ++ ": "
      let msg := if msg.startsWith pre then (msg.drop pre.length).toString else msg
      throwError "via `{r.name}`: {msg}"

@[tactic realfpTac] def evalRealfp : Tactic := fun stx => withMainContext do
  RealFP.requireNative
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
  try
    RealFP.withTrust trust (realfpCore rest)
  catch ex =>
    let nat := realfp.native.get (← getOptions)
    let tr := if trust == `inherit then (if nat then `native else `kernel) else trust
    throwError "realfp (trust := {tr}): {ex.toMessageData}"

end RealFP.Front
