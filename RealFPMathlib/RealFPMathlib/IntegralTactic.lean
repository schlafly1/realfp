/-
The `integral_bound` tactic: proves `c ≤ ∫ x in a..b, f x`, `∫ x in a..b, f x ≤ c` (or `<`),
and conjunctions / `∈ Set.Icc` of these, with `a`, `b`, `c` rational numerals (`a`, `b` exactly
representable as floats) and `f` built from the `interval` tactic's operations.

It searches natively for an order `K` and a uniform partition such that the kernel Taylor
quadrature certificate `quadBound` succeeds, then proves it by one `decide +kernel` and
`RealFP.KQ.integral_bounds_of_quadBound` (standard axioms only).

```
example : (0.7468 : ℝ) ≤ ∫ x in (0:ℝ)..1, Real.exp (-x^2) := by integral_bound
```
-/
import RealFPMathlib.KQuad
import RealFPMathlib.IntervalTactic

open Lean Meta Elab Tactic
open Interval64.KF Interval64.KF.KQ RealFP.IntervalTactic

namespace RealFP.IntegralTactic

/-- Exact bit pattern of a rational, if it is a float. -/
def exactBits (q : ℚ) : Option Nat :=
  let k := KI.ofRat q
  if k.lo == k.hi && ratOf k.lo == some q then some k.lo else none

/-- Search `(K, N)` (`K ∈ {4, 6, 8}`, `N ≤ 2^maxLog`) with `quadBound` true for `ql`, `qh`. -/
def searchQ (e : IExpr) (a b : Nat) (qa qb : ℚ) (lower upper : Option (ℚ × Bool)) (maxLog : Nat) :
    Option (Nat × Nat × ℚ × ℚ) := Id.run do
  for lg in List.range (maxLog + 1) do
    for K in [4, 6, 8] do
      let N := 2 ^ lg
      let cs := uniformCells (KQ.toFl a) (KQ.toFl b) N
      match quadK e K a b cs with
      | some R =>
        match ratOf R.lo, ratOf R.hi with
        | some l, some h =>
          let okL := match lower with
            | some (c, true) => decide (c < l) | _ => true
          let okU := match upper with
            | some (c, true) => decide (h < c) | _ => true
          let ql := match lower with | some (c, false) => c | _ => l
          let qh := match upper with | some (c, false) => c | _ => h
          if okL && okU && quadBound e K a b cs qa qb ql qh then return some (K, N, ql, qh)
        | _, _ => pure ()
      | none => pure ()
  return none

/-- Prove `ql ≤ ∫ ∧ ∫ ≤ qh` for the integral `I = ∫ x in a..b, body x`, adding it as `hI`. -/
def addBound (I : Expr) (lower upper : Option (ℚ × Bool)) : TacticM Unit := do
  let some (f, aE, bE) ← (do
      let (fn, as) := I.getAppFnArgs
      if fn == ``intervalIntegral && as.size ≥ 4 then
        pure (some (as[as.size - 4]!, as[as.size - 3]!, as[as.size - 2]!))
      else pure none) | throwError "integral_bound: expected `∫ x in a..b, f x`, got {I}"
  let some qa ← ratOf? aE | throwError "integral_bound: lower limit is not a numeral"
  let some qb ← ratOf? bE | throwError "integral_bound: upper limit is not a numeral"
  let some a := exactBits qa | throwError "integral_bound: {qa} is not a float"
  let some b := exactBits qb | throwError "integral_bound: {qb} is not a float"
  let e ← lambdaTelescope f fun xs body => do
    unless xs.size == 1 do throwError "integral_bound: unexpected integrand"
    reify xs body
  let some (K, N, ql, qh) := searchQ e a b qa qb lower upper 8 |
    throwError "integral_bound: no certificate with K ≤ 8 and ≤ 256 cells"
  let cs := uniformCells (KQ.toFl a) (KQ.toFl b) N
  let args := #[iexprToExpr e, toExpr K, toExpr a, toExpr b, toExpr cs, toExpr qa, toExpr qb,
    toExpr ql, toExpr qh]
  let ty := mkApp2 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
    (mkAppN (mkConst ``quadBound) args) |>.app (mkConst ``Bool.true)
  let pm ← mkFreshExprMVar ty
  let saved ← getGoals
  setGoals [pm.mvarId!]
  evalTactic (← `(tactic| decide +kernel))
  setGoals saved
  let pf := mkAppN (mkConst ``RealFP.KQ.integral_bounds_of_quadBound) (args.push pm)
  let goal ← getMainGoal
  let g ← goal.assert `hI (← inferType pf) pf
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

def closeTac : TacticM Unit := do
  let h := mkIdent `hI
  let h1 := mkIdent `hI1
  let h2 := mkIdent `hI2
  evalTactic (← `(tactic|
    (simp only [Interval64.KF.IExpr.denote, List.getD_cons_zero, List.getD_cons_succ] at $h:ident
     push_cast at $h:ident
     obtain ⟨$h1:ident, $h2:ident⟩ := $h:ident
     first
     | linarith
     | (norm_num at $h1:ident $h2:ident ⊢; linarith))))

partial def core : TacticM Unit := do
  let goal ← getMainGoal
  let t ← whnfR (← instantiateMVars (← goal.getType))
  match t.getAppFnArgs with
  | (``And, #[_, _]) =>
    evalTactic (← `(tactic| constructor))
    let gs ← getGoals
    for g in gs do
      setGoals [g]; core
  | (``LE.le, #[_, _, l, r]) | (``LT.lt, #[_, _, l, r]) =>
    let strict := t.isAppOf ``LT.lt
    if let some c ← ratOf? l then addBound r (some (c, strict)) none
    else if let some c ← ratOf? r then addBound l none (some (c, strict))
    else throwError "integral_bound: one side must be a rational numeral"
    closeTac
  | _ => throwError "integral_bound: unsupported goal {t}"

/-- `integral_bound` : rigorous numeric bounds on `∫ x in a..b, f x` by kernel-checked Taylor
    quadrature. Strict bounds `<` are proved from the non-strict certificate with slack only if
    the computed enclosure is strictly inside; give a slightly weaker numeral otherwise. -/
elab "integral_bound" : tactic => do
  evalTactic (← `(tactic| try simp only [Set.mem_Icc] ))
  core

end RealFP.IntegralTactic
