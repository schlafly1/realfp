/-
The `integral_bound` tactic: proves `c ≤ ∫ x in a..b, f x`, `∫ x in a..b, f x ≤ c` (or `<`),
and conjunctions / `∈ Set.Icc` of these, with `a`, `b`, `c` rational numerals (`a`, `b` exactly
representable as floats) and `f` built from the `interval` tactic's operations.

It searches (C kernels over a derivative tape) for an order `K ∈ {2, 4, 6, 8}` and an adaptive
partition (bisecting the cells with the widest enclosures) such that the kernel Taylor
quadrature certificate succeeds, then proves it by one `decide +kernel` on `quadBoundW` (the
derivatives as shared lets, so each `sin x`, `cos x`, … is evaluated once per cell environment)
with the let values of every cell given as checked witnesses, so every kernel operation runs
on literal inputs) and `RealFP.KQS.integral_bounds_of_quadBoundW` (standard axioms only).

```
example : (0.7468 : ℝ) ≤ ∫ x in (0:ℝ)..1, Real.exp (-x^2) := by integral_bound
```
-/
import RealFPMathlib.KQuad
import RealFPMathlib.KQuadShare
import RealFPMathlib.IntervalTactic

open Lean Meta Elab Tactic
open Interval64 Interval64.KF Interval64.KF.KQ RealFP.IntervalTactic

namespace RealFP.IntegralTactic

set_option linter.concreteInstances false
variable [ExtTbl]

/-- Exact bit pattern of a rational, if it is a float. -/
def exactBits (q : ℚ) : Option Nat :=
  let k := KI.ofRat q
  if k.lo == k.hi && ratOf k.lo == some q then some k.lo else none

/-- Midpoint bit pattern of two finite bit patterns. -/
def midBits (x y : Nat) : Nat := bitsOf (0.5 * KQ.toFl x + 0.5 * KQ.toFl y)

def flCell (c : Nat × Nat × Nat) : Float × Float × Float := (KQ.toFl c.1, KQ.toFl c.2.1, KQ.toFl c.2.2)

/-- Bisect a cell at its point. -/
def splitCell (c : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  [(c.1, midBits c.1 c.2.1, c.2.1), (c.2.1, midBits c.2.1 c.2.2, c.2.2)]

/-- Does the enclosure `[l, h]` (exact rationals of its endpoints) meet the requested bounds? -/
def meets (l h : Float) (lower upper : Option (ℚ × Bool)) : Bool :=
  match ratOf (bitsOf l), ratOf (bitsOf h) with
  | some l, some h =>
    let okL := match lower with
      | some (c, true) => decide (c < l)
      | some (c, false) => decide (c ≤ l)
      | none => true
    let okU := match upper with
      | some (c, true) => decide (h < c)
      | some (c, false) => decide (h ≤ c)
      | none => true
    okL && okU
  | _, _ => false

/-- Adaptive partition for order `K`: bisect the cells with the widest enclosures (C kernels, `quadF`
    cells) until the Float enclosure meets the bounds; at most `maxCells` cells. -/
def adaptCells (e : IExpr) (K : Nat) (a b : Nat) (lower upper : Option (ℚ × Bool)) (maxCells : Nat) :
    Option (List (Nat × Nat × Nat)) := Id.run do
  -- C tape when available; registered functions (`IExpr.ext`) have no tape: Lean evaluator
  let cell : Float × Float × Float → Interval64 := match derivTape e K with
    | some t => cellTape t
    | none => let ds := derivs e K; fun c => sumF ds K (ds.getLastD e) [c]
  let mut cs : List (Nat × Nat × Nat) := [(a, midBits a b, b)]
  for _ in List.range 64 do
    let ivs := cs.map fun c => cell (flCell c)
    let tot := ivs.foldr (· + ·) zeroI
    if meets tot.lo tot.hi lower upper then return some cs
    if cs.length ≥ maxCells then return none
    let ws := ivs.map fun I => let w := I.hi - I.lo; if w.isNaN then Float.inf else w
    let wmax := ws.foldl max 0
    cs := (cs.zip ws).flatMap fun (c, w) => if w ≥ 0.25 * wmax then splitCell c else [c]
  return none

/-- Float mirror of `domOK` (same `Interval64` operations under `toI`; untrusted). -/
def domOKF (env : List Interval64) : IExpr → Bool
  | .var _ => true
  | .rat _ => true
  | .add a b => domOKF env a && domOKF env b
  | .sub a b => domOKF env a && domOKF env b
  | .mul a b => domOKF env a && domOKF env b
  | .div a b => domOKF env a && domOKF env b && nzF (evalI env b)
  | .neg a => domOKF env a
  | .inv a => domOKF env a && nzF (evalI env a)
  | .sqrt a => domOKF env a && posF (evalI env a)
  | .abs _ => false
  | .pow a _ => domOKF env a
  | .exp a => domOKF env a
  | .log a => domOKF env a && posF (evalI env a)
  | .sin a => domOKF env a
  | .cos a => domOKF env a
  | .pi => true
  | .atan a => domOKF env a
  | .atan2 _ _ => false
  | .sinh a => domOKF env a
  | .cosh a => domOKF env a
  | .tanh a => domOKF env a
  | .log2 a => domOKF env a && posF (evalI env a)
  | .log10 a => domOKF env a && posF (evalI env a)
  | .tan a => domOKF env a && nzF (evalI env (.cos a))
  | .asin a => domOKF env a && posF (evalI env (.sub (.rat 1) (.pow a 2)))
  | .acos a => domOKF env a && posF (evalI env (.sub (.rat 1) (.pow a 2)))
  | .ext k d a => domOKF env a && extDomK k (ofI (evalI env a)) && decide (d = (ExtTbl.get k).deriv)
where
  posF (X : Interval64) : Bool := !X.lo.isNaN && !X.hi.isNaN && 0 < X.lo
  nzF (X : Interval64) : Bool := !X.lo.isNaN && !X.hi.isNaN && (0 < X.lo || X.hi < 0)

/-- Estimated kernel cost of one shared let (transcendental functions dominate). -/
def letCost : IExpr → Nat
  | .add .. | .sub .. | .mul .. | .div .. | .neg _ | .inv _ | .pow .. | .abs _ | .var _ | .rat _ => 1
  | _ => 30

/-- Search `K ∈ {2, 4, 6, 8}` with adaptive partitions (C kernels), and pick the smallest
    estimated kernel cost `cells × Σ cost(lets)` (shared subexpressions, `quadBoundS`). The certificate is checked only by
    the kernel; the search checks the same conditions on the `Float` mirror (`quadF` cells are
    bit-identical to `quadK`, `domOKF` mirrors `domOK`). -/
def searchQ (e : IExpr) (a b : Nat) (_qa _qb : ℚ) (lower upper : Option (ℚ × Bool)) (maxCells : Nat)
    (orders : List Nat := [2, 4, 6, 8]) :
    Option (Nat × List (Nat × Nat × Nat) × ℚ × ℚ) := Id.run do
  let mut best : Option (Nat × Nat × List (Nat × Nat × Nat)) := none
  -- registered functions are evaluated by Lean code (no C tape): keep the orders low
  let orders := if e.extFree then orders else
    match orders.filter (· ≤ 4) with | [] => orders | os => os
  for K in orders do
    let ds := derivs e K
    let cost1 := (shareDerivs e K).1.foldl (fun s d => s + letCost d) 1
    if let some cs := adaptCells e K a b lower upper maxCells then
      let dom := cs.all fun c => ds.dropLast.all fun d => domOKF [⟨KQ.toFl c.1, KQ.toFl c.2.2⟩] d
      let cost := cs.length * cost1
      if dom && (match best with | some (c, _, _) => cost < c | none => true) then
        best := some (cost, K, cs)
  let some (_, K, cs) := best | return none
  let R := quadF e K (cs.map flCell)
  match ratOf (bitsOf R.lo), ratOf (bitsOf R.hi) with
  | some l, some h =>
    let ql := match lower with | some (c, false) => c | _ => l
    let qh := match upper with | some (c, false) => c | _ => h
    return some (K, cs, ql, qh)
  | _, _ => return none

/-- Options of `integral_bound`: Taylor orders to try and the maximum number of cells. -/
structure ICfg where
  orders : List Nat := [2, 4, 6, 8]
  maxCells : Nat := 512

/-- Prove `ql ≤ ∫ ∧ ∫ ≤ qh` for the integral `I = ∫ x in a..b, body x`, adding it as `hI`. -/
def addBound (I : Expr) (lower upper : Option (ℚ × Bool)) (cfg : ICfg := {}) : TacticM Unit := do
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
  let some (K, cs, ql, qh) := searchQ e a b qa qb lower upper cfg.maxCells cfg.orders |
    throwError "integral_bound: no certificate with Taylor order K ∈ {cfg.orders} and ≤ \
      {cfg.maxCells} adaptive cells; loosen the bound or raise (maxBoxes := _)"
  let (lets, roots) := shareDerivs e K
  let lst := fun (l : List IExpr) => mkListLit (mkConst ``IExpr) (l.map iexprToExpr)
  let kiE := fun (k : KI) => mkApp2 (mkConst ``KI.mk) (toExpr k.lo) (toExpr k.hi)
  let kis := fun (l : List KI) => mkListLit (mkConst ``KI) (l.map kiE)
  let L ← lst lets
  let wl := cs.map fun c => ((evalLets [pt c.2.1] lets).drop 1, (evalLets [⟨c.1, c.2.2⟩] lets).drop 1)
  let ws ← wl.mapM fun (vm, vb) => do mkAppM ``Prod.mk #[← kis vm, ← kis vb]
  let wTy ← mkAppM ``Prod #[← mkAppM ``List #[mkConst ``KI], ← mkAppM ``List #[mkConst ``KI]]
  let wsE ← mkListLit wTy ws
  -- the witnesses, one small kernel check each (checked in parallel by `addDecl`)
  let boolTrue := fun (b : Expr) => mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)
  let rfl := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  let mut hw := mkApp ((← mkC ``RealFP.KQS.cellsW_nil)) L
  let n := cs.length
  for i in (List.range n).reverse do
    let c := cs[i]!; let w := wl[i]!
    let envM ← mkListLit (mkConst ``KI) [mkApp (mkConst ``pt) (toExpr c.2.1)]
    let envB ← mkListLit (mkConst ``KI) [kiE ⟨c.1, c.2.2⟩]
    let h1 ← mkAuxTheorem (boolTrue (mkAppN ((← mkC ``letsW)) #[envM, L, ← kis w.1])) rfl
    let h2 ← mkAuxTheorem (boolTrue (mkAppN ((← mkC ``letsW)) #[envB, L, ← kis w.2])) rfl
    hw := mkAppN ((← mkC ``RealFP.KQS.cellsW_cons)) #[L, toExpr c.1, toExpr c.2.1, toExpr c.2.2,
      ← kis w.1, ← kis w.2, toExpr (cs.drop (i + 1)), ← mkListLit wTy (ws.drop (i + 1)), h1, h2, hw]
  let args := #[iexprToExpr e, toExpr K, toExpr a, toExpr b, toExpr cs, L, ← lst roots, wsE,
    toExpr qa, toExpr qb, toExpr ql, toExpr qh]
  let ty := mkApp2 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
    (mkAppN ((← mkC ``quadBoundW)) args) |>.app (mkConst ``Bool.true)
  let pm ← mkFreshExprMVar ty
  let saved ← getGoals
  setGoals [pm.mvarId!]
  RealFP.closeCheck
  setGoals saved
  let pf := mkAppN ((← mkC ``RealFP.KQS.integral_bounds_of_quadBoundW)) ((args.push hw).push pm)
  let goal ← getMainGoal
  let g ← goal.assert `hI (← inferType pf) pf
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

def closeTac : TacticM Unit := do
  let h := mkIdent `hI
  let h1 := mkIdent `hI1
  let h2 := mkIdent `hI2
  let ids ← (← extSimpLemmas).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let ext ← if ids.isEmpty then `(tactic| skip) else `(tactic| try simp only [$ids,*] at $h:ident)
  evalTactic (← `(tactic|
    (simp only [Interval64.KF.IExpr.denote, List.getD_cons_zero, List.getD_cons_succ] at $h:ident
     $ext:tactic
     push_cast at $h:ident
     obtain ⟨$h1:ident, $h2:ident⟩ := $h:ident
     first
     | linarith
     | (norm_num at $h1:ident $h2:ident ⊢; linarith))))

partial def core (cfg : ICfg := {}) : TacticM Unit := do
  let goal ← getMainGoal
  let t ← whnfR (← instantiateMVars (← goal.getType))
  match t.getAppFnArgs with
  | (``And, #[_, _]) =>
    evalTactic (← `(tactic| constructor))
    let gs ← getGoals
    for g in gs do
      setGoals [g]; core cfg
  | (``LE.le, #[_, _, l, r]) | (``LT.lt, #[_, _, l, r]) =>
    let strict := t.isAppOf ``LT.lt
    if let some c ← ratOf? l then addBound r (some (c, strict)) none cfg
    else if let some c ← ratOf? r then addBound l none (some (c, strict)) cfg
    else throwError "integral_bound: one side must be a rational numeral"
    closeTac
  | _ => throwError "integral_bound: unsupported goal {t}"

/-- `integral_bound` : rigorous numeric bounds on `∫ x in a..b, f x` by kernel-checked Taylor
    quadrature. Strict bounds `<` are proved from the non-strict certificate with slack only if
    the computed enclosure is strictly inside; give a slightly weaker numeral otherwise. -/
syntax (name := integralBoundTac) "integral_bound" (ppSpace intervalOpt)* : tactic

/-- Options: `(trust := kernel|native)`, `(order := K)` (only Taylor order `K ∈ {2,4,6,8}`;
default: try all and keep the cheapest), `(maxBoxes := n)` (at most `n` cells, default 512). -/
@[tactic integralBoundTac] def evalIntegralBound : Tactic := fun stx => do
  let mut cfg : ICfg := {}
  let mut trust : Name := `inherit
  for o in stx[1].getArgs do
    let k := o[1].getId
    let n := o[3].isNatLit?
    if k == `trust then trust := o[3].getId
    else if k == `order then
      let some K := n | throwErrorAt o "integral_bound: (order := K) needs a numeral"
      unless K ∈ [2, 4, 6, 8] do
        throwErrorAt o "integral_bound: order must be 2, 4, 6 or 8 (got {K})"
      cfg := { cfg with orders := [K] }
    else if k == `maxBoxes then
      let some m := n | throwErrorAt o "integral_bound: (maxBoxes := n) needs a numeral"
      cfg := { cfg with maxCells := m }
    else throwErrorAt o "integral_bound: option `{k}` does not apply (integral_bound takes \
      `trust`, `order`, `maxBoxes`)"
  RealFP.requireNative
  RealFP.withTrust trust do
  evalTactic (← `(tactic| try simp only [Set.mem_Icc] ))
  withRegistered (core cfg)

end RealFP.IntegralTactic
