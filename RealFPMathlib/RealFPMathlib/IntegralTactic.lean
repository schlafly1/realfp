/-
The `integral_bound` tactic: proves `c ≤ ∫ x in a..b, f x`, `∫ x in a..b, f x ≤ c` (or `<`),
and conjunctions / `∈ Set.Icc` of these, with `a`, `b`, `c` rational numerals (`a`, `b` exactly
representable as floats) and `f` built from the `interval` tactic's operations.

It searches (C kernels over a derivative tape) for an order `K ∈ {2, 4, 6, 8}` and an adaptive
partition (bisecting the cells with the widest enclosures) such that the kernel Taylor
quadrature certificate succeeds, then proves it by one `decide +kernel` on `quadBoundS` (the
derivatives as shared lets, so each `sin x`, `cos x`, … is evaluated once per cell environment)
and `RealFP.KQS.integral_bounds_of_quadBoundS` (standard axioms only).

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
  let some t := derivTape e K | return none
  let mut cs : List (Nat × Nat × Nat) := [(a, midBits a b, b)]
  for _ in List.range 64 do
    let ivs := cs.map fun c => cellTape t (flCell c)
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
def searchQ (e : IExpr) (a b : Nat) (_qa _qb : ℚ) (lower upper : Option (ℚ × Bool)) (maxCells : Nat) :
    Option (Nat × List (Nat × Nat × Nat) × ℚ × ℚ) := Id.run do
  let mut best : Option (Nat × Nat × List (Nat × Nat × Nat)) := none
  for K in [2, 4, 6, 8] do
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
  let some (K, cs, ql, qh) := searchQ e a b qa qb lower upper 512 |
    throwError "integral_bound: no certificate with K ≤ 8 and ≤ 512 adaptive cells"
  let (lets, roots) := shareDerivs e K
  let lst := fun (l : List IExpr) => mkListLit (mkConst ``IExpr) (l.map iexprToExpr)
  let args := #[iexprToExpr e, toExpr K, toExpr a, toExpr b, toExpr cs, ← lst lets, ← lst roots,
    toExpr qa, toExpr qb, toExpr ql, toExpr qh]
  let ty := mkApp2 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
    (mkAppN (mkConst ``quadBoundS) args) |>.app (mkConst ``Bool.true)
  let pm ← mkFreshExprMVar ty
  let saved ← getGoals
  setGoals [pm.mvarId!]
  evalTactic (← `(tactic| decide +kernel))
  setGoals saved
  let pf := mkAppN (mkConst ``RealFP.KQS.integral_bounds_of_quadBoundS) (args.push pm)
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
