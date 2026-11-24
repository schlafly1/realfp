/-
The `interval` tactic: proves real inequalities by reflection and Interval64 bisection.

```
example : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x * (1 - x) ≤ 1/4 + 1/100 := by interval
example (x : ℝ) (h₀ : 1 ≤ x) (h₁ : x ≤ 2) : Real.exp x < 8 := by interval
example (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : 0 ≤ y ∧ y ≤ 1) : x * y ≤ 1 := by interval
example : … := by interval (depth := 30) (maxBoxes := 100000)
```

How it works:

1. Introduce binders; split `∧`, `Set.Icc` hypotheses; collect rational bounds `a ≤ x ≤ b`
   (`<` is weakened to `≤`) for every real variable of the goal.
2. Goals `f ≤ c`, `f < c`, `c ≤ f`, `c < f` with `c` a rational numeral are used as is; `f ≤ g`
   and `f < g` with neither side a numeral become `f - g ≤ 0` / `f - g < 0`. Conjunctions and
   `f ∈ Set.Icc a b` are split.
3. `f` is reified into `IExpr` (`+ - * / ⁻¹ √ |·| ^n exp log sin cos`, rational numerals).
4. A bisection certificate (`Cert`) is searched in compiled code by running the same Nat-level
   evaluator `evalK` the kernel uses, always splitting the widest variable at its float midpoint.
5. The proof is `prove_le e boxes c cert (by decide +kernel) xs hxs` — one kernel evaluation of
   `checkK`; soundness comes from `RealFP.checkK_sound` (no `native_decide`, standard axioms).
-/
import RealFPMathlib.IntervalSound
import RealFPMathlib.IntervalDeriv
import RealFPMathlib.Roots
import RealFPMathlib.Trust
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.CasesM

open Lean Meta Elab Tactic
open Interval64.KF

namespace RealFP.IntervalTactic

initialize registerTraceClass `interval

theorem inBoxes_nil : InBoxes [] [] ↔ True := ⟨fun _ => trivial, fun _ => List.Forall₂.nil⟩

theorem inBoxes_cons {x : ℝ} {xs : List ℝ} {b : ℚ × ℚ} {bs : List (ℚ × ℚ)} :
    InBoxes (x :: xs) (b :: bs) ↔ ((b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)) ∧ InBoxes xs bs :=
  List.forall₂_cons

theorem checkK_split_of {e : IExpr} {g : KI → Bool} {i m : Nat} {l r : Cert} {env : List KI}
    (hm : (!isNaN m && Nat.blt m (2 ^ 64)) = true)
    (hl : checkK e g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) = true)
    (hr : checkK e g r (env.set i ⟨m, (env.getD i zeroK).hi⟩) = true) :
    checkK e g (.split i m l r) env = true := by
  simp only [checkK, hl, hr, Bool.and_true]; exact hm

theorem close_le {a b A B : ℝ} (h : A ≤ B) (ha : a = A) (hb : b = B) : a ≤ b := ha ▸ hb ▸ h
theorem close_lt {a b A B : ℝ} (h : A < B) (ha : a = A) (hb : b = B) : a < b := ha ▸ hb ▸ h
theorem le_of_sub {a b : ℝ} (h : a - b ≤ 0) : a ≤ b := sub_nonpos.mp h
theorem lt_of_sub {a b : ℝ} (h : a - b < 0) : a < b := sub_neg.mp h

/-! ### Certificate search (runs the kernel's own evaluator `evalK` natively) -/

def toFl (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)

/-- Widest splittable variable and its float midpoint. -/
def pickSplit (env : List KI) : Option (Nat × Nat) := Id.run do
  let mut best : Option (Nat × Nat) := none
  let mut bestW : Float := -1
  for i in [0:env.length] do
    let X := env.getD i zeroK
    let lo := toFl X.lo
    let hi := toFl X.hi
    let mid := if (lo + hi).isInf then lo / 2 + hi / 2 else (lo + hi) / 2
    let mid := if mid == 0 then 0 else mid   -- avoid -0
    if lo < mid && mid < hi && !mid.isNaN then
      let w := hi - lo
      if w > bestW then
        bestW := w
        best := some (i, mid.toBits.toNat)
  return best

partial def search (e : IExpr) (g : KI → Bool) (maxEvals : Nat) :
    Nat → List KI → StateM Nat (Option Cert)
  | depth, env => do
    modify (· + 1)
    if g (evalK env e) then return some .leaf
    if depth == 0 || (← get) ≥ maxEvals then return none
    match pickSplit env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i zeroK
      let some l ← search e g maxEvals (depth - 1) (env.set i ⟨X.lo, m⟩) | return none
      let some r ← search e g maxEvals (depth - 1) (env.set i ⟨m, X.hi⟩) | return none
      return some (.split i m l r)

def certLeaves : Cert → Nat
  | .leaf => 1
  | .split _ _ l r => certLeaves l + certLeaves r

/-! ### Certificates with derivatives (`DCert`, `checkD`) -/

def dLeaves : DCert → Nat
  | .leaf => 1
  | .split _ _ l r => dLeaves l + dLeaves r
  | .mono _ _ dc c => dLeaves dc + dLeaves c
  | .center _ _ => 1

def dStats : DCert → Nat × Nat × Nat   -- (splits, mono, center)
  | .leaf => (0, 0, 0)
  | .split _ _ l r => let a := dStats l; let b := dStats r; (a.1 + b.1 + 1, a.2.1 + b.2.1, a.2.2 + b.2.2)
  | .mono _ _ dc c => let a := dStats dc; let b := dStats c; (a.1 + b.1, a.2.1 + b.2.1 + 1, a.2.2 + b.2.2)
  | .center _ _ => (0, 0, 1)

/-- Variables whose interval is not a point. -/
def wideVars (env : List KI) : List Nat :=
  (List.range env.length).filter fun i => (env.getD i zeroK).lo != (env.getD i zeroK).hi

/-- Search: leaf; else (if `deriv`) monotonicity with an obvious derivative sign, centred form,
monotonicity with a derivative sign proved recursively (up to `order` derivatives); else split. -/
partial def searchD (deriv : Bool) (maxEvals : Nat) (e : IExpr) (g : KI → Bool) (upper : Bool)
    (order : Nat) (allowSplit : Bool) : Nat → List KI → StateM Nat (Option DCert)
  | depth, env => do
    modify (· + 1)
    if g (evalK env e) then return some .leaf
    if (← get) ≥ maxEvals then return none
    if deriv && domOK env e then
      let tryEnd (i : Nat) (inc : Bool) (dc : DCert) : StateM Nat (Option DCert) := do
        let X := env.getD i zeroK
        let p := if inc == upper then X.hi else X.lo
        if !finK p then return none
        let some c ← searchD deriv maxEvals e g upper order allowSplit depth (env.set i ⟨p, p⟩)
          | return none
        return some (.mono i inc dc c)
      -- 1. monotone, sign visible on the box
      for i in wideVars env do
        modify (· + 1)
        let D := evalK env (e.deriv i)
        if gGe zeroHi D then
          if let some c ← tryEnd i true .leaf then return some c
        if gLe zeroLo D then
          if let some c ← tryEnd i false .leaf then return some c
      -- 2. centred form at the midpoint of the widest variable
      if let some (i, m) := pickSplit env then
        modify (· + 1)
        if checkD e g upper (.center i m) env then return some (.center i m)
      -- 3. monotone, sign proved with higher derivatives
      if order > 0 then
        for i in wideVars env do
          for inc in [true, false] do
            let gs := if inc then gGe zeroHi else gLe zeroLo
            if let some dc ← searchD deriv maxEvals (e.deriv i) gs (!inc) (order - 1) false depth env then
              if let some c ← tryEnd i inc dc then return some c
    if depth == 0 || !allowSplit || (← get) ≥ maxEvals then return none
    match pickSplit env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i zeroK
      let some l ← searchD deriv maxEvals e g upper order allowSplit (depth - 1)
        (env.set i ⟨X.lo, m⟩) | return none
      let some r ← searchD deriv maxEvals e g upper order allowSplit (depth - 1)
        (env.set i ⟨m, X.hi⟩) | return none
      return some (.split i m l r)

/-! ### Reification -/

partial def iexprToExpr : IExpr → Expr
  | .var i => mkApp (mkConst ``IExpr.var) (toExpr i)
  | .rat q => mkApp (mkConst ``IExpr.rat) (toExpr q)
  | .add a b => mkApp2 (mkConst ``IExpr.add) (iexprToExpr a) (iexprToExpr b)
  | .sub a b => mkApp2 (mkConst ``IExpr.sub) (iexprToExpr a) (iexprToExpr b)
  | .mul a b => mkApp2 (mkConst ``IExpr.mul) (iexprToExpr a) (iexprToExpr b)
  | .div a b => mkApp2 (mkConst ``IExpr.div) (iexprToExpr a) (iexprToExpr b)
  | .neg a => mkApp (mkConst ``IExpr.neg) (iexprToExpr a)
  | .inv a => mkApp (mkConst ``IExpr.inv) (iexprToExpr a)
  | .sqrt a => mkApp (mkConst ``IExpr.sqrt) (iexprToExpr a)
  | .abs a => mkApp (mkConst ``IExpr.abs) (iexprToExpr a)
  | .pow a n => mkApp2 (mkConst ``IExpr.pow) (iexprToExpr a) (toExpr n)
  | .exp a => mkApp (mkConst ``IExpr.exp) (iexprToExpr a)
  | .log a => mkApp (mkConst ``IExpr.log) (iexprToExpr a)
  | .sin a => mkApp (mkConst ``IExpr.sin) (iexprToExpr a)
  | .cos a => mkApp (mkConst ``IExpr.cos) (iexprToExpr a)
  | .pi => mkConst ``IExpr.pi
  | .atan a => mkApp (mkConst ``IExpr.atan) (iexprToExpr a)
  | .atan2 a b => mkApp2 (mkConst ``IExpr.atan2) (iexprToExpr a) (iexprToExpr b)
  | .sinh a => mkApp (mkConst ``IExpr.sinh) (iexprToExpr a)
  | .cosh a => mkApp (mkConst ``IExpr.cosh) (iexprToExpr a)
  | .tanh a => mkApp (mkConst ``IExpr.tanh) (iexprToExpr a)
  | .log2 a => mkApp (mkConst ``IExpr.log2) (iexprToExpr a)
  | .log10 a => mkApp (mkConst ``IExpr.log10) (iexprToExpr a)
  | .tan a => mkApp (mkConst ``IExpr.tan) (iexprToExpr a)
  | .asin a => mkApp (mkConst ``IExpr.asin) (iexprToExpr a)
  | .acos a => mkApp (mkConst ``IExpr.acos) (iexprToExpr a)

partial def dcertToExpr : DCert → Expr
  | .leaf => mkConst ``DCert.leaf
  | .split i m l r => mkApp4 (mkConst ``DCert.split) (toExpr i) (toExpr m) (dcertToExpr l) (dcertToExpr r)
  | .mono i inc dc c => mkApp4 (mkConst ``DCert.mono) (toExpr i) (toExpr inc) (dcertToExpr dc) (dcertToExpr c)
  | .center i m => mkApp2 (mkConst ``DCert.center) (toExpr i) (toExpr m)

partial def certToExpr : Cert → Expr
  | .leaf => mkConst ``Cert.leaf
  | .split i m l r => mkApp4 (mkConst ``Cert.split) (toExpr i) (toExpr m) (certToExpr l) (certToExpr r)

/-- Rational value of a closed real numeral expression, via `norm_num`. -/
def ratOf? (e : Expr) : MetaM (Option ℚ) := do
  if e.hasFVar || e.hasMVar then return none
  try
    let r ← Mathlib.Meta.NormNum.derive (u := Level.zero) (α := mkConst ``Real) e
    return r.toRat
  catch _ => return none

def natOf? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  let e ← instantiateMVars e
  if let some n := e.rawNatLit? then return some n
  if let some n := e.nat? then return some n
  try
    let r ← Mathlib.Meta.NormNum.derive (u := Level.zero) (α := mkConst ``Nat) e
    match r.toRat with
    | some q => if q.den == 1 && 0 ≤ q.num then return some q.num.toNat else return none
    | none => return none
  catch _ => return none

partial def reify (vars : Array Expr) (e : Expr) : MetaM IExpr := do
  let e ← instantiateMVars e
  if let some i := vars.findIdx? (· == e) then return .var i
  if e.hasFVar && (e.isApp || e.isProj) then
    for i in [0:vars.size] do
      if ← withReducible (isDefEq e vars[i]!) then return .var i
  if let some q ← ratOf? e then return .rat q
  let r := reify vars
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← r a) (← r b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← r a) (← r b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← r a) (← r b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return .div (← r a) (← r b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← r a)
  | (``Inv.inv, #[_, _, a]) => return .inv (← r a)
  | (``Real.sqrt, #[a]) => return .sqrt (← r a)
  | (``abs, #[_, _, _, a]) => return .abs (← r a)
  | (``Real.exp, #[a]) => return .exp (← r a)
  | (``Real.log, #[a]) => return .log (← r a)
  | (``Real.sin, #[a]) => return .sin (← r a)
  | (``Real.cos, #[a]) => return .cos (← r a)
  | (``Real.pi, #[]) => return .pi
  | (``Real.arctan, #[a]) => return .atan (← r a)
  | (``Real.sinh, #[a]) => return .sinh (← r a)
  | (``Real.cosh, #[a]) => return .cosh (← r a)
  | (``Real.tanh, #[a]) => return .tanh (← r a)
  | (``Real.tan, #[a]) => return .tan (← r a)
  | (``Real.arcsin, #[a]) => return .asin (← r a)
  | (``Real.arccos, #[a]) => return .acos (← r a)
  | (``Real.logb, #[b, a]) =>
    match ← r b with
    | .rat q =>
      if q == 2 then return .log2 (← r a)
      else if q == 10 then return .log10 (← r a)
      else throwError "interval: only `Real.logb 2` and `Real.logb 10` are supported: {e}"
    | _ => throwError "interval: only `Real.logb 2` and `Real.logb 10` are supported: {e}"
  | (``Complex.arg, #[z]) =>
    -- `Complex.arg (↑x + ↑y * Complex.I)` is `atan2 y x`
    match z.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      match a.getAppFnArgs, b.getAppFnArgs with
      | (``Complex.ofReal, #[x]), (``HMul.hMul, #[_, _, _, _, c, i]) =>
        match c.getAppFnArgs with
        | (``Complex.ofReal, #[y]) =>
          unless i.isConstOf ``Complex.I do throwError "interval: expected `↑x + ↑y * Complex.I`: {z}"
          return .atan2 (← r y) (← r x)
        | _ => throwError "interval: expected `↑x + ↑y * Complex.I`: {z}"
      | _, _ => throwError "interval: expected `↑x + ↑y * Complex.I`: {z}"
    | _ => throwError "interval: expected `Complex.arg (↑x + ↑y * Complex.I)`: {z}"
  | (``HPow.hPow, #[_, nT, _, _, a, n]) =>
    unless (← isDefEq nT (mkConst ``Nat)) do
      throwError "interval: only natural-number powers are supported: {e}"
    let some k ← natOf? n | throwError "interval: exponent is not a numeral: {n}"
    return .pow (← r a) k
  | _ => throwError "interval: cannot interpret {e} (variables need numeral bounds in context)"

partial def gatherFVars (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar id => if acc.contains id then acc else acc.push id
  | .app f a => gatherFVars a (gatherFVars f acc)
  | .mdata _ b => gatherFVars b acc
  | .proj _ _ b => gatherFVars b acc
  | .lam _ t b _ | .forallE _ t b _ => gatherFVars b (gatherFVars t acc)
  | .letE _ t v b _ => gatherFVars b (gatherFVars v (gatherFVars t acc))
  | _ => acc

/-- Real free variables occurring in `e`, in order of first occurrence. -/
def collectVars (e : Expr) : MetaM (Array Expr) := do
  let fvs := gatherFVars (← instantiateMVars e) #[]
  let mut out := #[]
  for fv in fvs do
    if (← isDefEq (← fv.getType) (mkConst ``Real)) then out := out.push (mkFVar fv)
  return out

/-- Rational bounds for `x` from the local context (strict bounds weakened). -/
def findBounds (x : Expr) : MetaM (ℚ × ℚ) := do
  let mut lo : Option ℚ := none
  let mut hi : Option ℚ := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars (← whnfR (← instantiateMVars d.type))
    let some (a, b) ← (do
        match t.getAppFnArgs with
        | (``LE.le, #[ty, _, a, b]) | (``LT.lt, #[ty, _, a, b]) =>
          if ← isDefEq ty (mkConst ``Real) then pure (some (a, b)) else pure none
        | _ => pure none) | continue
    if b == x then
      if let some q ← ratOf? a then lo := some (match lo with | some l => max l q | none => q)
    if a == x then
      if let some q ← ratOf? b then hi := some (match hi with | some h => min h q | none => q)
  match lo, hi with
  | some l, some h => return (l, h)
  | _, _ => throwError "interval: no numeral lower and upper bound for {x} in context"

/-! ### The tactic -/

structure Cfg where
  depth : Nat := 24
  maxBoxes : Nat := 50000
  /-- Boxes per `decide +kernel` call (separate kernel checks keep memory bounded). -/
  chunk : Nat := 32
  /-- Use derivatives (monotonicity, centred form). -/
  deriv : Bool := true
  /-- Highest derivative order used to prove monotonicity. -/
  order : Nat := 3

def denoteSimp : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | rfl
    | ((try simp only [Interval64.KF.IExpr.denote, List.getD_cons_zero, List.getD_cons_succ])
       first
       | rfl
       | (push_cast; done)
       | (push_cast; ring_nf; done)
       | (norm_num; done)
       | (norm_num <;> ring_nf; done))))

def inBoxesTac : TacticM Unit := do
  evalTactic (← `(tactic|
    (simp only [RealFP.IntervalTactic.inBoxes_cons, RealFP.IntervalTactic.inBoxes_nil, and_true]
     repeat' apply And.intro
     all_goals first | (push_cast; linarith) | (norm_num; linarith) | norm_num)))

/-- Proof of `checkK e g cert env = true`: subtrees with at most `chunk` boxes are one
`decide +kernel` call each, glued with `checkK_split_of`. -/
partial def proveCheck (chunk : Nat) (eE gE : Expr) (cert : Cert) (envE : Expr) : TacticM Expr := do
  match cert with
  | .split i m l r =>
    if certLeaves cert > chunk then
      let lem := mkAppN (mkConst ``checkK_split_of)
        #[eE, gE, toExpr i, toExpr m, certToExpr l, certToExpr r, envE]
      let ty ← inferType lem
      let .forallE _ _ b1 _ := ty | throwError "interval: internal (split lemma)"
      let .forallE _ hlT b2 _ := b1 | throwError "interval: internal (split lemma)"
      let .forallE _ hrT _ _ := b2 | throwError "interval: internal (split lemma)"
      let hm ← mkEqRefl (mkConst ``Bool.true)
      let getEnv (t : Expr) : MetaM Expr := do
        let some (_, lhs, _) := t.eq? | throwError "interval: internal (env)"
        return lhs.appArg!
      let hl ← proveCheck chunk eE gE l (← getEnv hlT)
      let hr ← proveCheck chunk eE gE r (← getEnv hrT)
      return mkAppN lem #[hm, hl, hr]
    else leafChunk
  | .leaf => leafChunk
where
  leafChunk : TacticM Expr := do
    let chk := mkApp4 (mkConst ``checkK) eE gE (certToExpr cert) envE
    let hM ← mkFreshExprMVar (← mkEq chk (mkConst ``Bool.true))
    let saved ← getGoals
    setGoals [hM.mvarId!]
    RealFP.closeCheck
    setGoals saved
    instantiateMVars hM

partial def proveCheckD (chunk : Nat) (eE gE upperE : Expr) (cert : DCert) (envE : Expr) :
    TacticM Expr := do
  match cert with
  | .split i m l r =>
    if dLeaves cert > chunk then
      let lem := mkAppN (mkConst ``RealFP.checkD_split_of)
        #[eE, gE, upperE, toExpr i, toExpr m, dcertToExpr l, dcertToExpr r, envE]
      let ty ← inferType lem
      let .forallE _ _ b1 _ := ty | throwError "interval: internal (split lemma)"
      let .forallE _ hlT b2 _ := b1 | throwError "interval: internal (split lemma)"
      let .forallE _ hrT _ _ := b2 | throwError "interval: internal (split lemma)"
      let hm ← mkEqRefl (mkConst ``Bool.true)
      let getEnv (t : Expr) : MetaM Expr := do
        let some (_, lhs, _) := t.eq? | throwError "interval: internal (env)"
        return lhs.appArg!
      let hl ← proveCheckD chunk eE gE upperE l (← getEnv hlT)
      let hr ← proveCheckD chunk eE gE upperE r (← getEnv hrT)
      return mkAppN lem #[hm, hl, hr]
    else leafChunk
  | _ => leafChunk
where
  leafChunk : TacticM Expr := do
    let chk := mkApp5 (mkConst ``checkD) eE gE upperE (dcertToExpr cert) envE
    let hM ← mkFreshExprMVar (← mkEq chk (mkConst ``Bool.true))
    let saved ← getGoals
    setGoals [hM.mvarId!]
    RealFP.closeCheck
    setGoals saved
    instantiateMVars hM

/-- Prove `lhs ≤ rhs` (`strict = false`) or `lhs < rhs` on the main goal. -/
def proveCmp (cfg : Cfg) (strict : Bool) (lhs rhs : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  -- orient: f ≤ c (upper) or c ≤ f (lower), else move everything left
  let (f, c, upper) ← do
    if let some c ← ratOf? rhs then pure (lhs, c, true)
    else if let some c ← ratOf? lhs then pure (rhs, c, false)
    else
      let lem := if strict then ``lt_of_sub else ``le_of_sub
      let gs ← goal.apply (mkConst lem)
      replaceMainGoal gs
      pure (← mkAppM ``HSub.hSub #[lhs, rhs], (0 : ℚ), true)
  let goal ← getMainGoal
  goal.withContext do
  let vars ← collectVars f
  let e ← reify vars f
  let bs ← vars.mapM (fun v => (findBounds v : MetaM (ℚ × ℚ)))
  let env := boxes bs.toList
  let cK := KI.ofRat c
  let (g, gName, pName) :=
    match strict, upper with
    | false, true => (gLe cK.lo, ``gLe, ``proveD_le)
    | true, true => (gLt cK.lo, ``gLt, ``proveD_lt)
    | false, false => (gGe cK.hi, ``gGe, ``proveD_ge)
    | true, false => (gGt cK.hi, ``gGt, ``proveD_gt)
  let (cert?, evals) :=
    (searchD cfg.deriv (2 * cfg.maxBoxes) e g upper cfg.order true cfg.depth env).run 0
  let some cert := cert? |
    throwError "interval: no certificate within depth {cfg.depth} / {cfg.maxBoxes} boxes \
      ({evals} evaluations); try larger (depth := _) (maxBoxes := _) or tighter bounds"
  if dLeaves cert > cfg.maxBoxes then
    throwError "interval: certificate needs {dLeaves cert} boxes > maxBoxes {cfg.maxBoxes}"
  let st := dStats cert
  trace[interval] "{vars.size} variable(s), {dLeaves cert} boxes ({st.1} splits, {st.2.1} mono, \
    {st.2.2} centred), {evals} native evaluations"
  let eE := iexprToExpr e
  let bsE := toExpr bs.toList
  let cE := toExpr c
  let certE := dcertToExpr cert
  let xsE ← mkListLit (mkConst ``Real) vars.toList
  let kc := mkApp (mkConst (if upper then ``KI.lo else ``KI.hi)) (mkApp (mkConst ``KI.ofRat) cE)
  let gE := mkApp (mkConst gName) kc
  let hM ← proveCheckD cfg.chunk eE gE (toExpr upper) cert (mkApp (mkConst ``boxes) bsE)
  let saved ← getGoals
  let hxsTy := mkApp2 (mkConst ``InBoxes) xsE bsE
  let hxsM ← mkFreshExprMVar hxsTy
  setGoals [hxsM.mvarId!]
  inBoxesTac
  setGoals saved
  let pf := mkAppN (mkConst pName) #[eE, bsE, cE, certE, hM, xsE, hxsM]
  let pfTy ← inferType pf
  -- close `lhs ≤ rhs` from `A ≤ B` via two equalities
  let goal ← getMainGoal
  let t ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, A, B) := (if strict then pfTy.lt? else pfTy.le?) | throwError "interval: internal"
  let (_, a, b) ← match (if strict then t.lt? else t.le?) with
    | some x => pure x | none => throwError "interval: internal (goal shape)"
  let lem := if strict then ``close_lt else ``close_le
  let ha ← mkFreshExprMVar (← mkEq a A)
  let hb ← mkFreshExprMVar (← mkEq b B)
  goal.assign (mkAppN (mkConst lem) #[a, b, A, B, pf, ha, hb])
  for m in [ha, hb] do
    setGoals [m.mvarId!]
    denoteSimp
    unless (← getGoals).isEmpty do
      throwError "interval: could not match the goal with its reified form"
  setGoals saved.tail

theorem close_ne {a A : ℝ} (h : A ≠ 0) (ha : a = A) : a ≠ 0 := ha ▸ h
theorem ne_of_sub_ne {a b : ℝ} (h : a - b ≠ 0) : a ≠ b := fun e => h (by rw [e, sub_self])

/-- Prove `lhs ≠ rhs` (exclusion of zeros of `lhs - rhs` on the box) by bisection until every
box excludes `0`. -/
def proveNe (cfg : Cfg) (lhs rhs : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let f ← goal.withContext do
    if let some q ← ratOf? rhs then
      if q == 0 then return lhs
    let gs ← goal.apply (mkConst ``ne_of_sub_ne)
    replaceMainGoal gs
    mkAppM ``HSub.hSub #[lhs, rhs]
  let goal ← getMainGoal
  goal.withContext do
  let vars ← collectVars f
  let e ← reify vars f
  let bs ← vars.mapM (fun v => (findBounds v : MetaM (ℚ × ℚ)))
  let env := boxes bs.toList
  let (cert?, evals) := (search e RealFP.Roots.gNe (2 * cfg.maxBoxes) cfg.depth env).run 0
  let some cert := cert? |
    throwError "interval: could not show {f} ≠ 0: no bisection certificate within depth \
      {cfg.depth} / {cfg.maxBoxes} boxes ({evals} evaluations). The expression may vanish on \
      the box (if it does, `root_exists` proves that); otherwise try larger (depth := _)"
  trace[interval] "≠ 0: {certLeaves cert} boxes, {evals} native evaluations"
  let eE := iexprToExpr e
  let bsE := toExpr bs.toList
  let certE := certToExpr cert
  let xsE ← mkListLit (mkConst ``Real) vars.toList
  let hM ← proveCheck cfg.chunk eE (mkConst ``RealFP.Roots.gNe) cert
    (mkApp (mkConst ``boxes) bsE)
  let saved ← getGoals
  let hxsM ← mkFreshExprMVar (mkApp2 (mkConst ``InBoxes) xsE bsE)
  setGoals [hxsM.mvarId!]
  inBoxesTac
  setGoals saved
  let pf := mkAppN (mkConst ``RealFP.Roots.prove_ne) #[eE, bsE, certE, hM, xsE, hxsM]
  let goal ← getMainGoal
  let ha ← mkFreshExprMVar (← mkEq f (mkApp2 (mkConst ``IExpr.denote) xsE eE))
  goal.assign (mkAppN (mkConst ``close_ne) #[f, mkApp2 (mkConst ``IExpr.denote) xsE eE, pf, ha])
  setGoals [ha.mvarId!]
  denoteSimp
  unless (← getGoals).isEmpty do
    throwError "interval: could not match the goal with its reified form"
  setGoals saved.tail

partial def intervalCore (cfg : Cfg) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let t ← instantiateMVars (← goal.getType)
  let t ← whnfR t
  match t.getAppFnArgs with
  | (``And, #[_, _]) =>
    let gs ← goal.apply (mkConst ``And.intro [])
    for g in gs do
      setGoals [g]; intervalCore cfg
    setGoals []
  | (``Membership.mem, #[_, _, _, s, x]) =>
    let s ← whnfR s
    match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, a, b]) =>
      let _ := (a, b, x)
      evalTactic (← `(tactic| rw [Set.mem_Icc]))
      intervalCore cfg
    | _ => throwError "interval: unsupported set membership {t}"
  | (``Not, #[p]) =>
    let p ← whnfR (← instantiateMVars p)
    match p.getAppFnArgs with
    | (``Eq, #[ty, a, b]) =>
      unless ← isDefEq ty (mkConst ``Real) do throwError "interval: goal is not over ℝ"
      proveNe cfg a b
    | _ => throwError "interval: unsupported goal {t}"
  | (``LE.le, #[ty, _, a, b]) =>
    unless ← isDefEq ty (mkConst ``Real) do throwError "interval: goal is not over ℝ"
    proveCmp cfg false a b
  | (``LT.lt, #[ty, _, a, b]) =>
    unless ← isDefEq ty (mkConst ``Real) do throwError "interval: goal is not over ℝ"
    proveCmp cfg true a b
  | _ => throwError "interval: unsupported goal {t}; expected `f ≤ g`, `f < g`, `f ≠ g`, \
      `f ∈ Set.Icc a b` or a conjunction of these (over ℝ, variables bounded in context)"

declare_syntax_cat intervalOpt
syntax "(" ident " := " num ")" : intervalOpt
syntax "(" ident " := " ident ")" : intervalOpt
/-- `interval` with options in any order: `(depth := n)`, `(maxBoxes := n)`, `(chunk := n)`,
    `(deriv := false)`, `(order := n)`, `(trust := kernel|native)`. -/
syntax (name := intervalTac) "interval" (ppSpace intervalOpt)* : tactic

@[tactic intervalTac] def evalInterval : Tactic := fun stx => do
  let mut cfg : Cfg := {}
  let mut trust : Name := `kernel
  for o in stx[1].getArgs do
    let k := o[1].getId
    let v := o[3]
    let n := v.isNatLit?
    if k == `depth then cfg := { cfg with depth := n.getD cfg.depth }
    else if k == `maxBoxes then cfg := { cfg with maxBoxes := n.getD cfg.maxBoxes }
    else if k == `chunk then cfg := { cfg with chunk := n.getD cfg.chunk }
    else if k == `order then cfg := { cfg with order := n.getD cfg.order }
    else if k == `deriv then cfg := { cfg with deriv := v.getId != `false }
    else if k == `trust then trust := v.getId
    else throwErrorAt o "interval: unknown option {k} (expected depth, maxBoxes, chunk, deriv, \
      order, trust)"
  RealFP.withTrust trust do
  evalTactic (← `(tactic| intros))
  evalTactic (← `(tactic| try simp only [Set.mem_Icc, Set.mem_Ioo, Set.mem_Ico, Set.mem_Ioc,
    ge_iff_le, gt_iff_lt] at *))
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  intervalCore cfg

end RealFP.IntervalTactic
