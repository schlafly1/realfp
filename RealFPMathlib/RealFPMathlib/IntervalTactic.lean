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
import RealFPMathlib.Opt
import RealFPMathlib.Roots
import RealFPMathlib.Registry
import RealFPMathlib.Trust
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.CasesM
import Batteries.Data.BinaryHeap

open Lean Meta Elab Tactic
open Interval64.KF

namespace RealFP.IntervalTactic

initialize registerTraceClass `interval

theorem inBoxes_nil : InBoxes [] [] ↔ True := ⟨fun _ => trivial, fun _ => List.Forall₂.nil⟩

theorem inBoxes_cons {x : ℝ} {xs : List ℝ} {b : ℚ × ℚ} {bs : List (ℚ × ℚ)} :
    InBoxes (x :: xs) (b :: bs) ↔ ((b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)) ∧ InBoxes xs bs :=
  List.forall₂_cons

theorem close_le {a b A B : ℝ} (h : A ≤ B) (ha : a = A) (hb : b = B) : a ≤ b := ha ▸ hb ▸ h
theorem close_lt {a b A B : ℝ} (h : A < B) (ha : a = A) (hb : b = B) : a < b := ha ▸ hb ▸ h
theorem le_of_sub {a b : ℝ} (h : a - b ≤ 0) : a ≤ b := sub_nonpos.mp h
theorem lt_of_sub {a b : ℝ} (h : a - b < 0) : a < b := sub_neg.mp h
theorem close_ne {a A : ℝ} (h : A ≠ 0) (ha : a = A) : a ≠ 0 := ha ▸ h
theorem ne_of_sub_ne {a b : ℝ} (h : a - b ≠ 0) : a ≠ b := fun e => h (by rw [e, sub_self])

/-! Everything below is generic in the extension table (`RealFP.Registry`): the native
searches run with the runtime table of the registered functions in the goal. -/

set_option linter.concreteInstances false
variable [ExtTbl]

theorem checkK_split_of {e : IExpr} {g : KI → Bool} {i m : Nat} {l r : Cert} {env : List KI}
    (hm : (!isNaN m && Nat.blt m (2 ^ 64)) = true)
    (hl : checkK e g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) = true)
    (hr : checkK e g r (env.set i ⟨m, (env.getD i zeroK).hi⟩) = true) :
    checkK e g (.split i m l r) env = true := by
  simp only [checkK, hl, hr, Bool.and_true]; exact hm


/-! ### Certificate search (runs the kernel's own evaluator `evalK` natively) -/

def toFl (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)

/-- `evalK` computed with the hardware interval evaluator `evalI` (the C runtime); equal to
`evalK` by `Interval64Proofs.evalK_toI`. Used only by the (untrusted) native searches. -/
def evalF (env : List KI) (e : IExpr) : KI :=
  let r := evalI (env.map fun X => ⟨toFl X.lo, toFl X.hi⟩) e
  ⟨r.lo.toBits.toNat, r.hi.toBits.toNat⟩

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
    if g (evalF env e) then return some .leaf
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
    if g (evalF env e) then return some .leaf
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
        let D := evalF env (e.deriv i)
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

/-! ### Multivariate centred-form certificates (`MCert`, `checkM`) -/

def mLeaves : MCert → Nat
  | .enc _ => 1
  | .d c => dLeaves c
  | .split _ _ l r => mLeaves l + mLeaves r
  | .mono _ _ dc c => dLeaves dc + mLeaves c

def mStats : MCert → Nat × Nat × Nat   -- (splits, mono, centred leaves)
  | .enc (.cen _ _ _) => (0, 0, 1)
  | .enc .nat => (0, 0, 0)
  | .d _ => (0, 0, 0)
  | .split _ _ l r => let a := mStats l; let b := mStats r; (a.1 + b.1 + 1, a.2.1 + b.2.1, a.2.2 + b.2.2)
  | .mono _ _ _ c => let a := mStats c; (a.1, a.2.1 + 1, a.2.2)

def midBits (X : KI) : Option Nat :=
  let lo := toFl X.lo
  let hi := toFl X.hi
  let mid := if (lo + hi).isInf then lo / 2 + hi / 2 else (lo + hi) / 2
  let mid := if mid == 0 then 0 else mid
  if lo ≤ mid && mid ≤ hi && !mid.isNaN && !mid.isInf then some mid.toBits.toNat else none

/-- Nested centred form at the box midpoint (widest variables centred first). -/
def cenCert (env : List KI) : ECert := Id.run do
  let ws := (wideVars env).map fun i =>
    let X := env.getD i zeroK
    (i, toFl X.hi - toFl X.lo)
  let ws := (ws.toArray.qsort (fun a b => a.2 > b.2)).toList
  let mut k : ECert := .nat
  for (i, _) in ws.reverse do
    if let some m := midBits (env.getD i zeroK) then k := .cen i m k
  return k

/-- `encK` with precomputed derivatives `ds[i] = e.deriv i` (same value; for the native search). -/
def encKd (e : IExpr) (ds : Array IExpr) : ECert → List KI → KI
  | .nat, env => evalF env e
  | .cen i m k, env =>
    if cenOK env e i m then
      KI.add (encKd e ds k (env.set i ⟨m, m⟩))
        (KI.mul (evalF env (ds.getD i (e.deriv i))) (KI.sub (env.getD i zeroK) ⟨m, m⟩))
    else evalF env e

def partials (e : IExpr) (n : Nat) : Array IExpr := (List.range n).toArray.map e.deriv

def absMaxF (X : KI) : Float := max (toFl X.lo).abs (toFl X.hi).abs

/-- Split variable: largest `width × |∂ᵢf|` (widest if derivatives are unavailable). -/
def pickSplitM (e : IExpr) (ds : Array IExpr) (env : List KI) : Option (Nat × Nat) := Id.run do
  let dom := domOK env e
  let mut best : Option (Nat × Nat) := none
  let mut bestS : Float := -1
  for i in wideVars env do
    let X := env.getD i zeroK
    let some m := midBits X | continue
    if m == X.lo || m == X.hi then continue
    let w := toFl X.hi - toFl X.lo
    let s := if dom then
        let d := absMaxF (evalF env (ds.getD i (e.deriv i)))
        if d.isNaN || d.isInf then w * 1e300 else w * d + w * 1e-300
      else w
    if s > bestS then
      bestS := s
      best := some (i, m)
  if best.isNone then return pickSplit env
  return best

/-- Does the box pass with the natural or nested centred enclosure? -/
def passM (e : IExpr) (ds : Array IExpr) (g : KI → Bool) (env : List KI) : Bool :=
  g (evalF env e) || (domOK env e && g (encKd e ds (cenCert env) env))

/-- Split with one-step lookahead: prefer the variable whose halves pass (natural or centred
form); ties broken by `pickSplitM`'s `width × |∂ᵢf|` score. -/
def pickSplitLook (e : IExpr) (ds : Array IExpr) (g : KI → Bool) (env : List KI) :
    Option (Nat × Nat) := Id.run do
  let dflt := pickSplitM e ds env
  let ws := wideVars env
  if ws.length < 2 then return dflt
  let mut best := dflt
  let mut bestS : Nat := 0
  if let some (i, m) := dflt then
    let X := env.getD i zeroK
    bestS := (if passM e ds g (env.set i ⟨X.lo, m⟩) then 1 else 0) +
      (if passM e ds g (env.set i ⟨m, X.hi⟩) then 1 else 0)
  if bestS == 2 then return best
  for i in ws do
    let X := env.getD i zeroK
    let some m := midBits X | continue
    if m == X.lo || m == X.hi then continue
    let sc := (if passM e ds g (env.set i ⟨X.lo, m⟩) then 1 else 0) +
      (if passM e ds g (env.set i ⟨m, X.hi⟩) then 1 else 0)
    if sc > bestS then
      bestS := sc
      best := some (i, m)
  return best

/-- Depth-first search for an `MCert`: natural enclosure, nested centred form, monotonicity on
a face, else bisection (variable chosen by `pickSplitM`). -/
partial def searchM (maxEvals : Nat) (e : IExpr) (ds : Array IExpr) (g : KI → Bool) (upper : Bool) :
    Nat → List KI → StateM Nat (Option MCert)
  | depth, env => do
    modify (· + 1)
    if g (evalF env e) then return some (.enc .nat)
    if (← get) ≥ maxEvals then return none
    let dom := domOK env e
    if dom then
      let k := cenCert env
      modify (· + 1)
      if g (encKd e ds k env) then return some (.enc k)
      for i in wideVars env do
        let D := evalF env (ds.getD i (e.deriv i))
        let inc? : Option Bool :=
          if gGe zeroHi D then some true else if gLe zeroLo D then some false else none
        if let some inc := inc? then
          let X := env.getD i zeroK
          let p := if inc == upper then X.hi else X.lo
          if finK p then
            if let some c ← searchM maxEvals e ds g upper depth (env.set i ⟨p, p⟩) then
              return some (.mono i inc .leaf c)
    if depth == 0 || (← get) ≥ maxEvals then return none
    match pickSplitLook e ds g env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i zeroK
      let some l ← searchM maxEvals e ds g upper (depth - 1) (env.set i ⟨X.lo, m⟩) | return none
      let some r ← searchM maxEvals e ds g upper (depth - 1) (env.set i ⟨m, X.hi⟩) | return none
      return some (.split i m l r)

/-! ### Horner form for polynomial objectives (untrusted rewriting; the equality with the
user's expression is proved by `ring_nf` when the goal is matched) -/

/-- Sparse multivariate polynomial: monomials (exponent list, coefficient). -/
abbrev Poly := List (List Nat × ℚ)

def Poly.norm (p : Poly) : Poly := Id.run do
  let mut out : Array (List Nat × ℚ) := #[]
  for (m, c) in p do
    match out.findIdx? (·.1 == m) with
    | some j => out := out.modify j fun (m', c') => (m', c' + c)
    | none => out := out.push (m, c)
  return (out.filter (·.2 != 0)).toList

def expAdd : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: expAdd as bs
  | [], bs => bs
  | as, [] => as

def Poly.mul (p q : Poly) : Poly :=
  Poly.norm (p.flatMap fun (m, c) => q.map fun (m', c') => (expAdd m m', c * c'))

def unitExp (i : Nat) : List Nat := (List.replicate i 0) ++ [1]

partial def toPoly : IExpr → Option Poly
  | .var i => some [(unitExp i, 1)]
  | .rat q => some (if q == 0 then [] else [([], q)])
  | .add a b => do return Poly.norm ((← toPoly a) ++ (← toPoly b))
  | .sub a b => do return Poly.norm ((← toPoly a) ++ (← toPoly b).map fun (m, c) => (m, -c))
  | .neg a => do return (← toPoly a).map fun (m, c) => (m, -c)
  | .mul a b => do return Poly.mul (← toPoly a) (← toPoly b)
  | .div a (.rat q) => do
    if q == 0 then none
    return (← toPoly a).map fun (m, c) => (m, c / q)
  | .pow a n => do
    let pa ← toPoly a
    let mut r : Poly := [([], 1)]
    for _ in [0:n] do r := Poly.mul r pa
    return r
  | _ => none

def expGet (m : List Nat) (i : Nat) : Nat := m.getD i 0
def expDrop (m : List Nat) (i : Nat) : List Nat := m.set i 0

def varPow (v d : Nat) : IExpr := if d == 1 then .var v else .pow (.var v) d

/-- Horner form, variables taken in the order `vs` (nested Horner for the coefficients). -/
partial def horner (vs : List Nat) (p : Poly) : IExpr :=
  match vs.find? (fun v => p.any fun (m, _) => expGet m v > 0) with
  | none => .rat (p.foldl (fun s (_, c) => s + c) 0)
  | some v =>
    let ks := ((p.map fun (m, _) => expGet m v).eraseDups.toArray.qsort (· < ·)).toList
    let coef (k : Nat) : IExpr :=
      horner vs (p.filterMap fun (m, c) => if expGet m v == k then some (expDrop m v, c) else none)
    let rec build : List Nat → IExpr
      | [] => .rat 0
      | [k] => coef k
      | k :: k' :: rest =>
        let tail := build (k' :: rest)
        let c := coef k
        let t := match tail with
          | .rat 1 => varPow v (k' - k)
          | _ => IExpr.mul (varPow v (k' - k)) tail
        match c with
        | .rat 0 => t
        | _ => .add c t
    let body := build ks
    match ks with
    | k0 :: _ => if k0 == 0 then body else match body with
      | .rat 1 => varPow v k0
      | _ => .mul (varPow v k0) body
    | [] => .rat 0

def polyDeg (p : Poly) (v : Nat) : Nat := p.foldl (fun d (m, _) => max d (expGet m v)) 0

/-- Horner form of a polynomial expression (highest-degree variables outermost), if `e` is a
polynomial and the form differs from `e`. -/
def hornerOf? (e : IExpr) (n : Nat) : Option IExpr := do
  let p ← toPoly e
  let vs := ((List.range n).toArray.qsort (fun a b => polyDeg p a > polyDeg p b)).toList
  some (horner vs p)

/-! ### Branch and bound for the global minimum (untrusted estimate, used for discovery,
witnesses and error messages; every claim is re-proved by a certificate) -/

structure BBNode where
  key : Float        -- negated lower bound (the binary heap pops the maximum)
  lb : Float
  depth : Nat
  env : List KI

instance : Ord BBNode := ⟨fun a b => if a.key < b.key then .lt else if b.key < a.key then .gt else .eq⟩

structure BBResult where
  /-- Lower bound for the minimum of `±f` from the interval enclosures (not yet certified). -/
  lower : Float
  /-- Upper bound: rigorous enclosure upper end of `±f` at `arg`. -/
  upper : Float
  /-- Approximate minimiser (float points inside the box). -/
  arg : List Float
  boxes : Nat
  deriving Inhabited

def fixNaN (x d : Float) : Float := if x.isNaN then d else x

/-- Lower bound of `s·e` on `env` (`s = -1` if `maximize`): natural and nested centred forms. -/
def bbLower (e : IExpr) (ds : Array IExpr) (maximize : Bool) (env : List KI) : Float :=
  let F := evalF env e
  let a := if maximize then -(toFl F.hi) else toFl F.lo
  let a := fixNaN a (-1.0/0.0)
  if domOK env e then
    let G := encKd e ds (cenCert env) env
    let b := fixNaN (if maximize then -(toFl G.hi) else toFl G.lo) (-1.0/0.0)
    max a b
  else a

def midEnv (env : List KI) : List KI :=
  env.map fun X => match midBits X with | some m => ⟨m, m⟩ | none => ⟨X.lo, X.lo⟩

/-- Rigorous upper bound of `s·e` at the midpoint of `env`. -/
def bbUpperAt (e : IExpr) (maximize : Bool) (env : List KI) : Float × List Float :=
  let pe := midEnv env
  let F := evalF pe e
  let u := fixNaN (if maximize then -(toFl F.lo) else toFl F.hi) (1.0/0.0)
  (u, pe.map fun X => toFl X.lo)

/-- Rigorous upper bound of `s·e` at a float point. -/
def bbUpperPt (e : IExpr) (maximize : Bool) (p : List Float) : Float :=
  let F := evalF (p.map fun x => (⟨x.toBits.toNat, x.toBits.toNat⟩ : KI)) e
  fixNaN (if maximize then -(toFl F.lo) else toFl F.hi) (1.0/0.0)

/-- Local pattern search from `p` inside `env0` (improves the reported minimiser). -/
def refineArg (e : IExpr) (maximize : Bool) (env0 : List KI) (p : List Float) (u : Float) :
    Float × List Float := Id.run do
  let n := p.length
  let los := env0.map fun X => toFl X.lo
  let his := env0.map fun X => toFl X.hi
  let mut cur := p.toArray
  let mut best := u
  let mut step : Array Float := (List.range n).toArray.map fun i =>
    (his.getD i 0 - los.getD i 0) / 64
  for _ in [0:4000] do
    let mut moved := false
    for i in [0:n] do
      for sgn in [1.0, -1.0] do
        let x := cur[i]! + sgn * step[i]!
        let x := max (los.getD i 0) (min (his.getD i 0) x)
        let cand := cur.set! i x
        let v := bbUpperPt e maximize cand.toList
        if v < best then
          best := v; cur := cand; moved := true
    if !moved then
      step := step.map (· / 2)
      if step.all fun st => st < 1e-17 then break
  return (best, cur.toList)

/-- Best-first branch and bound for `min (±e)` on `env0`; stops when the gap is below `tol`
(absolute, plus `tol·|upper|`) or after `maxBoxes` boxes. -/
partial def bnbMin (e : IExpr) (maximize : Bool) (env0 : List KI) (maxBoxes : Nat := 20000)
    (tol : Float := 1e-9) (maxDepth : Nat := 200) : BBResult := Id.run do
  let ds := partials e env0.length
  let lb0 := bbLower e ds maximize env0
  let (u0, a0) := bbUpperAt e maximize env0
  let mut heap : Batteries.BinaryHeap BBNode := Batteries.BinaryHeap.empty
  heap := heap.insert ⟨-lb0, lb0, 0, env0⟩
  let mut U := u0
  let mut arg := a0
  let mut n := 1
  let mut lower := lb0
  let mut stalled : Float := 1.0/0.0   -- min lower bound of boxes that cannot be split further
  while true do
    let (top?, h') := heap.extractMax
    heap := h'
    let some nd := top? | do lower := min stalled U; break
    lower := min nd.lb stalled
    if nd.lb ≥ U - tol * (1 + U.abs) || n ≥ maxBoxes then
      break
    if nd.depth ≥ maxDepth then
      stalled := min stalled nd.lb; continue
    match pickSplitM e ds nd.env with
    | none => stalled := min stalled nd.lb
    | some (i, m) =>
      let X := nd.env.getD i zeroK
      for ch in [nd.env.set i ⟨X.lo, m⟩, nd.env.set i ⟨m, X.hi⟩] do
        n := n + 1
        let lb := bbLower e ds maximize ch
        let (u, a) := bbUpperAt e maximize ch
        if u < U then U := u; arg := a
        if lb < U then heap := heap.insert ⟨-lb, lb, nd.depth + 1, ch⟩
  let (U', arg') := refineArg e maximize env0 arg U
  return { lower := min lower U', upper := U', arg := arg', boxes := n }

/-! ### Numbers for messages -/

def floatRat? (x : Float) : Option ℚ := Interval64.Spec.bitsToRat? x.toBits

def qToF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- `q` as a decimal if its denominator is a power of ten, else `num/den`. -/
def fmtRat (q : ℚ) : String := Id.run do
  if q.den == 1 then return s!"{q.num}"
  let some k := (List.range 40).find? (fun k => (10 ^ k) % q.den == 0) |
    return s!"{q.num}/{q.den}"
  let num : Int := q.num * ((10 ^ k / q.den : Nat) : Int)
  let a := toString num.natAbs
  let a := if a.length ≤ k then String.ofList (List.replicate (k + 1 - a.length) '0') ++ a else a
  let i := a.length - k
  let s := String.ofList (a.toList.take i) ++ "." ++ String.ofList (a.toList.drop i)
  return (if q.num < 0 then "-" else "") ++ s

/-- Decimal string of a float with `d` significant digits (for messages). -/
def fmtFloat (x : Float) : String :=
  if x.isNaN then "NaN" else if x.isInf then (if x > 0 then "∞" else "-∞") else
  match floatRat? x with
  | none => toString x
  | some q =>
    -- 12 significant digits
    let a := q.num.natAbs
    if a == 0 then "0" else
    let e := (Float.log10 x.abs).floor
    let k : Int := 11 - e.toInt64.toInt
    let scaled : ℚ := if k ≥ 0 then q * (10 ^ k.toNat : ℚ) else q / (10 ^ (-k).toNat : ℚ)
    let r : Int := (scaled + (if q ≥ 0 then 1/2 else -1/2)).floor
    let neg := r < 0
    let ds := (toString r.natAbs).toList
    let zeros (n : Nat) : List Char := List.replicate n '0'
    let cs : List Char := if k ≤ 0 then ds ++ zeros (-k).toNat
      else if ds.length > k.toNat then
        let i := ds.length - k.toNat
        ds.take i ++ ['.'] ++ ds.drop i
      else ['0', '.'] ++ zeros (k.toNat - ds.length) ++ ds
    let cs := if cs.contains '.' then
        let t := (cs.reverse.dropWhile (· == '0'))
        (if t.head? == some '.' then t.tail else t).reverse
      else cs
    let s := String.ofList cs
    (if neg then "-" else "") ++ s


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
  | .ext k d a => mkApp3 (mkConst ``IExpr.ext) (toExpr k) (iexprToExpr d) (iexprToExpr a)

partial def dcertToExpr : DCert → Expr
  | .leaf => mkConst ``DCert.leaf
  | .split i m l r => mkApp4 (mkConst ``DCert.split) (toExpr i) (toExpr m) (dcertToExpr l) (dcertToExpr r)
  | .mono i inc dc c => mkApp4 (mkConst ``DCert.mono) (toExpr i) (toExpr inc) (dcertToExpr dc) (dcertToExpr c)
  | .center i m => mkApp2 (mkConst ``DCert.center) (toExpr i) (toExpr m)

partial def ecertToExpr : ECert → Expr
  | .nat => mkConst ``ECert.nat
  | .cen i m k => mkApp3 (mkConst ``ECert.cen) (toExpr i) (toExpr m) (ecertToExpr k)

partial def mcertToExpr : MCert → Expr
  | .enc k => mkApp (mkConst ``MCert.enc) (ecertToExpr k)
  | .d c => mkApp (mkConst ``MCert.d) (dcertToExpr c)
  | .split i m l r => mkApp4 (mkConst ``MCert.split) (toExpr i) (toExpr m) (mcertToExpr l) (mcertToExpr r)
  | .mono i inc dc c => mkApp4 (mkConst ``MCert.mono) (toExpr i) (toExpr inc) (dcertToExpr dc) (mcertToExpr c)

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
  | _ =>
    -- registered functions (`@[realfp_fn]`, see `RealFPMathlib.Registry`)
    if let .const c _ := e.getAppFn then
      if e.getAppNumArgs == 1 then
        if let some en ← findEntry? c then
          let F ← evalExtFn en.ext
          return .ext en.key F.deriv (← r e.appArg!)
    throwError "interval: cannot interpret {e} (variables need numeral bounds in context)"

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
  let ids ← (← extSimpLemmas).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let ext ← if ids.isEmpty then `(tactic| skip) else `(tactic| try simp only [$ids,*])
  evalTactic (← `(tactic|
    first
    | rfl
    | ((try simp only [Interval64.KF.IExpr.denote, List.getD_cons_zero, List.getD_cons_succ]); $ext:tactic
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
      let lem := mkAppN (← mkC ``checkK_split_of)
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
    let chk := mkApp4 (← mkC ``checkK) eE gE (certToExpr cert) envE
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
      let lem := mkAppN (← mkC ``RealFP.checkD_split_of)
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
    let chk := mkApp5 (← mkC ``checkD) eE gE upperE (dcertToExpr cert) envE
    let hM ← mkFreshExprMVar (← mkEq chk (mkConst ``Bool.true))
    let saved ← getGoals
    setGoals [hM.mvarId!]
    RealFP.closeCheck
    setGoals saved
    instantiateMVars hM

partial def proveCheckM (chunk : Nat) (eE gE upperE : Expr) (cert : MCert) (envE : Expr) :
    TacticM Expr := do
  match cert with
  | .split i m l r =>
    if mLeaves cert > chunk then
      let lem := mkAppN (← mkC ``RealFP.checkM_split_of)
        #[eE, gE, upperE, toExpr i, toExpr m, mcertToExpr l, mcertToExpr r, envE]
      let ty ← inferType lem
      let .forallE _ _ b1 _ := ty | throwError "interval: internal (split lemma)"
      let .forallE _ hlT b2 _ := b1 | throwError "interval: internal (split lemma)"
      let .forallE _ hrT _ _ := b2 | throwError "interval: internal (split lemma)"
      let hm ← mkEqRefl (mkConst ``Bool.true)
      let getEnv (t : Expr) : MetaM Expr := do
        let some (_, lhs, _) := t.eq? | throwError "interval: internal (env)"
        return lhs.appArg!
      let hl ← proveCheckM chunk eE gE upperE l (← getEnv hlT)
      let hr ← proveCheckM chunk eE gE upperE r (← getEnv hrT)
      return mkAppN lem #[hm, hl, hr]
    else leafChunk
  | _ => leafChunk
where
  leafChunk : TacticM Expr := do
    let chk := mkApp5 (← mkC ``checkM) eE gE upperE (mcertToExpr cert) envE
    let hM ← mkFreshExprMVar (← mkEq chk (mkConst ``Bool.true))
    let saved ← getGoals
    setGoals [hM.mvarId!]
    RealFP.closeCheck
    setGoals saved
    instantiateMVars hM

/-- Certificate search for `interval` bounds: the derivative search (`searchD`) with a small
budget, then the multivariate centred-form search (`searchM`), then `searchD` with the full
budget. Returns the certificate and the number of native evaluations. -/
def findCertDM (cfg : Cfg) (e : IExpr) (g : KI → Bool) (upper : Bool) (nvars : Nat)
    (env : List KI) : Option (IExpr × (DCert ⊕ MCert)) × Nat := Id.run do
  let full := 2 * cfg.maxBoxes
  let b1 := min full 6000
  let (c1, n1) := (searchD cfg.deriv b1 e g upper cfg.order true cfg.depth env).run 0
  if let some c := c1 then return (some (e, .inl c), n1)
  let depthM := cfg.depth + 8 * nvars
  let (c2, n2) := (searchM full e (partials e nvars) g upper depthM env).run 0
  -- polynomial objectives: also try the Horner form and keep the smaller certificate
  let (c2, n2) : Option (IExpr × MCert) × Nat := match hornerOf? e nvars with
    | some h =>
      let (ch, nh) := (searchM full h (partials h nvars) g upper depthM env).run 0
      match c2, ch with
      | some a, some b => (some (if mLeaves b < mLeaves a then (h, b) else (e, a)), n2 + nh)
      | some a, none => (some (e, a), n2 + nh)
      | none, some b => (some (h, b), n2 + nh)
      | none, none => (none, n2 + nh)
    | none => (c2.map (e, ·), n2)
  if let some (e', c) := c2 then return (some (e', .inr c), n1 + n2)
  if b1 < full then
    let (c3, n3) := (searchD cfg.deriv full e g upper cfg.order true cfg.depth env).run 0
    if let some c := c3 then return (some (e, .inl c), n1 + n2 + n3)
    return (none, n1 + n2 + n3)
  return (none, n1 + n2)

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
  let (cert?, evals) := findCertDM cfg e g upper vars.size env
  let some (e, cert) := cert? | do
    -- explain with a branch-and-bound estimate of the extremum
    let r := bnbMin e upper env 20000 1e-9
    let (lo, hi, word) := if upper then (-r.upper, -r.lower, "maximum") else (r.lower, r.upper, "minimum")
    let pt := MessageData.joinSep ((vars.toList.zip r.arg).map fun (v, x) =>
      m!"{v} ≈ {fmtFloat x}") ", "
    let cF := qToF c
    let false? := if upper then (if strict then lo ≥ cF else lo > cF)
      else (if strict then hi ≤ cF else hi < cF)
    let expl := if false? then
        m!"the bound is false: the {word} is ≈ {fmtFloat (if upper then lo else hi)} at {pt} \
          (rigorous value at that point), beyond {fmtFloat cF}"
      else
        m!"the {word} on the box is in [{fmtFloat lo}, {fmtFloat hi}] (branch and bound, \
          attained near {pt}), so the bound {fmtFloat cF} has a margin of only \
          {fmtFloat (if upper then cF - hi else lo - cF)}; loosen it or raise (depth := _) / \
          (maxBoxes := _)"
    throwError "interval: no certificate within depth {cfg.depth} / {cfg.maxBoxes} boxes \
      ({evals} evaluations): {expl}"
  -- the (untrusted, native) search above does not count against `maxHeartbeats`
  withCurrHeartbeats do
    let leaves := match cert with | .inl c => dLeaves c | .inr c => mLeaves c
    if leaves > cfg.maxBoxes then
      throwError "interval: certificate needs {leaves} boxes > maxBoxes {cfg.maxBoxes}"
    let stMsg : MessageData := match cert with
      | .inl c =>
        let st := dStats c
        m!"{st.1} splits, {st.2.1} mono, {st.2.2} centred"
      | .inr c =>
        let st := mStats c
        m!"{st.1} splits, {st.2.1} mono, {st.2.2} multivariate centred"
    trace[interval] "{vars.size} variable(s), {leaves} boxes ({stMsg}), {evals} native evaluations"
    let eE := iexprToExpr e
    let bsE := toExpr bs.toList
    let cE := toExpr c
    let xsE ← mkListLit (mkConst ``Real) vars.toList
    let kc := mkApp (mkConst (if upper then ``KI.lo else ``KI.hi)) (mkApp (mkConst ``KI.ofRat) cE)
    let gE := mkApp (mkConst gName) kc
    let envE := mkApp (mkConst ``boxes) bsE
    let saved ← getGoals
    let hxsTy := mkApp2 (mkConst ``InBoxes) xsE bsE
    let hxsM ← mkFreshExprMVar hxsTy
    let pf ← match cert with
      | .inl dc => do
        let hM ← proveCheckD cfg.chunk eE gE (toExpr upper) dc envE
        setGoals [hxsM.mvarId!]; inBoxesTac; setGoals saved
        pure (mkAppN (← mkC pName) #[eE, bsE, cE, dcertToExpr dc, hM, xsE, hxsM])
      | .inr mc => do
        let hM ← proveCheckM cfg.chunk eE gE (toExpr upper) mc envE
        setGoals [hxsM.mvarId!]; inBoxesTac; setGoals saved
        let pM := match strict, upper with
          | false, true => ``proveM_le | true, true => ``proveM_lt
          | false, false => ``proveM_ge | true, false => ``proveM_gt
        pure (mkAppN (← mkC pM) #[eE, bsE, cE, mcertToExpr mc, hM, xsE, hxsM])
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
  let pf := mkAppN (← mkC ``RealFP.Roots.prove_ne) #[eE, bsE, certE, hM, xsE, hxsM]
  let goal ← getMainGoal
  let ha ← mkFreshExprMVar (← mkEq f (mkApp2 (← mkC ``IExpr.denote) xsE eE))
  goal.assign (mkAppN (mkConst ``close_ne) #[f, mkApp2 (← mkC ``IExpr.denote) xsE eE, pf, ha])
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
  let mut trust : Name := `inherit
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
  RealFP.requireNative
  RealFP.withTrust trust do
  -- keep the user's binder names (`x`, not `x✝`) so messages can refer to them
  liftMetaTactic fun g => do
    let (_, g) ← g.introNP (getIntrosSize (← instantiateMVars (← g.getType)))
    return [g]
  evalTactic (← `(tactic| try simp only [Set.mem_Icc, Set.mem_Ioo, Set.mem_Ico, Set.mem_Ioc,
    ge_iff_le, gt_iff_lt] at *))
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  withRegistered (intervalCore cfg)

end RealFP.IntervalTactic
