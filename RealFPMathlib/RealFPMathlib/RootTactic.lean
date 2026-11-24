/-
Root tactics: `root_exists` and `root_unique`.

```
example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by root_exists
example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by root_unique
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by root_unique
```

Accepted goals: `∃ p, P p` / `∃! p, P p` where `p : ℝ`, `ℝ × ℝ`, `ℝ × ℝ × ℝ` or `Fin n → ℝ`, and
`P p` is a conjunction (any order) of one closed box per coordinate (`c ∈ Set.Icc a b`, or
`a ≤ c` and `c ≤ b`, numerals `a`, `b`) and `n` equations `L = R` between `interval`
expressions in the coordinates `c`.

Methods (certificates are found natively and checked by `decide +kernel`, or `native_decide`
with `(trust := native)`):
* one variable, `∃`: a sign change on the box or on a sub-interval found by a grid scan
  (intermediate value theorem, `RealFP.Roots.ivt_exists_in`);
* one variable, `∃!`: a sign change plus a strict sign of `f'` on the whole box, proved with the
  derivative certificates of `interval` (`RealFP.Roots.unique_one`); falls back to Krawczyk;
* `n` variables: the Krawczyk test with a contraction bound (`RealFP.Roots.kraw_existsUnique`);
  for `∃` also on a small box around a Newton approximation (`kraw_exists_in`).
-/
import RealFPMathlib.IntervalTactic
import RealFPMathlib.Krawczyk
import RealFPMathlib.I128Kraw

open Lean Meta Elab Tactic
open Interval64.KF RealFP RealFP.Roots RealFP.IntervalTactic

namespace RealFP.RootTactic

/-! ### Bridging lemmas -/

theorem icc_iff {x c a b : ℝ} {qa qb : ℚ} (hc : x = c) (ha : a = (qa : ℝ)) (hb : b = (qb : ℝ)) :
    x ∈ Set.Icc a b ↔ ((qa : ℝ) ≤ c ∧ c ≤ (qb : ℝ)) := by
  subst hc ha hb; exact Set.mem_Icc

theorem lo_iff {x c a : ℝ} {qa : ℚ} (hc : x = c) (ha : a = (qa : ℝ)) :
    a ≤ x ↔ (qa : ℝ) ≤ c := by subst hc ha; rfl

theorem hi_iff {x c b : ℝ} {qb : ℚ} (hc : x = c) (hb : b = (qb : ℝ)) :
    x ≤ b ↔ c ≤ (qb : ℝ) := by subst hc hb; rfl

theorem eq_iff_sub {L R D : ℝ} (h : L - R = D) : L = R ↔ D = 0 := by
  rw [← h, sub_eq_zero]

theorem inBoxes_cons' {x : ℝ} {xs : List ℝ} {b : ℚ × ℚ} {bs : List (ℚ × ℚ)} :
    InBoxes (x :: xs) (b :: bs) ↔ ((b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)) ∧ InBoxes xs bs :=
  List.forall₂_cons
theorem inBoxes_nil' : InBoxes [] [] ↔ True := ⟨fun _ => trivial, fun _ => List.Forall₂.nil⟩
set_option linter.concreteInstances false
variable [ExtTbl]

section
variable [ExtSem]
theorem allZero_cons {e : IExpr} {es : List IExpr} {xs : List ℝ} :
    AllZero (e :: es) xs ↔ e.denote xs = 0 ∧ AllZero es xs := List.forall_mem_cons
theorem allZero_nil {xs : List ℝ} : AllZero [] xs ↔ True := by simp [AllZero]
end

/-! ### Native helpers (untrusted search) -/

def ratOfF (x : Float) : Option ℚ := Interval64.Spec.bitsToRat? x.toBits

def midF (X : KI) : Float :=
  let lo := toFl X.lo
  let hi := toFl X.hi
  if lo == hi then lo else lo / 2 + hi / 2

def evalAt (e : IExpr) (xs : List ℚ) : Float := midF (evalK (boxes (ptBoxes xs)) e)

def jacAt (Fs : List IExpr) (n : Nat) (xs : List ℚ) : Array (Array Float) :=
  (List.range n).toArray.map fun k => (List.range n).toArray.map fun j =>
    evalAt ((fget Fs k).deriv j) xs

/-- Solve `A X = B` by Gaussian elimination with partial pivoting (Float, untrusted). -/
def gauss (A B : Array (Array Float)) : Option (Array (Array Float)) := Id.run do
  let n := A.size
  let mut M : Array (Array Float) := (List.range n).toArray.map fun i => A[i]! ++ B[i]!
  for c in [0:n] do
    let mut p := c
    let mut best := (M[c]!)[c]!.abs
    for r in [c+1:n] do
      if (M[r]!)[c]!.abs > best then
        p := r
        best := (M[r]!)[c]!.abs
    if best == 0 || best.isNaN || best.isInf then return none
    let tmp := M[c]!
    M := M.set! c M[p]!
    M := M.set! p tmp
    let piv := (M[c]!)[c]!
    let rowc := (M[c]!).map (· / piv)
    M := M.set! c rowc
    for r in [0:n] do
      if r != c then
        let f := (M[r]!)[c]!
        let row := M[r]!
        M := M.set! r ((List.range row.size).toArray.map fun t => row[t]! - f * rowc[t]!)
  return some (M.map fun row => row.extract n row.size)

def identF (n : Nat) : Array (Array Float) :=
  (List.range n).toArray.map fun i => (List.range n).toArray.map fun j => if i == j then 1 else 0

def toQ (x : Float) : Except String ℚ :=
  match ratOfF x with
  | some q => pure q
  | none => throw "a non-finite value appeared"

def qToF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

def fmtQ (q : ℚ) : String :=
  if q.den == 1 then toString q.num
  else if q.den ≤ 1000000 then s!"{q.num}/{q.den}"
  else toString (qToF q)

def fmtBox (bs : List (ℚ × ℚ)) : String :=
  " × ".intercalate (bs.map fun b => s!"[{fmtQ b.1}, {fmtQ b.2}]")

/-- Newton iteration from `x0` (Float; `none` if it breaks down). -/
def newton (Fs : List IExpr) (n : Nat) (x0 : List ℚ) (iters : Nat := 60) : Option (List ℚ) :=
  Id.run do
    let mut x := x0
    for _ in [0:iters] do
      let F := (List.range n).toArray.map fun k => #[evalAt (fget Fs k) x]
      let some d := gauss (jacAt Fs n x) F | return none
      let xf := x.toArray.mapIdx fun i q => qToF q - (d[i]!)[0]!
      let some xq := xf.toList.mapM ratOfF | return none
      if xq == x then return some x
      x := xq
    return some x

/-- Try to build a Krawczyk certificate on `bs` around the centre `m`. -/
def tryKraw (Fs : List IExpr) (bs : List (ℚ × ℚ)) (m : List ℚ) : Except String KCert := do
  let n := bs.length
  let Jm := jacAt Fs n m
  let some Yf := gauss Jm (identF n) |
    throw "the Jacobian at the centre is singular (or not finite)"
  let Y ← Yf.toList.mapM fun row => row.toList.mapM toQ
  let Z ← Jm.toList.mapM fun row => row.toList.mapM toQ
  let B := bEnv n Fs m
  let J := jEnv n Fs bs
  let envT := boxes (unitBoxes n) ++ boxes (ptBoxes m) ++ B ++ J
  let mut qf : Float := 0
  for i in [0:n] do
    for F in [evalK envT (tE n Y i), evalK envT (nE n Y Z i)] do
      let lo := toFl F.lo
      let hi := toFl F.hi
      if lo.isNaN || hi.isNaN || lo.isInf || hi.isInf then
        throw s!"the interval Jacobian is not finite on the box (row {i})"
      qf := max qf (max lo.abs hi.abs)
  if qf ≥ 1 then
    throw s!"contraction factor ‖I - Y·J(X)‖∞ ≈ {qf} ≥ 1 (box too wide or Jacobian too \
      ill-conditioned)"
  let q ← toQ (qf + (1 - qf) / 4)
  let env := boxes bs ++ boxes (ptBoxes m) ++ B ++ J
  for i in [0:n] do
    let K := evalK env (kE n Y i)
    let b := bs.getD i (0, 0)
    unless inLH b.1 b.2 K do
      throw s!"Krawczyk image of coordinate {i} is [{toFl K.lo}, {toFl K.hi}], not inside \
        [{fmtQ b.1}, {fmtQ b.2}]"
  let c : KCert := { m, Y, Z, q, B, J }
  unless krawCheck Fs bs c do throw "internal: the certificate was rejected by `krawCheck`"
  return c

def midQ (bs : List (ℚ × ℚ)) : List ℚ := bs.map fun b => (b.1 + b.2) / 2

def inBoxQ (bs : List (ℚ × ℚ)) (x : List ℚ) : Bool :=
  x.length == bs.length && (List.zip x bs).all fun (v, b) => decide (b.1 ≤ v ∧ v ≤ b.2)

/-- Starting points for Newton: the midpoint, then a `g^n` grid of cell centres (g = 2, 4). -/
def starts (bs : List (ℚ × ℚ)) : List (List ℚ) := Id.run do
  let mut out := [midQ bs]
  for g in [2, 4] do
    let pts : List (List ℚ) := bs.foldr (fun b acc =>
      (List.range g).flatMap fun i =>
        acc.map fun rest => (b.1 + (b.2 - b.1) * ((2 * i + 1 : ℚ) / (2 * g))) :: rest) [[]]
    out := out ++ pts
  return out

/-- A Newton approximation to a root inside `bs` (residual below `1e-9`), from several starts. -/
def newtonIn (Fs : List IExpr) (bs : List (ℚ × ℚ)) : Option (List ℚ) := Id.run do
  let n := bs.length
  for x0 in starts bs do
    if let some x := newton Fs n x0 then
      let res := (List.range n).foldl (fun a k => max a (evalAt (fget Fs k) x).abs) 0
      if inBoxQ bs x && res < 1e-9 then return some x
  return none

/-- A small box around `x` inside `bs` (relative radius `r`), with float endpoints. -/
def boxAround (bs : List (ℚ × ℚ)) (x : List ℚ) (r : Float) : Option (List (ℚ × ℚ)) :=
  (List.zip x bs).mapM fun (v, b) => do
    let vf := qToF v
    let w := r * max 1 vf.abs
    let lo ← ratOfF (vf - w)
    let hi ← ratOfF (vf + w)
    pure (max b.1 lo, min b.2 hi)

/-- Krawczyk on the whole box: centre = midpoint, then a Newton approximation. -/
def krawWhole (Fs : List IExpr) (bs : List (ℚ × ℚ)) : Except String KCert := do
  let m := midQ bs
  match tryKraw Fs bs m with
  | .ok c => return c
  | .error e1 =>
    match newtonIn Fs bs with
    | some x =>
      match tryKraw Fs bs x with
      | .ok c => return c
      | .error e2 => throw s!"centre = midpoint: {e1}; centre = Newton point: {e2}"
    | none => throw s!"{e1}; Newton's method found no root inside the box"

/-- Krawczyk on a sub-box around a Newton approximation (existence only). -/
def krawSub (Fs : List IExpr) (bs : List (ℚ × ℚ)) : Except String (List (ℚ × ℚ) × KCert) := do
  let some x := newtonIn Fs bs | throw "no approximate root inside the box for a sub-box"
  let mut last := ""
  for r in [1e-12, 1e-9, 1e-6, 1e-3] do
    if let some bs' := boxAround bs x r then
      match tryKraw Fs bs' x with
      | .ok c => return (bs', c)
      | .error e => last := e
  throw s!"no Krawczyk certificate near the Newton point: {last}"

/-! ### Krawczyk at precision 128 (untrusted search) -/

def dyMidQ (X : Interval128.Dy.DI) : Option ℚ :=
  match X.lo, X.hi with
  | some a, some b => some ((Interval128.Dy.toRat a + Interval128.Dy.toRat b) / 2)
  | _, _ => none

def magQ (X : Interval128.Dy.DI) : Option ℚ :=
  match X.lo, X.hi with
  | some a, some b => some (max |Interval128.Dy.toRat a| |Interval128.Dy.toRat b|)
  | _, _ => none

/-- Round to a multiple of `2^-k`. -/
def roundQ (q : ℚ) (k : Nat := 160) : ℚ := ((q * 2 ^ k).floor : ℚ) / 2 ^ k

def evalAtQ (e : IExpr) (xs : List ℚ) : Option ℚ :=
  dyMidQ (Interval128.Dy.evalQ (Interval128.Dy.boxes (ptBoxes xs)) e)

/-- Simplified Newton `x ← x - Y F(x)` with a fixed rational `Y`, in 128-bit arithmetic. -/
def newtonQ (Fs : List IExpr) (n : Nat) (Y : List (List ℚ)) (x0 : List ℚ) (iters : Nat := 10) :
    Option (List ℚ) := Id.run do
  let mut x := x0
  for _ in [0:iters] do
    let some F := (List.range n).mapM fun k => evalAtQ (fget Fs k) x | return none
    let x' := (List.range n).map fun i =>
      roundQ (x.getD i 0 - ((List.range n).map fun k => qget Y i k * F.getD k 0).sum)
    if x' == x then return some x
    x := x'
  return some x

/-- `Y ≈ F'(x)⁻¹` and `Z ≈ F'(x)` from binary64. -/
def yzAt (Fs : List IExpr) (n : Nat) (x : List ℚ) : Except String (List (List ℚ) × List (List ℚ)) := do
  let Jm := jacAt Fs n x
  let some Yf := gauss Jm (identF n) |
    throw "the Jacobian at the centre is singular (or not finite)"
  let Y ← Yf.toList.mapM fun row => row.toList.mapM toQ
  let Z ← Jm.toList.mapM fun row => row.toList.mapM toQ
  return (Y, Z)

/-- Try a 128-bit Krawczyk certificate on `bs` around the centre `m`. -/
def tryKrawQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) (m : List ℚ) :
    Except String RealFP.I128Q.KCertQ := do
  let n := bs.length
  let (Y, Z) ← yzAt Fs n m
  let B := RealFP.I128Q.bEnvQ n Fs m
  let J := RealFP.I128Q.jEnvQ n Fs bs
  let envT := Interval128.Dy.boxes (unitBoxes n) ++ Interval128.Dy.boxes (ptBoxes m) ++ B ++ J
  let mut qm : ℚ := 0
  for i in [0:n] do
    for F in [Interval128.Dy.evalQ envT (tE n Y i), Interval128.Dy.evalQ envT (nE n Y Z i)] do
      let some v := magQ F | throw s!"the interval Jacobian is not finite on the box (row {i})"
      qm := max qm v
  if qm ≥ 1 then
    throw s!"contraction factor ‖I - Y·J(X)‖∞ ≈ {qToF qm} ≥ 1 (box too wide or Jacobian too \
      ill-conditioned)"
  let q : ℚ := ((((qm + (1 - qm) / 4) * 2 ^ 64).ceil : ℤ) : ℚ) / 2 ^ 64
  let env := Interval128.Dy.boxes bs ++ Interval128.Dy.boxes (ptBoxes m) ++ B ++ J
  for i in [0:n] do
    let K := Interval128.Dy.evalQ env (kE n Y i)
    let b := bs.getD i (0, 0)
    unless RealFP.I128Q.inLHQ b.1 b.2 K do
      throw s!"Krawczyk image of coordinate {i} is {K.toString}, not inside [{fmtQ b.1}, {fmtQ b.2}]"
  let c : RealFP.I128Q.KCertQ := { m, Y, Z, q }
  unless RealFP.I128Q.krawCheckQ Fs bs c do
    throw "internal: the certificate was rejected by `krawCheckQ`"
  return c

/-- Centres to try at 128: Newton points (binary64 Newton, then 128-bit refinement) from the
midpoint and the start grid, then the midpoint. -/
def centresQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) : List (List ℚ) := Id.run do
  let n := bs.length
  let mut out : Array (List ℚ) := #[]
  for x0 in starts bs do
    let x1 := (newton Fs n x0).getD x0
    for x in [x1, x0] do
      if let .ok (Y, _) := yzAt Fs n x then
        if let some x' := newtonQ Fs n Y (x.map roundQ) then
          if inBoxQ bs x' && !out.contains x' then out := out.push x'
    if out.size ≥ 2 then break
  return out.toList ++ [midQ bs]

def krawWholeQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) : Except String RealFP.I128Q.KCertQ := do
  let mut errs : Array String := #[]
  for m in centresQ Fs bs do
    match tryKrawQ Fs bs m with
    | .ok c => return c
    | .error e => errs := errs.push e
  throw ("; ".intercalate errs.toList)

def krawSubQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) :
    Except String (List (ℚ × ℚ) × RealFP.I128Q.KCertQ) := do
  let cs := (centresQ Fs bs).dropLast
  if cs.isEmpty then throw "no approximate root inside the box for a sub-box"
  let mut last := ""
  for x in cs do
    for k in [30, 26, 22, 18, 14, 10, 6] do
      let r : ℚ := 1 / 10 ^ k
      let bs' := (List.zip x bs).map fun (v, b) =>
        let w := r * max 1 |v|
        (max b.1 (v - w), min b.2 (v + w))
      match tryKrawQ Fs bs' x with
      | .ok c => return (bs', c)
      | .error e => last := e
  throw s!"no Krawczyk certificate near the Newton point: {last}"

/-! ### Goal analysis -/

inductive PtKind where
  | real | prod2 | prod3 | fin (n : Nat)

def ptKind (T : Expr) : MetaM (Option PtKind) := do
  let T ← whnfR T
  if T.isConstOf ``Real then return some .real
  match T.getAppFnArgs with
  | (``Prod, #[A, B]) =>
    unless (← whnfR A).isConstOf ``Real do return none
    if (← whnfR B).isConstOf ``Real then return some .prod2
    match (← whnfR B).getAppFnArgs with
    | (``Prod, #[C, D]) =>
      if (← whnfR C).isConstOf ``Real && (← whnfR D).isConstOf ``Real then return some .prod3
      return none
    | _ => return none
  | _ =>
    match T with
    | .forallE _ dom body _ =>
      if body.hasLooseBVars || !(← whnfR body).isConstOf ``Real then return none
      match (← whnfR dom).getAppFnArgs with
      | (``Fin, #[nE]) =>
        let some n ← natOf? nE | return none
        return some (.fin n)
      | _ => return none
    | _ => return none

def coordsOf (k : PtKind) (p : Expr) : MetaM (Array Expr) := do
  match k with
  | .real => return #[p]
  | .prod2 => return #[← mkAppM ``Prod.fst #[p], ← mkAppM ``Prod.snd #[p]]
  | .prod3 =>
    let s ← mkAppM ``Prod.snd #[p]
    return #[← mkAppM ``Prod.fst #[p], ← mkAppM ``Prod.fst #[s], ← mkAppM ``Prod.snd #[s]]
  | .fin n =>
    let finT := mkApp (mkConst ``Fin) (toExpr n)
    (List.range n).toArray.mapM fun i => do return mkApp p (← mkNumeral finT i)

/-- `ofL`, `hto`, `hinj` for the point type. -/
def kindLemmas (k : PtKind) : MetaM (Expr × Expr × Expr) := do
  let listR := mkApp (mkConst ``List [Level.zero]) (mkConst ``Real)
  let gd (i : Nat) (xs : Expr) : MetaM Expr := do
    mkAppM ``List.getD #[xs, toExpr i, ← mkNumeral (mkConst ``Real) 0]
  match k with
  | .real =>
    let ofL ← withLocalDeclD `xs listR fun xs => do mkLambdaFVars #[xs] (← gd 0 xs)
    return (ofL, mkConst ``coords1_to, (← mkC ``RealFP.Roots.coords1_inj))
  | .prod2 =>
    let ofL ← withLocalDeclD `xs listR fun xs => do
      mkLambdaFVars #[xs] (← mkAppM ``Prod.mk #[← gd 0 xs, ← gd 1 xs])
    return (ofL, mkConst ``coords2_to, (← mkC ``RealFP.Roots.coords2_inj))
  | .prod3 =>
    let ofL ← withLocalDeclD `xs listR fun xs => do
      mkLambdaFVars #[xs] (← mkAppM ``Prod.mk #[← gd 0 xs, ← mkAppM ``Prod.mk #[← gd 1 xs, ← gd 2 xs]])
    return (ofL, mkConst ``coords3_to, (← mkC ``RealFP.Roots.coords3_inj))
  | .fin n =>
    let finT := mkApp (mkConst ``Fin) (toExpr n)
    let ofL ← withLocalDeclD `xs listR fun xs => do
      withLocalDeclD `i finT fun i => do
        let iN ← mkAppM ``Fin.val #[i]
        mkLambdaFVars #[xs, i] (← mkAppM ``List.getD #[xs, iN, (← mkNumeral (mkConst ``Real) 0)])
    return (ofL, mkApp ((← mkC ``RealFP.Roots.coordsFin_to)) (toExpr n), mkApp ((← mkC ``RealFP.Roots.coordsFin_inj)) (toExpr n))

/-- Prove `lhs = rhs` (closed real numerals) by `norm_num`. -/
def proveNumEq (lhs rhs : Expr) : TacticM Expr := do
  let m ← mkFreshExprMVar (← mkEq lhs rhs)
  let saved ← getGoals
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| first | rfl | norm_num))
  unless (← getGoals).isEmpty do throwError "realfp: could not prove {lhs} = {rhs}"
  setGoals saved
  instantiateMVars m

/-- Prove `lhs = rhs` where `rhs` is a reified denotation (as `interval` does). -/
def proveDenoteEq (lhs rhs : Expr) : TacticM Expr := do
  let m ← mkFreshExprMVar (← mkEq lhs rhs)
  let saved ← getGoals
  setGoals [m.mvarId!]
  denoteSimp
  unless (← getGoals).isEmpty do
    throwError "realfp: could not match {lhs} with its reified form"
  setGoals saved
  instantiateMVars m

structure St where
  lo : Array (Option ℚ)
  hi : Array (Option ℚ)
  eqs : Array IExpr := #[]

def ratCastR (q : ℚ) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``RatCast [Level.zero]) (mkConst ``Real))
  return mkApp3 (mkConst ``Rat.cast [Level.zero]) (mkConst ``Real) inst (toExpr q)

def coordIdx (coords : Array Expr) (x : Expr) : MetaM (Option Nat) := do
  for i in [0:coords.size] do
    if ← withReducible (isDefEq x coords[i]!) then return some i
  return none

def setBound (lo : Bool) (i : Nat) (q : ℚ) : StateT St TacticM Unit := do
  let s ← get
  let arr := if lo then s.lo else s.hi
  if (arr[i]!).isSome then
    throwError "realfp: coordinate {i} has two {if lo then "lower" else "upper"} bounds; give \
      exactly one closed box per coordinate"
  if lo then set { s with lo := s.lo.set! i (some q) } else set { s with hi := s.hi.set! i (some q) }

/-- Canonical form `Q` of the constraint `a` and a proof of `a ↔ Q`. -/
partial def canon (coords : Array Expr) (xsE : Expr) (a : Expr) :
    StateT St TacticM (Expr × Expr) := do
  let a ← instantiateMVars a
  match a.getAppFnArgs with
  | (``And, #[A, B]) =>
    let (qA, hA) ← canon coords xsE A
    let (qB, hB) ← canon coords xsE B
    return (mkAnd qA qB, ← mkAppM ``and_congr #[hA, hB])
  | (``Membership.mem, #[_, _, _, s, x]) =>
    let s ← whnfR s
    let some i ← coordIdx coords x | throwError "realfp: {x} is not a coordinate of the point"
    match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, l, u]) =>
      let some ql ← ratOf? l | throwError "realfp: box endpoint {l} is not a numeral"
      let some qu ← ratOf? u | throwError "realfp: box endpoint {u} is not a numeral"
      setBound true i ql; setBound false i qu
      let c := coords[i]!
      let ha ← proveNumEq l (← ratCastR ql)
      let hb ← proveNumEq u (← ratCastR qu)
      let hc ← mkEqRefl x
      let q := mkAnd (← mkAppM ``LE.le #[← ratCastR ql, c]) (← mkAppM ``LE.le #[c, ← ratCastR qu])
      return (q, mkAppN ((← mkC ``RealFP.RootTactic.icc_iff))
        #[x, c, l, u, toExpr ql, toExpr qu, hc, ha, hb])
    | _ => throwError "realfp: only closed boxes `Set.Icc a b` are supported, got {s}"
  | (``GE.ge, #[_, _, l, r]) => canon coords xsE (← mkAppM ``LE.le #[r, l])
  | (``LE.le, #[ty, _, l, r]) =>
    unless (← whnfR ty).isConstOf ``Real do throwError "realfp: constraint {a} is not over ℝ"
    if let some i ← coordIdx coords r then
      if let some ql ← ratOf? l then
        setBound true i ql
        let c := coords[i]!
        let ha ← proveNumEq l (← ratCastR ql)
        return (← mkAppM ``LE.le #[← ratCastR ql, c], mkAppN ((← mkC ``RealFP.RootTactic.lo_iff))
          #[r, c, l, toExpr ql, ← mkEqRefl r, ha])
    if let some i ← coordIdx coords l then
      if let some qu ← ratOf? r then
        setBound false i qu
        let c := coords[i]!
        let hb ← proveNumEq r (← ratCastR qu)
        return (← mkAppM ``LE.le #[c, ← ratCastR qu], mkAppN ((← mkC ``RealFP.RootTactic.hi_iff))
          #[l, c, r, toExpr qu, ← mkEqRefl l, hb])
    throwError "realfp: unsupported constraint {a}; expected a numeral bound on one coordinate"
  | (``Eq, #[ty, l, r]) =>
    unless (← whnfR ty).isConstOf ``Real do throwError "realfp: equation {a} is not over ℝ"
    let d ← mkAppM ``HSub.hSub #[l, r]
    let e ← reify coords d
    modify fun s => { s with eqs := s.eqs.push e }
    let D := mkApp2 ((← mkC ``IExpr.denote)) xsE (iexprToExpr e)
    let h ← proveDenoteEq d D
    return (← mkEq D ((← mkNumeral (mkConst ``Real) 0)), mkApp4 ((← mkC ``RealFP.RootTactic.eq_iff_sub)) l r D h)
  | (``LT.lt, _) => throwError "realfp: strict bound {a}; use closed bounds (`≤` or `Set.Icc`)"
  | _ => throwError "realfp: unsupported constraint {a}"

/-- Parsed root goal: point kind, predicate, box, equations and the bridge `∀ p, P p ↔ Canon p`. -/
structure RootGoal where
  kind : PtKind
  T : Expr
  bs : List (ℚ × ℚ)
  es : List IExpr
  /-- `fun p => coordinate list`. -/
  toL : Expr
  /-- `∀ p, P p ↔ InBoxes (toL p) bs ∧ AllZero es (toL p)`. -/
  hiff : Expr

def analyse (T pred : Expr) : TacticM RootGoal := do
  let some kind ← ptKind T | throwError "realfp: the point must have type ℝ, ℝ × ℝ, ℝ × ℝ × ℝ or \
    Fin n → ℝ, got {T}"
  withLocalDeclD `p T fun p => do
    let body ← whnfR (← instantiateMVars (mkApp pred p)) -- beta
    let body := body.headBeta
    let coords ← coordsOf kind p
    let n := coords.size
    let xsE ← mkListLit (mkConst ``Real) coords.toList
    let st0 : St := ⟨Array.replicate n none, Array.replicate n none, #[]⟩
    let ((Q, hPQ), st) ← (canon coords xsE body).run st0
    let mut bs : List (ℚ × ℚ) := []
    for i in [0:n] do
      match st.lo[i]!, st.hi[i]! with
      | some l, some h =>
        unless l ≤ h do throwError "realfp: empty box for coordinate {i}: [{l}, {h}]"
        bs := bs ++ [(l, h)]
      | _, _ => throwError "realfp: coordinate {coords[i]!} needs a numeral lower and upper bound"
    unless st.eqs.size == n do
      throwError "realfp: {st.eqs.size} equation(s) for {n} unknown(s); root tactics need a \
        square system"
    let es := st.eqs.toList
    let bsE := toExpr bs
    let esE ← mkListLit (mkConst ``IExpr) (es.map iexprToExpr)
    let canonE := mkAnd (mkApp2 ((← mkC ``RealFP.InBoxes)) xsE bsE)
      (mkApp2 ((← mkC ``RealFP.Roots.AllZero)) esE xsE)
    -- `Q ↔ Canon` by unfolding `Canon` into the same atoms and propositional reasoning
    let hQC ← mkFreshExprMVar (mkApp2 (mkConst ``Iff) Q canonE)
    let saved ← getGoals
    setGoals [hQC.mvarId!]
    evalTactic (← `(tactic|
      (simp only [RealFP.RootTactic.inBoxes_cons', RealFP.RootTactic.inBoxes_nil',
        RealFP.RootTactic.allZero_cons, RealFP.RootTactic.allZero_nil, and_true]
       try tauto)))
    unless (← getGoals).isEmpty do throwError "realfp: internal (canonical form)"
    setGoals saved
    let h ← mkAppM ``Iff.trans #[hPQ, ← instantiateMVars hQC]
    let hiff ← mkLambdaFVars #[p] h
    let toL ← mkLambdaFVars #[p] xsE
    return { kind, T, bs, es, toL, hiff }

/-- A proof of `check = true` by `decide +kernel` (or `native_decide`). -/
def proveTrue (check : Expr) : TacticM Expr := do
  let m ← mkFreshExprMVar (← mkEq check (mkConst ``Bool.true))
  let saved ← getGoals
  setGoals [m.mvarId!]
  closeCheck
  setGoals saved
  instantiateMVars m

def kcertE (c : KCert) : Expr :=
  mkAppN (mkConst ``RealFP.Roots.KCert.mk) #[toExpr c.m, toExpr c.Y, toExpr c.Z, toExpr c.q, toExpr c.B,
    toExpr c.J]

def esList (es : List IExpr) : MetaM Expr := mkListLit (mkConst ``IExpr) (es.map iexprToExpr)

/-- One variable: derivative-sign certificate for `∃!`. -/
def derivCert (cfg : Cfg) (e : IExpr) (a b : ℚ) : Option (Bool × DCert) := Id.run do
  let env := boxes [(a, b)]
  for inc in [true, false] do
    let (g, upper) := if inc then (gGt (KI.ofRat 0).hi, false) else (gLt (KI.ofRat 0).lo, true)
    let (c?, _) := (searchD cfg.deriv (2 * cfg.maxBoxes) (e.deriv 0) g upper cfg.order true
      cfg.depth env).run 0
    if let some c := c? then
      if derivSign e a b inc c then return some (inc, c)
  return none

/-- One variable: sign change on `[a, b]` or on a sub-interval of a grid. -/
def ivtSub (e : IExpr) (a b : ℚ) (grid : Nat := 512) : Option (ℚ × ℚ) := Id.run do
  if ivtCheck e a b then return some (a, b)
  let af := qToF a
  let bf := qToF b
  let pts : List ℚ := (List.range (grid + 1)).filterMap fun k =>
    if k == 0 then some a else if k == grid then some b
    else ratOfF (af + (bf - af) * Float.ofNat k / Float.ofNat grid)
  for (p, q) in List.zip pts (pts.drop 1) do
    if a ≤ p && p ≤ q && q ≤ b && ivtCheck e p q then return some (p, q)
  return none

/-- One variable at precision 128: derivative-sign certificate for `∃!`. -/
def derivCertQ (cfg : Cfg) (e : IExpr) (a b : ℚ) : Option (Bool × Interval128.Dy.DCert) := Id.run do
  let env := Interval128.Dy.boxes [(a, b)]
  for inc in [true, false] do
    let (g, upper) := if inc then (Interval128.Dy.gGt 0, false) else (Interval128.Dy.gLt 0, true)
    let (c?, _) := (Interval128.Dy.searchDQ cfg.deriv (2 * cfg.maxBoxes) (e.deriv 0) g upper
      cfg.order true cfg.depth env).run 0
    if let some c := c? then
      if RealFP.I128Q.derivSignQ e a b inc c then return some (inc, c)
  return none

/-- One variable at precision 128: sign change on `[a, b]` or on a cell of a rational grid,
refined by bisection of the cell containing the sign change (so the cell can be much narrower
than binary64 resolution). -/
def ivtSubQ (e : IExpr) (a b : ℚ) (grid : Nat := 512) : Option (ℚ × ℚ) := Id.run do
  if RealFP.I128Q.ivtCheckQ e a b then return some (a, b)
  let pts : List ℚ := (List.range (grid + 1)).map fun k => a + (b - a) * k / grid
  for (p, q) in List.zip pts (pts.drop 1) do
    if RealFP.I128Q.ivtCheckQ e p q then return some (p, q)
  return none

def kcertQE (c : RealFP.I128Q.KCertQ) : Expr :=
  mkAppN (mkConst ``RealFP.I128Q.KCertQ.mk) #[toExpr c.m, toExpr c.Y, toExpr c.Z, toExpr c.q]

/-- Krawczyk at precision 128 (`n` variables, or one variable as a fallback). -/
def krawRoots128 (unique : Bool) (rg : RootGoal) (ofL hto hinj : Expr) :
    TacticM (Except String Expr) := do
  let esE ← esList rg.es
  let bsE := toExpr rg.bs
  if unique then
    match krawWholeQ rg.es rg.bs with
    | .ok c =>
      let h ← proveTrue (mkApp3 (← mkC ``RealFP.I128Q.krawCheckQ) esE bsE (kcertQE c))
      return .ok (mkAppN (← mkC ``RealFP.I128Q.kraw_existsUniqueQ)
        #[rg.T, esE, bsE, kcertQE c, rg.toL, ofL, hto, hinj, h])
    | .error s => return .error s!"Krawczyk (128-bit) on the whole box {fmtBox rg.bs}: {s}"
  else
    let attempt : Except String (List (ℚ × ℚ) × RealFP.I128Q.KCertQ) :=
      match krawWholeQ rg.es rg.bs with
      | .ok c => .ok (rg.bs, c)
      | .error s1 => match krawSubQ rg.es rg.bs with
        | .ok r => .ok r
        | .error s2 => .error s!"{s1}; {s2}"
    match attempt with
    | .ok (bs', c) =>
      let chk := mkApp2 (mkConst ``and) (mkApp2 (← mkC ``RealFP.Roots.subBoxes) (toExpr bs') bsE)
        (mkApp3 (← mkC ``RealFP.I128Q.krawCheckQ) esE (toExpr bs') (kcertQE c))
      let h ← proveTrue chk
      return .ok (mkAppN (← mkC ``RealFP.I128Q.kraw_exists_inQ)
        #[rg.T, esE, bsE, toExpr bs', kcertQE c, rg.toL, ofL, hto, h])
    | .error s => return .error s!"Krawczyk (128-bit): {s}"

/-- `∃` / `∃!` at precision 128. -/
def proveRoots128 (cfg : Cfg) (unique : Bool) (rg : RootGoal) (ofL hto hinj : Expr) :
    TacticM Expr := do
  let tac := if unique then "root_unique" else "root_exists"
  unless rg.bs.length == 1 do
    match ← krawRoots128 unique rg ofL hto hinj with
    | .ok pf => return pf
    | .error s => throwError "{tac} (precision := 128): no certificate for the system on \
        {fmtBox rg.bs}:\n• {s}"
  let e := rg.es.head!
  let (a, b) := rg.bs.head!
  let mut err := ""
  if unique then
    if RealFP.I128Q.ivtCheckQ e a b then
      if let some (inc, c) := derivCertQ cfg e a b then
        let chk := mkApp2 (mkConst ``and) (mkApp3 (← mkC ``RealFP.I128Q.ivtCheckQ) (iexprToExpr e)
          (toExpr a) (toExpr b)) (mkAppN (← mkC ``RealFP.I128Q.derivSignQ) #[iexprToExpr e, toExpr a,
            toExpr b, toExpr inc, dcertQToExpr c])
        let h ← proveTrue chk
        return mkAppN (← mkC ``RealFP.I128Q.unique_oneQ) #[iexprToExpr e, toExpr a, toExpr b,
          toExpr inc, dcertQToExpr c, h]
      err := s!"f' has no certified strict sign on the box (depth {cfg.depth}, order {cfg.order})"
    else err := "f has no certified sign change between the endpoints"
  else
    if let some (a', b') := ivtSubQ e a b then
      let chk := mkApp2 (mkConst ``and) (← mkDecide (← mkAppM ``And
        #[← mkAppM ``LE.le #[toExpr a, toExpr a'], ← mkAppM ``LE.le #[toExpr b', toExpr b]]))
        (mkApp3 (← mkC ``RealFP.I128Q.ivtCheckQ) (iexprToExpr e) (toExpr a') (toExpr b'))
      let h ← proveTrue chk
      return mkAppN (← mkC ``RealFP.I128Q.ivt_exists_inQ) #[iexprToExpr e, toExpr a, toExpr b,
        toExpr a', toExpr b', h]
    err := "no sign change of f found on a 512-point grid"
  match ← krawRoots128 unique rg ofL hto hinj with
  | .ok pf => return pf
  | .error s => throwError "{tac} (precision := 128): {err}; {s}"

/-- Prove the root goal. `unique`: `∃!`, else `∃`. -/
def proveRoots (cfg : Cfg) (unique : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let t ← whnfR (← instantiateMVars (← goal.getType))
  let tac := if unique then "root_unique" else "root_exists"
  let (T, pred) ← match t.getAppFnArgs with
    | (``ExistsUnique, #[T, pred]) =>
      unless unique do throwError "{tac}: goal is `∃!`, use `root_unique`"
      pure (T, pred)
    | (``Exists, #[T, pred]) =>
      if unique then throwError "{tac}: goal is `∃`, use `root_exists`"
      pure (T, pred)
    | _ => throwError "{tac}: expected `∃ p, …` or `∃! p, …`, got {t}"
  let rg ← analyse T pred
  let n := rg.bs.length
  let (ofL, hto, hinj) ← kindLemmas rg.kind
  let esE ← esList rg.es
  let bsE := toExpr rg.bs
  let mut errs : Array String := #[]
  let mut core? : Option Expr := none
  if cfg.precision == 128 then
    core? := some (← proveRoots128 cfg unique rg ofL hto hinj)
  -- one variable
  else if n == 1 then
    let e := rg.es.head!
    let (a, b) := rg.bs.head!
    if unique then
      if ivtCheck e a b then
        match derivCert cfg e a b with
        | some (inc, c) =>
          let chk := mkApp2 (mkConst ``and) (mkApp3 ((← mkC ``RealFP.Roots.ivtCheck)) (iexprToExpr e) (toExpr a)
            (toExpr b)) (mkAppN ((← mkC ``RealFP.Roots.derivSign)) #[iexprToExpr e, toExpr a, toExpr b,
              toExpr inc, dcertToExpr c])
          let h ← proveTrue chk
          core? := some (mkAppN ((← mkC ``RealFP.Roots.unique_one)) #[iexprToExpr e, toExpr a, toExpr b,
            toExpr inc, dcertToExpr c, h])
        | none => errs := errs.push s!"f' has no certified strict sign on the box (depth \
            {cfg.depth}, order {cfg.order}), so monotonicity cannot give uniqueness"
      else errs := errs.push "f has no certified sign change between the endpoints"
    else
      match ivtSub e a b with
      | some (a', b') =>
        let chk := mkApp2 (mkConst ``and) (mkApp2 ((← mkC ``RealFP.Roots.subBoxes)) (toExpr [(a', b')])
          (toExpr [(a, b)])) (mkApp3 ((← mkC ``RealFP.Roots.ivtCheck)) (iexprToExpr e) (toExpr a') (toExpr b'))
        let h ← proveTrue chk
        core? := some (mkAppN ((← mkC ``RealFP.Roots.ivt_exists_in)) #[iexprToExpr e, toExpr a, toExpr b,
          toExpr a', toExpr b', h])
      | none => errs := errs.push "no sign change of f found on a 512-point grid (a root of \
          even multiplicity, or no root)"
  -- Krawczyk
  if core?.isNone then
    if unique then
      match krawWhole rg.es rg.bs with
      | .ok c =>
        let h ← proveTrue (mkApp3 ((← mkC ``RealFP.Roots.krawCheck)) esE bsE (kcertE c))
        core? := some (mkAppN ((← mkC ``RealFP.Roots.kraw_existsUnique))
          #[rg.T, esE, bsE, kcertE c, rg.toL, ofL, hto, hinj, h])
      | .error s => errs := errs.push s!"Krawczyk on the whole box {fmtBox rg.bs}: {s}"
    else
      let attempt : Except String (List (ℚ × ℚ) × KCert) :=
        match krawWhole rg.es rg.bs with
        | .ok c => .ok (rg.bs, c)
        | .error s1 => match krawSub rg.es rg.bs with
          | .ok r => .ok r
          | .error s2 => .error s!"{s1}; {s2}"
      match attempt with
      | .ok (bs', c) =>
        let chk := mkApp2 (mkConst ``and) (mkApp2 ((← mkC ``RealFP.Roots.subBoxes)) (toExpr bs') bsE)
          (mkApp3 ((← mkC ``RealFP.Roots.krawCheck)) esE (toExpr bs') (kcertE c))
        let h ← proveTrue chk
        core? := some (mkAppN ((← mkC ``RealFP.Roots.kraw_exists_in))
          #[rg.T, esE, bsE, toExpr bs', kcertE c, rg.toL, ofL, hto, h])
      | .error s => errs := errs.push s!"Krawczyk: {s}"
  let some core := core? | do
    let hint := match newton rg.es n (midQ rg.bs) with
      | some x => if inBoxQ rg.bs x then
          s!" An approximate root is ({", ".intercalate (x.map fmtQ)}); a smaller box around it \
            usually works for `∃!`."
        else ""
      | none => ""
    throwError "{tac}: no certificate for the system on {fmtBox rg.bs}:\n• {"\n• ".intercalate errs.toList}\n{hint}"
  let pf ← if unique then mkAppM ``Iff.mpr #[← mkAppM ``existsUnique_congr #[rg.hiff], core]
    else mkAppM ``Iff.mpr #[← mkAppM ``exists_congr #[rg.hiff], core]
  goal.assign pf
  replaceMainGoal []

/-! ### Syntax -/

def parseCfg (opts : Array Syntax) (tac : String) : TacticM (Cfg × Name) := do
  let mut cfg : Cfg := {}
  let mut trust : Name := `inherit
  for o in opts do
    let k := o[1].getId
    let v := o[3]
    let n := v.isNatLit?
    if k == `depth then cfg := { cfg with depth := n.getD cfg.depth }
    else if k == `maxBoxes then cfg := { cfg with maxBoxes := n.getD cfg.maxBoxes }
    else if k == `chunk then cfg := { cfg with chunk := n.getD cfg.chunk }
    else if k == `order then cfg := { cfg with order := n.getD cfg.order }
    else if k == `deriv then cfg := { cfg with deriv := v.getId != `false }
    else if k == `trust then trust := v.getId
    else if k == `precision then
      match n with
      | some 64 => cfg := { cfg with precision := 64 }
      | some 128 => cfg := { cfg with precision := 128 }
      | _ => throwErrorAt o "{tac}: (precision := _) must be 64 or 128"
    else throwErrorAt o "{tac}: unknown option {k} (expected depth, maxBoxes, chunk, deriv, \
      order, trust, precision)"
  return (cfg, trust)

/-- `root_exists`: prove `∃ p, box ∧ equations` (sign change in one variable, Krawczyk in
several). Options as for `interval`, including `(trust := native)`. -/
syntax (name := rootExistsTac) "root_exists" (ppSpace intervalOpt)* : tactic
/-- `root_unique`: prove `∃! p, box ∧ equations` (sign change + monotonicity in one variable,
Krawczyk contraction in several). -/
syntax (name := rootUniqueTac) "root_unique" (ppSpace intervalOpt)* : tactic

@[tactic rootExistsTac] def evalRootExists : Tactic := fun stx => do
  let (cfg, trust) ← parseCfg stx[1].getArgs "root_exists"
  requireNative
  withTrust trust (withRegistered (proveRoots cfg false))

@[tactic rootUniqueTac] def evalRootUnique : Tactic := fun stx => do
  let (cfg, trust) ← parseCfg stx[1].getArgs "root_unique"
  requireNative
  withTrust trust (withRegistered (proveRoots cfg true))

end RealFP.RootTactic
