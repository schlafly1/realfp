/-
Taylor quadrature with shared subexpressions (kernel CSE).

The kernel evaluates `IExpr` trees without sharing, so `sin x`, `cos x`, … occurring many times in
the derivatives `d_0 … d_K` are recomputed each time (and `KI.sin` is costly). Here the
derivatives are given as `roots` over a list of `lets`: `var 0` is `x`, `var (k+1)` is the value of
`lets[k]` (which may only use `var 0 … var k`). `quadKS` evaluates every let once per environment
(point `m` and box `[lo, hi]`) and checks that expanding `roots` gives exactly `derivs e K`; then
it equals `quadK` (`RealFP.KQS.quadKS_eq`), so `quadBoundS` is sound
(`RealFP.KQS.integral_bounds_of_quadBoundS`).
-/
import Interval64.Kernel.Quad

namespace Interval64.KF

deriving instance DecidableEq for IExpr

/-- Substitute `σ i` for `var i`. -/
def IExpr.subst (σ : Nat → IExpr) : IExpr → IExpr
  | .var i => σ i
  | .rat q => .rat q
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .sub a b => .sub (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .div a b => .div (a.subst σ) (b.subst σ)
  | .neg a => .neg (a.subst σ)
  | .inv a => .inv (a.subst σ)
  | .sqrt a => .sqrt (a.subst σ)
  | .abs a => .abs (a.subst σ)
  | .pow a n => .pow (a.subst σ) n
  | .exp a => .exp (a.subst σ)
  | .log a => .log (a.subst σ)
  | .sin a => .sin (a.subst σ)
  | .cos a => .cos (a.subst σ)
  | .pi => .pi
  | .atan a => .atan (a.subst σ)
  | .atan2 a b => .atan2 (a.subst σ) (b.subst σ)
  | .sinh a => .sinh (a.subst σ)
  | .cosh a => .cosh (a.subst σ)
  | .tanh a => .tanh (a.subst σ)
  | .log2 a => .log2 (a.subst σ)
  | .log10 a => .log10 (a.subst σ)
  | .tan a => .tan (a.subst σ)
  | .asin a => .asin (a.subst σ)
  | .acos a => .acos (a.subst σ)

/-- All variables `< n`. -/
def IExpr.varsLt (n : Nat) : IExpr → Bool
  | .var i => Nat.blt i n
  | .rat _ => true
  | .pi => true
  | .add a b | .sub a b | .mul a b | .div a b | .atan2 a b => a.varsLt n && b.varsLt n
  | .neg a | .inv a | .sqrt a | .abs a | .pow a _ | .exp a | .log a | .sin a | .cos a | .atan a
  | .sinh a | .cosh a | .tanh a | .log2 a | .log10 a | .tan a | .asin a | .acos a => a.varsLt n

namespace KQ

/-- `env` extended by the values of the lets. -/
def evalLets (env : List KI) (lets : List IExpr) : List KI :=
  lets.foldl (fun acc d => acc ++ [evalK acc d]) env

/-- Expansions: `[var 0, lets[0] expanded, …]`. -/
def expLets (lets : List IExpr) : List IExpr :=
  lets.foldl (fun acc d => acc ++ [d.subst fun i => acc.getD i (.var 0)]) [.var 0]

/-- Each let only refers to earlier entries. -/
def letsOK : Nat → List IExpr → Bool
  | _, [] => true
  | n, d :: ds => d.varsLt n && letsOK (n + 1) ds

def taylorKS (lo m hi : Nat) (envM : List KI) : Nat → List IExpr → KI
  | _, [] => zeroK
  | _, [_] => zeroK
  | j, d :: ds => KI.add (KI.mul (evalK envM d) (momK lo m hi j)) (taylorKS lo m hi envM (j + 1) ds)

def cellKS (lets roots : List IExpr) (K : Nat) (ds : List IExpr) (c : Nat × Nat × Nat) : KI :=
  KI.add (taylorKS c.1 c.2.1 c.2.2 (evalLets [pt c.2.1] lets) 0 roots)
    (KI.mul (evalK (evalLets [⟨c.1, c.2.2⟩] lets) (roots.getLastD (ds.getLastD (.var 0))))
      (momK c.1 c.2.1 c.2.2 K))

def sumCellsS (lets roots : List IExpr) (K : Nat) (ds : List IExpr) : List (Nat × Nat × Nat) → KI
  | [] => zeroK
  | c :: cs => KI.add (cellKS lets roots K ds c) (sumCellsS lets roots K ds cs)

/-- Structural check: lets well scoped, roots expand to `derivs e K`. -/
def shareOK (e : IExpr) (K : Nat) (lets roots : List IExpr) : Bool :=
  letsOK 1 lets && roots.all (IExpr.varsLt (lets.length + 1)) &&
    decide (roots.map (IExpr.subst fun i => (expLets lets).getD i (.var 0)) = derivs e K)

def quadKS (e : IExpr) (K : Nat) (a b : Nat) (cs : List (Nat × Nat × Nat)) (lets roots : List IExpr) :
    Option KI :=
  let ds := derivs e K
  if shareOK e K lets roots && Nat.beq (K % 2) 0 && Nat.blt 0 K && chainOK a b cs && cs.all (cellOK ds)
  then some (sumCellsS lets roots K ds cs)
  else none

def quadBoundS (e : IExpr) (K a b : Nat) (cs : List (Nat × Nat × Nat)) (lets roots : List IExpr)
    (qa qb ql qh : Rat) : Bool :=
  decide (ratOf a = some qa) && decide (ratOf b = some qb) &&
  match quadKS e K a b cs lets roots with
  | some R =>
    match ratOf R.lo, ratOf R.hi with
    | some l, some h => decide (ql ≤ l) && decide (h ≤ qh)
    | _, _ => false
  | none => false

/-! ### Witnessed let values

The kernel does not reliably share the (lazily reduced) let values, so `quadKW` takes the let
values of every cell as a witness `ws` (point and box environments) and only checks each let
against its witness: every kernel operation then runs on literal inputs. Under `cellsW` it
computes exactly `quadKS` (`RealFP.KQS.quadKW_some`). -/

/-- Boolean equality of kernel intervals. -/
def keq (a b : KI) : Bool := Nat.beq a.lo b.lo && Nat.beq a.hi b.hi

/-- The witnessed values `vs` are the let values over `acc`. -/
def letsW (acc : List KI) : List IExpr → List KI → Bool
  | [], [] => true
  | d :: ds, v :: vs => keq (evalK acc d) v && letsW (acc ++ [v]) ds vs
  | _, _ => false

/-- `cellKS` with the let values given. -/
def cellKW (roots : List IExpr) (K : Nat) (ds : List IExpr) (c : Nat × Nat × Nat)
    (vm vb : List KI) : KI :=
  KI.add (taylorKS c.1 c.2.1 c.2.2 (pt c.2.1 :: vm) 0 roots)
    (KI.mul (evalK (⟨c.1, c.2.2⟩ :: vb) (roots.getLastD (ds.getLastD (.var 0))))
      (momK c.1 c.2.1 c.2.2 K))

/-- Every cell's witnesses are correct. -/
def cellsW (lets : List IExpr) : List (Nat × Nat × Nat) → List (List KI × List KI) → Bool
  | [], [] => true
  | c :: cs, w :: ws => letsW [pt c.2.1] lets w.1 && letsW [⟨c.1, c.2.2⟩] lets w.2 && cellsW lets cs ws
  | _, _ => false

def sumCellsW (roots : List IExpr) (K : Nat) (ds : List IExpr) :
    List (Nat × Nat × Nat) → List (List KI × List KI) → KI
  | c :: cs, w :: ws => KI.add (cellKW roots K ds c w.1 w.2) (sumCellsW roots K ds cs ws)
  | _, _ => zeroK

def quadKW (e : IExpr) (K : Nat) (a b : Nat) (cs : List (Nat × Nat × Nat)) (lets roots : List IExpr)
    (ws : List (List KI × List KI)) : Option KI :=
  let ds := derivs e K
  if shareOK e K lets roots && Nat.beq (K % 2) 0 && Nat.blt 0 K && chainOK a b cs && cs.all (cellOK ds)
    && cellsW lets cs ws
  then some (sumCellsW roots K ds cs ws)
  else none

def quadBoundW (e : IExpr) (K a b : Nat) (cs : List (Nat × Nat × Nat)) (lets roots : List IExpr)
    (ws : List (List KI × List KI)) (qa qb ql qh : Rat) : Bool :=
  decide (ratOf a = some qa) && decide (ratOf b = some qb) &&
  match quadKW e K a b cs lets roots ws with
  | some R =>
    match ratOf R.lo, ratOf R.hi with
    | some l, some h => decide (ql ≤ l) && decide (h ≤ qh)
    | _, _ => false
  | none => false

/-! ### Untrusted: hash-consing into lets -/

/-- One level: rebuild `t` with already-shared children. -/
partial def shareGo (t : IExpr) : StateM (Array IExpr) IExpr := do
  let leaf : Bool := match t with | .var _ | .rat _ | .pi => true | _ => false
  if leaf then return t
  let t' ← match t with
    | .add a b => pure <| .add (← shareGo a) (← shareGo b)
    | .sub a b => pure <| .sub (← shareGo a) (← shareGo b)
    | .mul a b => pure <| .mul (← shareGo a) (← shareGo b)
    | .div a b => pure <| .div (← shareGo a) (← shareGo b)
    | .atan2 a b => pure <| .atan2 (← shareGo a) (← shareGo b)
    | .neg a => pure <| .neg (← shareGo a)
    | .inv a => pure <| .inv (← shareGo a)
    | .sqrt a => pure <| .sqrt (← shareGo a)
    | .abs a => pure <| .abs (← shareGo a)
    | .pow a n => pure <| .pow (← shareGo a) n
    | .exp a => pure <| .exp (← shareGo a)
    | .log a => pure <| .log (← shareGo a)
    | .sin a => pure <| .sin (← shareGo a)
    | .cos a => pure <| .cos (← shareGo a)
    | .atan a => pure <| .atan (← shareGo a)
    | .sinh a => pure <| .sinh (← shareGo a)
    | .cosh a => pure <| .cosh (← shareGo a)
    | .tanh a => pure <| .tanh (← shareGo a)
    | .log2 a => pure <| .log2 (← shareGo a)
    | .log10 a => pure <| .log10 (← shareGo a)
    | .tan a => pure <| .tan (← shareGo a)
    | .asin a => pure <| .asin (← shareGo a)
    | .acos a => pure <| .acos (← shareGo a)
    | t => pure t
  let lets ← get
  match lets.findIdx? (· == t') with
  | some k => return .var (k + 1)
  | none => set (lets.push t'); return .var (lets.size + 1)

/-- `(lets, roots)` for `derivs e K`. -/
def shareDerivs (e : IExpr) (K : Nat) : List IExpr × List IExpr :=
  let (roots, lets) := ((derivs e K).mapM shareGo).run #[]
  (lets.toList, roots)

end KQ
end Interval64.KF
