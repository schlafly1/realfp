/-
Reflective interval checker (Mathlib-free part).

`IExpr` is an arithmetic expression over variables `x₀, x₁, …`. `evalI` evaluates it with
`Interval64` operations (the semantics used in soundness proofs) and `evalK` with the kernel
fast path `KI` (proved equal: `Interval64Proofs/KernelReflect.lean`). `checkK` walks a
bisection certificate: at a leaf it evaluates the expression on the current box and tests a
goal predicate; at a split it checks both halves of one variable's interval. The real
denotation and the soundness theorem are in `RealFPMathlib/IntervalTactic.lean`.
-/
import Interval64.Kernel.Interval
import Interval64.Ops

namespace Interval64.KF

/-- Expressions for the `interval` tactic. `div a b` is evaluated as `a * inv b`. -/
inductive IExpr where
  | var (i : Nat)
  | rat (q : Rat)
  | add (a b : IExpr)
  | sub (a b : IExpr)
  | mul (a b : IExpr)
  | div (a b : IExpr)
  | neg (a : IExpr)
  | inv (a : IExpr)
  | sqrt (a : IExpr)
  | abs (a : IExpr)
  | pow (a : IExpr) (n : Nat)
  | exp (a : IExpr)
  | log (a : IExpr)
  | sin (a : IExpr)
  | cos (a : IExpr)
  | pi
  | atan (a : IExpr)
  /-- `atan2 y x = Complex.arg (x + y i)`. -/
  | atan2 (y x : IExpr)
  deriving Repr, Inhabited

/-! ### `Interval64` semantics -/

def zeroI : Interval64 := ⟨0, 0⟩

/-- `√X` extended to negative members (`Real.sqrt x = 0` for `x < 0`). -/
def sqrtI (X : Interval64) : Interval64 :=
  if decide (X.lo < 0) then hull zeroI (Interval64.sqrt X) else Interval64.sqrt X

/-- `log X` if `X > 0`, else the whole line. -/
def logI (X : Interval64) : Interval64 :=
  if decide (0 < X.lo) then Interval64.log X else whole

/-- `atan2` for the tactic, with `Y / X` as `Y * inv X` (as `IExpr.div`); see `Interval64.atan2`. -/
def atan2I (y x : Interval64) : Interval64 :=
  if anyNan y x then invalid
  else if decide (0 < x.lo) then Interval64.atan (y * inv x)
  else if decide (0 < y.lo) then halfPi - Interval64.atan (x * inv y)
  else if decide (y.hi < 0) then negHalfPi - Interval64.atan (x * inv y)
  else argHull

def evalI (env : List Interval64) : IExpr → Interval64
  | .var i => env.getD i zeroI
  | .rat q => ofRat q
  | .add a b => evalI env a + evalI env b
  | .sub a b => evalI env a - evalI env b
  | .mul a b => evalI env a * evalI env b
  | .div a b => evalI env a * inv (evalI env b)
  | .neg a => -evalI env a
  | .inv a => inv (evalI env a)
  | .sqrt a => sqrtI (evalI env a)
  | .abs a => Interval64.abs (evalI env a)
  | .pow a n => pown (evalI env a) n
  | .exp a => Interval64.exp (evalI env a)
  | .log a => logI (evalI env a)
  | .sin a => Interval64.sin (evalI env a)
  | .cos a => Interval64.cos (evalI env a)
  | .pi => Interval64.pi
  | .atan a => Interval64.atan (evalI env a)
  | .atan2 a b => atan2I (evalI env a) (evalI env b)

/-! ### Kernel semantics -/

def zeroK : KI := ⟨0, 0⟩

def sqrtK (X : KI) : KI := bif lt X.lo 0 then KI.hull zeroK (KI.sqrt X) else KI.sqrt X

def logK (X : KI) : KI := bif lt 0 X.lo then KI.log X else KI.whole

def atan2K (y x : KI) : KI :=
  bif KI.anyNan y x then KI.invalid
  else bif lt 0 x.lo then KI.atan (KI.mul y (KI.inv x))
  else bif lt 0 y.lo then KI.sub KI.halfPi (KI.atan (KI.mul x (KI.inv y)))
  else bif lt y.hi 0 then KI.sub KI.negHalfPi (KI.atan (KI.mul x (KI.inv y)))
  else KI.argHull

def evalK (env : List KI) : IExpr → KI
  | .var i => env.getD i zeroK
  | .rat q => KI.ofRat q
  | .add a b => KI.add (evalK env a) (evalK env b)
  | .sub a b => KI.sub (evalK env a) (evalK env b)
  | .mul a b => KI.mul (evalK env a) (evalK env b)
  | .div a b => KI.mul (evalK env a) (KI.inv (evalK env b))
  | .neg a => KI.neg (evalK env a)
  | .inv a => KI.inv (evalK env a)
  | .sqrt a => sqrtK (evalK env a)
  | .abs a => KI.abs (evalK env a)
  | .pow a n => KI.pown (evalK env a) n
  | .exp a => KI.exp (evalK env a)
  | .log a => logK (evalK env a)
  | .sin a => KI.sin (evalK env a)
  | .cos a => KI.cos (evalK env a)
  | .pi => KI.pi
  | .atan a => KI.atan (evalK env a)
  | .atan2 a b => atan2K (evalK env a) (evalK env b)

/-! ### Goal predicates on the enclosure `F` of the expression -/

/-- `f ≤ c` (`c` = bit pattern of a float `≤` the real bound). -/
def gLe (c : Nat) (F : KI) : Bool := !isNaN F.lo && !isNaN F.hi && !isNaN c && le F.hi c
/-- `f < c`. -/
def gLt (c : Nat) (F : KI) : Bool := !isNaN F.lo && !isNaN F.hi && !isNaN c && lt F.hi c
/-- `c ≤ f` (`c` = bit pattern of a float `≥` the real bound). -/
def gGe (c : Nat) (F : KI) : Bool := !isNaN F.lo && !isNaN F.hi && !isNaN c && le c F.lo
/-- `c < f`. -/
def gGt (c : Nat) (F : KI) : Bool := !isNaN F.lo && !isNaN F.hi && !isNaN c && lt c F.lo

/-! ### Bisection certificates -/

/-- `split i m l r`: split variable `i` at the float with bits `m`. -/
inductive Cert where
  | leaf
  | split (i : Nat) (m : Nat) (l r : Cert)
  deriving Repr, Inhabited

def checkK (e : IExpr) (g : KI → Bool) : Cert → List KI → Bool
  | .leaf, env => g (evalK env e)
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkK e g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkK e g r (env.set i ⟨m, (env.getD i zeroK).hi⟩)

/-- Initial boxes from rational bounds. -/
def boxes : List (Rat × Rat) → List KI
  | [] => []
  | (a, b) :: t => KI.ofRatInterval a b :: boxes t

end Interval64.KF
