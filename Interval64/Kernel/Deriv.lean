/-
Derivatives for the reflective checker (Mathlib-free part).

* `IExpr.diff e i` — symbolic partial derivative of `e` in variable `i` (no simplification, so
  its interval evaluation is the forward-mode interval derivative of `e`).
* `domOK env e` — on the box `env`, every `/`, `⁻¹` denominator excludes `0`, every `√`, `log`
  argument is `> 0`, and there is no `|·|` (so `e` is differentiable at every point of the box).
* `DCert` / `checkD` — certificates with, besides `leaf` and `split`:
  - `mono i inc dc c`: `∂ᵢe` has a fixed sign on the box (proved by the nested certificate `dc`),
    so the extreme value in variable `i` is attained at an endpoint; continue with `c` on the
    box where variable `i` is that endpoint (a point);
  - `center i m`: mean-value (centred) form in variable `i` at the point `m`, intersected with the
    naive enclosure.
Soundness (Mathlib): `RealFPMathlib/IntervalDeriv.lean`.
-/
import Interval64.Kernel.Reflect

namespace Interval64.KF

/-- Symbolic partial derivative in variable `i`. -/
def IExpr.diff (i : Nat) : IExpr → IExpr
  | .var j => .rat (bif Nat.beq j i then 1 else 0)
  | .rat _ => .rat 0
  | .add a b => .add (a.diff i) (b.diff i)
  | .sub a b => .sub (a.diff i) (b.diff i)
  | .mul a b => .add (.mul (a.diff i) b) (.mul a (b.diff i))
  -- `a / b^m` keeps a single power of `b` in the denominator (`(a' b - m a b') / b^(m+1)`),
  -- so iterated derivatives of `1/x`, `1/(1+x²)`, … do not nest `((b²)²)²`.
  | .div a (.pow b (n + 1)) =>
    .div (.sub (.mul (a.diff i) b) (.mul (.mul (.rat (n + 1 : Nat)) a) (b.diff i))) (.pow b (n + 2))
  | .div a b => .div (.sub (.mul (a.diff i) b) (.mul a (b.diff i))) (.pow b 2)
  | .neg a => .neg (a.diff i)
  | .inv a => .neg (.div (a.diff i) (.pow a 2))
  | .sqrt a => .div (a.diff i) (.mul (.rat 2) (.sqrt a))
  | .abs _ => .rat 0
  | .pow a n => .mul (.mul (.rat n) (.pow a (n - 1))) (a.diff i)
  | .exp a => .mul (.exp a) (a.diff i)
  | .log a => .div (a.diff i) a
  | .sin a => .mul (.cos a) (a.diff i)
  | .cos a => .neg (.mul (.sin a) (a.diff i))
  | .pi => .rat 0
  | .atan a => .div (a.diff i) (.add (.rat 1) (.pow a 2))
  | .atan2 _ _ => .rat 0
  | .sinh a => .mul (.cosh a) (a.diff i)
  | .cosh a => .mul (.sinh a) (a.diff i)
  | .tanh a => .div (a.diff i) (.pow (.cosh a) 2)
  | .log2 a => .div (.div (a.diff i) a) (.log (.rat 2))
  | .log10 a => .div (.div (a.diff i) a) (.log (.rat 10))
  | .tan a => .div (a.diff i) (.pow (.cos a) 2)
  | .asin a => .div (a.diff i) (.sqrt (.sub (.rat 1) (.pow a 2)))
  | .acos a => .neg (.div (a.diff i) (.sqrt (.sub (.rat 1) (.pow a 2))))

/-! ### Light algebraic simplification (exact rational constant folding)

Folding constants exactly in `Rat` avoids spurious rounding (e.g. `36 * (1/36)`), which matters
when a bound is touching. `denote_dsimp` (Mathlib layer) shows the denotation is unchanged. -/

def mkAdd : IExpr → IExpr → IExpr
  | .rat p, .rat q => .rat (p + q)
  | .rat p, b => bif p == 0 then b else .add (.rat p) b
  | a, .rat q => bif q == 0 then a else .add a (.rat q)
  | a, b => .add a b

def mkNeg : IExpr → IExpr
  | .rat p => .rat (-p)
  | .neg a => a
  | a => .neg a

def mkSub : IExpr → IExpr → IExpr
  | .rat p, .rat q => .rat (p - q)
  | .rat p, b => bif p == 0 then mkNeg b else .sub (.rat p) b
  | a, .rat q => bif q == 0 then a else .sub a (.rat q)
  | a, b => .sub a b

/-- `p * b` with `p` a rational. -/
def mkMulC (p : Rat) : IExpr → IExpr
  | .rat q => .rat (p * q)
  | .mul (.rat q) c => bif p * q == 0 then .rat 0 else bif p * q == 1 then c else .mul (.rat (p * q)) c
  | b => bif p == 0 then .rat 0 else bif p == 1 then b else .mul (.rat p) b

def mkMul : IExpr → IExpr → IExpr
  | .rat p, b => mkMulC p b
  | a, .rat q => mkMulC q a
  | a, b => .mul a b

def mkDiv : IExpr → IExpr → IExpr
  | a, .rat q => bif q == 0 then .rat 0 else mkMulC (1 / q) a
  | a, b => .div a b

def mkPow : IExpr → Nat → IExpr
  | .rat p, n => .rat (p ^ n)
  | a, n => bif Nat.beq n 0 then .rat 1 else bif Nat.beq n 1 then a else .pow a n

def IExpr.dsimp : IExpr → IExpr
  | .add a b => mkAdd a.dsimp b.dsimp
  | .sub a b => mkSub a.dsimp b.dsimp
  | .mul a b => mkMul a.dsimp b.dsimp
  | .div a b => mkDiv a.dsimp b.dsimp
  | .neg a => mkNeg a.dsimp
  | .pow a n => mkPow a.dsimp n
  | .inv a => .inv a.dsimp
  | .sqrt a => .sqrt a.dsimp
  | .abs a => .abs a.dsimp
  | .exp a => .exp a.dsimp
  | .log a => .log a.dsimp
  | .sin a => .sin a.dsimp
  | .cos a => .cos a.dsimp
  | .atan a => .atan a.dsimp
  | .sinh a => .sinh a.dsimp
  | .cosh a => .cosh a.dsimp
  | .tanh a => .tanh a.dsimp
  | .log2 a => .log2 a.dsimp
  | .log10 a => .log10 a.dsimp
  | .tan a => .tan a.dsimp
  | .asin a => .asin a.dsimp
  | .acos a => .acos a.dsimp
  | e => e

/-- Simplified partial derivative (used by the checker). -/
def IExpr.deriv (i : Nat) (e : IExpr) : IExpr := (e.diff i).dsimp

/-- The enclosure is non-NaN and strictly positive. -/
def posK (X : KI) : Bool := !isNaN X.lo && !isNaN X.hi && lt 0 X.lo
/-- The enclosure is non-NaN and excludes `0`. -/
def nzK (X : KI) : Bool := !isNaN X.lo && !isNaN X.hi && (lt 0 X.lo || lt X.hi 0)

def domOK (env : List KI) : IExpr → Bool
  | .var _ => true
  | .rat _ => true
  | .add a b => domOK env a && domOK env b
  | .sub a b => domOK env a && domOK env b
  | .mul a b => domOK env a && domOK env b
  | .div a b => domOK env a && domOK env b && nzK (evalK env b)
  | .neg a => domOK env a
  | .inv a => domOK env a && nzK (evalK env a)
  | .sqrt a => domOK env a && posK (evalK env a)
  | .abs _ => false
  | .pow a _ => domOK env a
  | .exp a => domOK env a
  | .log a => domOK env a && posK (evalK env a)
  | .sin a => domOK env a
  | .cos a => domOK env a
  | .pi => true
  | .atan a => domOK env a
  | .atan2 _ _ => false
  | .sinh a => domOK env a
  | .cosh a => domOK env a
  | .tanh a => domOK env a
  | .log2 a => domOK env a && posK (evalK env a)
  | .log10 a => domOK env a && posK (evalK env a)
  | .tan a => domOK env a && nzK (evalK env (.cos a))
  | .asin a => domOK env a && posK (evalK env (.sub (.rat 1) (.pow a 2)))
  | .acos a => domOK env a && posK (evalK env (.sub (.rat 1) (.pow a 2)))

/-- Finite float bit pattern. -/
def finK (p : Nat) : Bool := !isNaN p && !isInf p && Nat.blt p (2 ^ 64)

/-- Intersection of two enclosures. -/
def KI.meet (a b : KI) : KI := ⟨KI.fmax a.lo b.lo, KI.fmin a.hi b.hi⟩

inductive DCert where
  | leaf
  | split (i : Nat) (m : Nat) (l r : DCert)
  /-- `∂ᵢe ≥ 0` (`inc`) or `≤ 0` on the box (certificate `dc`); continue at the endpoint. -/
  | mono (i : Nat) (inc : Bool) (dc c : DCert)
  /-- Centred form in variable `i` at the float `m`. -/
  | center (i : Nat) (m : Nat)
  deriving Repr, Inhabited

/-- Zero bits for derivative-sign goals (`c = 0`). -/
def zeroLo : Nat := (KI.ofRat 0).lo
def zeroHi : Nat := (KI.ofRat 0).hi

/-- Centred-form enclosure of `e` on `env` in variable `i` around the point `m`. -/
def centerK (env : List KI) (e : IExpr) (i m : Nat) : KI :=
  KI.meet (evalK env e)
    (KI.add (evalK (env.set i ⟨m, m⟩) e)
      (KI.mul (evalK env (e.deriv i)) (KI.sub (env.getD i zeroK) ⟨m, m⟩)))

/-- `upper`: the goal predicate is downward closed (`f ≤ c`, `f < c`); otherwise upward closed. -/
def checkD (e : IExpr) (g : KI → Bool) (upper : Bool) : DCert → List KI → Bool
  | .leaf, env => g (evalK env e)
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkD e g upper l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkD e g upper r (env.set i ⟨m, (env.getD i zeroK).hi⟩)
  | .mono i inc dc c, env =>
    Nat.blt i env.length && domOK env e &&
      (bif inc then checkD (e.deriv i) (gGe zeroHi) false dc env
       else checkD (e.deriv i) (gLe zeroLo) true dc env) &&
      finK (bif inc == upper then (env.getD i zeroK).hi else (env.getD i zeroK).lo) &&
      checkD e g upper c
        (env.set i (bif inc == upper then ⟨(env.getD i zeroK).hi, (env.getD i zeroK).hi⟩
          else ⟨(env.getD i zeroK).lo, (env.getD i zeroK).lo⟩))
  | .center i m, env =>
    Nat.blt i env.length && domOK env e && finK m &&
      !isNaN (env.getD i zeroK).lo && !isNaN (env.getD i zeroK).hi &&
      le (env.getD i zeroK).lo m && le m (env.getD i zeroK).hi &&
      g (centerK env e i m)

end Interval64.KF
