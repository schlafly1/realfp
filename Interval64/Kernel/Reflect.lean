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
  | sinh (a : IExpr)
  | cosh (a : IExpr)
  | tanh (a : IExpr)
  /-- `Real.logb 2`. -/
  | log2 (a : IExpr)
  /-- `Real.logb 10`. -/
  | log10 (a : IExpr)
  | tan (a : IExpr)
  /-- Mathlib's `Real.arcsin` (clamped outside `[-1, 1]`). -/
  | asin (a : IExpr)
  /-- Mathlib's `Real.arccos`. -/
  | acos (a : IExpr)
  /-- A registered extension function (see `RealFPMathlib/Registry.lean`): key `k` in the
  extension table (`ExtTbl`), applied to `a`. `d` is the function's derivative as an expression
  in `var 0` (built-in functions only); `domOK` checks it is the registered one. -/
  | ext (k : Nat) (d : IExpr) (a : IExpr)
  deriving Repr, Inhabited

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
  | .ext k d a => .ext k d (a.subst σ)

/-- `e` uses no extension function. -/
def IExpr.extFree : IExpr → Bool
  | .var _ | .rat _ | .pi => true
  | .add a b | .sub a b | .mul a b | .div a b | .atan2 a b => a.extFree && b.extFree
  | .neg a | .inv a | .sqrt a | .abs a | .pow a _ | .exp a | .log a | .sin a | .cos a | .atan a
  | .sinh a | .cosh a | .tanh a | .log2 a | .log10 a | .tan a | .asin a | .acos a => a.extFree
  | .ext .. => false

/-- Substitution for `var 0` (other variables become `0`): the argument of a derivative
template. -/
def IExpr.subst0 (a : IExpr) : Nat → IExpr := fun i => bif Nat.beq i 0 then a else .rat 0

/-! ### Extension functions

An extension function is plugged in by giving its kernel enclosure `evK` (on bit-pattern
intervals `KI`; used by the kernel checks, and natively by the search), a domain test `domK`
(where it is differentiable with derivative `deriv`), and the derivative as an `IExpr` in
`var 0`. The real function and the soundness proofs live in the Mathlib layer
(`RealFP.ExtSem`, `RealFPMathlib/Registry.lean`). A C fast path can be attached to `evK` with
`@[implemented_by]` (trusted only by `native_decide`). -/

structure ExtFn where
  /-- Name shown in messages. -/
  name : String := "ext"
  /-- Enclosure: for a non-NaN box `X`, `evK X` contains `f x` for every `x ∈ X`. -/
  evK : KI → KI
  /-- `domK X = true` ⇒ every `x ∈ X` is in the function's domain of differentiability. -/
  domK : KI → Bool := fun _ => false
  /-- Derivative template in `var 0` (built-in functions only). -/
  deriv : IExpr := .rat 0

instance : Inhabited ExtFn := ⟨{ evK := fun _ => KI.whole }⟩

/-- No function: enclosure `whole`, never differentiable. -/
def ExtFn.none : ExtFn := { evK := fun _ => KI.whole }

/-- The extension table: key ↦ function. The default instance is empty; the tactics supply
the registered functions (`RealFPMathlib/Registry.lean`). -/
class ExtTbl where
  get : Nat → ExtFn

instance (priority := low) ExtTbl.empty : ExtTbl := ⟨fun _ => ExtFn.none⟩

/-- Out-of-range bit patterns are replaced by `whole` (so the result is always well formed). -/
def sanitizeK (Y : KI) : KI :=
  bif Nat.blt Y.lo (2 ^ 64) && Nat.blt Y.hi (2 ^ 64) then Y else KI.whole

/-- Kernel enclosure of extension `k` on `X` (`whole` on NaN input). -/
def extK [ExtTbl] (k : Nat) (X : KI) : KI :=
  bif isNaN X.lo || isNaN X.hi then KI.whole else sanitizeK ((ExtTbl.get k).evK X)

/-- `Interval64` → bit patterns. -/
def ofI (X : Interval64) : KI := ⟨X.lo.toBits.toNat, X.hi.toBits.toNat⟩
/-- Bit patterns → `Interval64`. -/
def toIv (X : KI) : Interval64 := ⟨Float.ofBits (UInt64.ofNat X.lo), Float.ofBits (UInt64.ofNat X.hi)⟩

/-- `Interval64` enclosure of extension `k` (through the kernel enclosure). -/
def extI [ExtTbl] (k : Nat) (X : Interval64) : Interval64 :=
  if X.lo.isNaN || X.hi.isNaN then whole else toIv (sanitizeK ((ExtTbl.get k).evK (ofI X)))

/-- Domain test of extension `k` on `X` (false on NaN input). -/
def extDomK [ExtTbl] (k : Nat) (X : KI) : Bool :=
  !isNaN X.lo && !isNaN X.hi && (ExtTbl.get k).domK X

variable [ExtTbl]

/-! ### `Interval64` semantics -/

def zeroI : Interval64 := ⟨0, 0⟩

/-- `√X` extended to negative members (`Real.sqrt x = 0` for `x < 0`). -/
def sqrtI (X : Interval64) : Interval64 :=
  if decide (X.lo < 0) then hull zeroI (Interval64.sqrt X) else Interval64.sqrt X

/-- `log X` if `X > 0`, else the whole line. -/
def logI (X : Interval64) : Interval64 :=
  if decide (0 < X.lo) then Interval64.log X else whole

/-- `log2` / `log10` if `X > 0`, else the whole line (`Real.logb b x = log x / log b`). -/
def logBI (ten : Bool) (X : Interval64) : Interval64 :=
  if decide (0 < X.lo) then Interval64.logB ten X else whole

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
  | .sinh a => Interval64.sinh (evalI env a)
  | .cosh a => Interval64.cosh (evalI env a)
  | .tanh a => Interval64.tanh (evalI env a)
  | .log2 a => logBI false (evalI env a)
  | .log10 a => logBI true (evalI env a)
  | .tan a => Interval64.tan (evalI env a)
  | .asin a => Interval64.asin (evalI env a)
  | .acos a => Interval64.acos (evalI env a)
  | .ext k _ a => extI k (evalI env a)

/-! ### Kernel semantics -/

def zeroK : KI := ⟨0, 0⟩

def sqrtK (X : KI) : KI := bif lt X.lo 0 then KI.hull zeroK (KI.sqrt X) else KI.sqrt X

def logK (X : KI) : KI := bif lt 0 X.lo then KI.log X else KI.whole

def logBK (ten : Bool) (X : KI) : KI := bif lt 0 X.lo then KI.logB ten X else KI.whole

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
  | .sinh a => KI.sinh (evalK env a)
  | .cosh a => KI.cosh (evalK env a)
  | .tanh a => KI.tanh (evalK env a)
  | .log2 a => logBK false (evalK env a)
  | .log10 a => logBK true (evalK env a)
  | .tan a => KI.tan (evalK env a)
  | .asin a => KI.asin (evalK env a)
  | .acos a => KI.acos (evalK env a)
  | .ext k _ a => extK k (evalK env a)

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
