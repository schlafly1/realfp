/-
Reflective evaluation of `IExpr` with `Interval128` (double-double) endpoints: the
`(precision := 128)` path of the `interval` / `realfp` tactics.

* `evalD env e` evaluates `e` with the Interval128 operations: `+ - * / ⁻¹ √ |·| ^n` and
  rational constants are double-double (about `2⁻¹⁰⁶` relative), `π` is enclosed by its
  20-digit rational bounds. Every other function (`exp`, `log`, `sin`, …, extension functions)
  is evaluated by the Interval64 kernel evaluator `evalK` on the outward binary64 hull of its
  argument (`lift1` / `lift2`), so its result is only as tight as Interval64.
* `checkD e g cert env` walks a bisection certificate whose split points are rationals.
* Goal predicates compare the exact value of a double-double endpoint with a rational.

Everything is a plain Lean definition: `decide +kernel` evaluates the specifications, compiled
code (search, `native_decide`) runs the C kernels attached by `@[implemented_by]`. Soundness:
`RealFPMathlib/I128Sound.lean`.
-/
import Interval128.Interval
import Interval128.Display
import Interval64.Kernel.Reflect

namespace Interval128.Refl

open Interval64 Interval64.KF


abbrev I := Interval128.Interval128

def zeroD : I := ⟨0, 0, 0, 0⟩
def oneD : I := Interval128.Interval128.ofRat 1

/-- Interval64 hull of `X` as kernel bit patterns (`none` on a NaN endpoint). -/
def hull64 (X : I) : Option KI :=
  let J := Interval128.Interval128.toInterval64 X
  if J.lo.isNaN || J.hi.isNaN then none else some (ofI J)

variable [ExtTbl]

/-- Interval64 enclosure of the unary template `f` (in `var 0`) on `X`, embedded exactly. -/
def lift1 (f : IExpr) (X : I) : I :=
  match hull64 X with
  | some K => Interval128.Interval128.ofInterval64 (toIv (evalK [K] f))
  | none => Interval128.Interval128.whole

/-- Same for a binary template in `var 0`, `var 1`. -/
def lift2 (f : IExpr) (X Y : I) : I :=
  match hull64 X, hull64 Y with
  | some K, some L => Interval128.Interval128.ofInterval64 (toIv (evalK [K, L] f))
  | _, _ => Interval128.Interval128.whole

/-- Division: double-double when the divisor is finite and excludes `0`, else the whole line
(`x / 0 = 0` in `ℝ`, so `whole` is the only safe answer when `0` may be in the divisor). -/
def divD (X Y : I) : I :=
  if Y.isFin && (_root_.Interval128.DD.pos Y.lh Y.ll || _root_.Interval128.DD.neg Y.uh Y.ul) then Interval128.Interval128.div X Y
  else Interval128.Interval128.whole

def invD (X : I) : I := divD oneD X

/-- `√X` (double-double when `X` is finite and nonnegative, else through Interval64). -/
def sqrtD (X : I) : I :=
  if X.isFin && _root_.Interval128.DD.nonneg X.lh X.ll then Interval128.Interval128.sqrt X
  else lift1 (.sqrt (.var 0)) X

/-- `|X|` (exact when `X` has a sign, else through Interval64). -/
def absD (X : I) : I :=
  if X.isFin && _root_.Interval128.DD.nonneg X.lh X.ll then X
  else if X.isFin && _root_.Interval128.DD.nonpos X.uh X.ul then Interval128.Interval128.neg X
  else lift1 (.abs (.var 0)) X

/-- `X ^ n` by repeated multiplication. -/
def mulPow (X : I) : Nat → I
  | 0 => oneD
  | n + 1 => Interval128.Interval128.mul (mulPow X n) X

/-- `X ^ n`; even powers start from `|X|` (no sign loss). -/
def powD (X : I) (n : Nat) : I := if n % 2 == 0 then mulPow (absD X) n else mulPow X n

/-- `π ∈ [3.14159265358979323846, 3.14159265358979323847]` (Mathlib's `pi_gt_d20`/`pi_lt_d20`). -/
def piLo : Rat := 314159265358979323846 / 100000000000000000000
def piHi : Rat := 314159265358979323847 / 100000000000000000000
def piD : I :=
  Interval128.Interval128.ofDD (Interval128.Interval128.ddOfRatDown piLo)
    (Interval128.Interval128.ddOfRatUp piHi)

def evalD (env : List I) : IExpr → I
  | .var i => env.getD i zeroD
  | .rat q => Interval128.Interval128.ofRat q
  | .add a b => Interval128.Interval128.add (evalD env a) (evalD env b)
  | .sub a b => Interval128.Interval128.sub (evalD env a) (evalD env b)
  | .mul a b => Interval128.Interval128.mul (evalD env a) (evalD env b)
  | .div a b => divD (evalD env a) (evalD env b)
  | .neg a => Interval128.Interval128.neg (evalD env a)
  | .inv a => invD (evalD env a)
  | .sqrt a => sqrtD (evalD env a)
  | .abs a => absD (evalD env a)
  | .pow a n => powD (evalD env a) n
  | .exp a => lift1 (.exp (.var 0)) (evalD env a)
  | .log a => lift1 (.log (.var 0)) (evalD env a)
  | .sin a => lift1 (.sin (.var 0)) (evalD env a)
  | .cos a => lift1 (.cos (.var 0)) (evalD env a)
  | .pi => piD
  | .atan a => lift1 (.atan (.var 0)) (evalD env a)
  | .atan2 a b => lift2 (.atan2 (.var 0) (.var 1)) (evalD env a) (evalD env b)
  | .sinh a => lift1 (.sinh (.var 0)) (evalD env a)
  | .cosh a => lift1 (.cosh (.var 0)) (evalD env a)
  | .tanh a => lift1 (.tanh (.var 0)) (evalD env a)
  | .log2 a => lift1 (.log2 (.var 0)) (evalD env a)
  | .log10 a => lift1 (.log10 (.var 0)) (evalD env a)
  | .tan a => lift1 (.tan (.var 0)) (evalD env a)
  | .asin a => lift1 (.asin (.var 0)) (evalD env a)
  | .acos a => lift1 (.acos (.var 0)) (evalD env a)
  | .ext k d a => lift1 (.ext k d (.var 0)) (evalD env a)

/-- Functions evaluated at Interval64 precision under `evalD` (for messages). -/
def lifted : IExpr → List String
  | .var _ | .rat _ | .pi => []
  | .add a b | .sub a b | .mul a b | .div a b => lifted a ++ lifted b
  | .neg a | .inv a | .sqrt a | .abs a | .pow a _ => lifted a
  | .exp a => "exp" :: lifted a
  | .log a => "log" :: lifted a
  | .sin a => "sin" :: lifted a
  | .cos a => "cos" :: lifted a
  | .atan a => "arctan" :: lifted a
  | .atan2 a b => "atan2" :: (lifted a ++ lifted b)
  | .sinh a => "sinh" :: lifted a
  | .cosh a => "cosh" :: lifted a
  | .tanh a => "tanh" :: lifted a
  | .log2 a => "logb 2" :: lifted a
  | .log10 a => "logb 10" :: lifted a
  | .tan a => "tan" :: lifted a
  | .asin a => "arcsin" :: lifted a
  | .acos a => "arccos" :: lifted a
  | .ext _ _ a => "extension function" :: lifted a

/-! ### Goal predicates: exact comparison of a double-double endpoint with a rational -/

/-- `f ≤ c`: the exact upper endpoint is `≤ c`. -/
def gLe (c : Rat) (F : I) : Bool :=
  match Interval128.Interval128.ddRat? F.uh F.ul with | some u => decide (u ≤ c) | none => false
def gLt (c : Rat) (F : I) : Bool :=
  match Interval128.Interval128.ddRat? F.uh F.ul with | some u => decide (u < c) | none => false
def gGe (c : Rat) (F : I) : Bool :=
  match Interval128.Interval128.ddRat? F.lh F.ll with | some l => decide (c ≤ l) | none => false
def gGt (c : Rat) (F : I) : Bool :=
  match Interval128.Interval128.ddRat? F.lh F.ll with | some l => decide (c < l) | none => false

/-! ### Bisection certificates with rational split points -/

inductive Cert where
  | leaf
  | split (i : Nat) (q : Rat) (l r : Cert)
  deriving Repr, Inhabited

/-- Left half of `X` at `q`: upper endpoint `q` rounded up. -/
def leftAt (X : I) (q : Rat) : I :=
  Interval128.Interval128.ofDD X.lo (Interval128.Interval128.ddOfRatUp q)
/-- Right half of `X` at `q`: lower endpoint `q` rounded down. -/
def rightAt (X : I) (q : Rat) : I :=
  Interval128.Interval128.ofDD (Interval128.Interval128.ddOfRatDown q) X.hi

def checkD (e : IExpr) (g : I → Bool) : Cert → List I → Bool
  | .leaf, env => g (evalD env e)
  | .split i q l r, env =>
    checkD e g l (env.set i (leftAt (env.getD i zeroD) q)) &&
      checkD e g r (env.set i (rightAt (env.getD i zeroD) q))

/-- Initial boxes from rational bounds. -/
def boxes : List (Rat × Rat) → List I
  | [] => []
  | (a, b) :: t =>
    Interval128.Interval128.ofDD (Interval128.Interval128.ddOfRatDown a)
      (Interval128.Interval128.ddOfRatUp b) :: boxes t

/-! ### Certificate search (compiled code; not trusted) -/

/-- Width of a box coordinate as a rational (`none` if an endpoint is not finite). -/
def widthQ (X : I) : Option Rat :=
  match Interval128.Interval128.ddRat? X.lh X.ll, Interval128.Interval128.ddRat? X.uh X.ul with
  | some a, some b => some (b - a)
  | _, _ => none

/-- Widest variable and its midpoint. -/
def pickSplit (env : List I) : Option (Nat × Rat) := Id.run do
  let mut best : Option (Nat × Rat × Rat) := none
  for h : i in [0:env.length] do
    let X := env[i]
    match Interval128.Interval128.ddRat? X.lh X.ll, Interval128.Interval128.ddRat? X.uh X.ul with
    | some a, some b =>
      if a < b then
        let w := b - a
        match best with
        | some (_, w', _) => if w' < w then best := some (i, w, (a + b) / 2)
        | none => best := some (i, w, (a + b) / 2)
    | _, _ => pure ()
  return best.map fun (i, _, m) => (i, m)

/-- Depth-first bisection (widest variable, midpoint) within `depth` / `maxEvals`. -/
partial def search (e : IExpr) (g : I → Bool) (depth maxEvals : Nat) :
    List I → StateM Nat (Option Cert)
  | env => do
    let n ← get
    if n ≥ maxEvals then return none
    set (n + 1)
    if g (evalD env e) then return some .leaf
    if depth == 0 then return none
    match pickSplit env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i zeroD
      let some l ← search e g (depth - 1) maxEvals (env.set i (leftAt X m)) | return none
      let some r ← search e g (depth - 1) maxEvals (env.set i (rightAt X m)) | return none
      return some (.split i m l r)

def Cert.leaves : Cert → Nat
  | .leaf => 1
  | .split _ _ l r => l.leaves + r.leaves

end Interval128.Refl
