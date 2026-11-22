/-
Interval polynomials (monomial basis), univariate and bivariate.

* `IPoly` = `Array Interval64`, coefficients low degree first (`P.coeff k`, `[0, 0]` past
  the end). A real polynomial `p` is *in* `P` when `p.coeff k ∈ P.coeff k` for every `k`
  (`RealFP.Poly.Contains`, Mathlib layer).
* Evaluation: `eval P X` (Horner), `evalMV P dP X` (mean-value form, intersected with Horner).
* Arithmetic: `add`, `neg`, `sub`, `smul`, `mul`, `deriv`, `integ` (antiderivative with
  constant term `0`), `comp` (composition, Horner over polynomials), `shift P A = P(x + A)`.
* Sign certificates by bisection: `checkGe P c X fuel` (`c ≤ p x` on `X`), `checkGt`,
  `checkLe`, `checkLt`; range enclosure `range P X fuel` (hull over a uniform bisection).
* Bivariate `IPoly2` = `Array IPoly` (`P[j]` = coefficient polynomial in `x` of `y^j`):
  `eval2`, `checkGe2` / `checkGt2` (bisection in both variables).

The Lean definitions are the specifications (used by the proofs and by `decide +kernel`).
At runtime `eval`, `evalMV`, `rangeAux`, `checkGe`/`Gt`/`Le`/`Lt`, `eval2`, `checkGe2`/`Gt2`
run as single C routines (`c/iv64_poly.{h,c}`, `@[implemented_by]`), which perform the same
`Interval64` operations in the same order (bit-identical; differential tests).
-/
import Interval64.Matrix

namespace Interval64

open Mat (zeroI idot)

/-- Interval polynomial, coefficients low degree first. -/
abbrev IPoly := Array Interval64

namespace IPoly

/-- Coefficient `k` (`[0, 0]` past the end). -/
def coeff (P : IPoly) (k : Nat) : Interval64 := P.getD k zeroI

/-- `Σ_{k < len} c (off + k) X^k` by Horner's rule. -/
def hornerAux (c : Nat → Interval64) (X : Interval64) : Nat → Nat → Interval64
  | _, 0 => zeroI
  | off, 1 => c off
  | off, len + 2 => c off + X * hornerAux c X (off + 1) (len + 1)

/-- C implementation of `eval` (`c/iv64_poly.c`). -/
@[extern "iv64_poly_eval"] opaque evalExt (P : @& IPoly) (X : @& Interval64) : Interval64
def evalImpl (P : IPoly) (X : Interval64) : Interval64 := evalExt P X

/-- Interval Horner evaluation (C kernel `iv64_poly_eval` at runtime). -/
@[implemented_by evalImpl]
def eval (P : IPoly) (X : Interval64) : Interval64 := hornerAux P.coeff X 0 P.size

/-- Build from a coefficient function. -/
def ofFn (m : Nat) (f : Nat → Interval64) : IPoly := Array.ofFn (n := m) fun k => f k.val

/-- Outward enclosure of a polynomial with rational coefficients `l[0] + l[1] X + …`. -/
def ofRats (l : Array Rat) : IPoly := l.map ofRat

def add (P Q : IPoly) : IPoly := ofFn (max P.size Q.size) fun k => P.coeff k + Q.coeff k
def neg (P : IPoly) : IPoly := P.map Interval64.neg
def sub (P Q : IPoly) : IPoly := ofFn (max P.size Q.size) fun k => P.coeff k - Q.coeff k
/-- `C * P`. -/
def smul (C : Interval64) (P : IPoly) : IPoly := ofFn P.size fun k => C * P.coeff k

/-- Size of a product. -/
def mulSize (P Q : IPoly) : Nat := if P.size = 0 ∨ Q.size = 0 then 0 else P.size + Q.size - 1

/-- Product: coefficient `k` is `Σ_{i ≤ k} P_i Q_{k-i}`. -/
def mul (P Q : IPoly) : IPoly :=
  ofFn (mulSize P Q) fun k => idot (fun i => P.coeff i) (fun i => Q.coeff (k - i)) (k + 1)

/-- Derivative. -/
def deriv (P : IPoly) : IPoly := ofFn (P.size - 1) fun k => P.coeff (k + 1) * ofNat (k + 1)

/-- Antiderivative with constant term `0`: coefficient `k + 1` is `P_k / (k + 1)`. -/
def integ (P : IPoly) : IPoly :=
  ofFn (P.size + 1) fun k => if k = 0 then zeroI else P.coeff (k - 1) * ofRat (1 / (k : Rat))

instance : Add IPoly := ⟨add⟩
instance : Sub IPoly := ⟨sub⟩
instance : Mul IPoly := ⟨mul⟩

/-- `Σ_{k < len} P_{off+k} Q^k` (Horner over polynomials). -/
def compAux (P Q : IPoly) : Nat → Nat → IPoly
  | _, 0 => #[]
  | off, 1 => #[P.coeff off]
  | off, len + 2 => add #[P.coeff off] (mul Q (compAux P Q (off + 1) (len + 1)))

/-- Composition `P ∘ Q`. -/
def comp (P Q : IPoly) : IPoly := compAux P Q 0 P.size

/-- `P(x + A)`. -/
def shift (P : IPoly) (A : Interval64) : IPoly := comp P #[A, ⟨1, 1⟩]

@[extern "iv64_poly_eval_mv"]
opaque evalMVExt (P dP : @& IPoly) (X : @& Interval64) : Interval64
def evalMVImpl (P dP : IPoly) (X : Interval64) : Interval64 := evalMVExt P dP X

/-- Mean-value form at `m = mid X`: `P(m) + P'(X) (X - m)`, intersected with Horner
    (`dP` should be `deriv P`; Horner alone if `m` is infinite). -/
@[implemented_by evalMVImpl]
def evalMV (P dP : IPoly) (X : Interval64) : Interval64 :=
  let m := mid X
  let H := eval P X
  if m.isInf then H
  else intersect H (eval P (point m) + eval dP X * (X - point m))

@[extern "iv64_poly_range_aux"]
opaque rangeAuxExt (P dP : @& IPoly) (fuel : @& Nat) (X : @& Interval64) : Interval64
def rangeAuxImpl (P dP : IPoly) (fuel : Nat) (X : Interval64) : Interval64 := rangeAuxExt P dP fuel X

/-- Enclosure of `P` on `X` by bisection to depth `fuel` (hull of the mean-value forms). -/
@[implemented_by rangeAuxImpl]
def rangeAux (P dP : IPoly) : Nat → Interval64 → Interval64
  | 0, X => evalMV P dP X
  | fuel + 1, X => hull (rangeAux P dP fuel (bisect X).1) (rangeAux P dP fuel (bisect X).2)

def range (P : IPoly) (X : Interval64) (fuel : Nat) : Interval64 := rangeAux P (deriv P) fuel X

/-- Adaptive bisection test of a predicate `g` on the enclosure. -/
def checkAux (P dP : IPoly) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (evalMV P dP X)
  | fuel + 1, X =>
    g (evalMV P dP X) ||
      (checkAux P dP g fuel (bisect X).1 && checkAux P dP g fuel (bisect X).2)

/-- C implementation of `checkAux` with goal `mode` (0: `c ≤ lo`, 1: `c < lo`, 2: `hi ≤ c`,
    3: `hi < c`). -/
@[extern "iv64_poly_check"]
opaque checkAuxC (P dP : @& IPoly) (mode : UInt8) (c : Float) (fuel : @& Nat) (X : @& Interval64) : Bool

def checkGeImpl (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxC P (deriv P) 0 c fuel X
def checkGtImpl (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxC P (deriv P) 1 c fuel X
def checkLeImpl (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxC P (deriv P) 2 c fuel X
def checkLtImpl (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxC P (deriv P) 3 c fuel X

/-- `c ≤ p x` for all `x ∈ X` (certificate by bisection, at most `2^fuel` boxes). -/
@[implemented_by checkGeImpl]
def checkGe (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (c ≤ R.lo)) fuel X
@[implemented_by checkGtImpl]
def checkGt (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (c < R.lo)) fuel X
@[implemented_by checkLeImpl]
def checkLe (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (R.hi ≤ c)) fuel X
@[implemented_by checkLtImpl]
def checkLt (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (R.hi < c)) fuel X

end IPoly

/-- Bivariate interval polynomial: `P[j]` is the coefficient polynomial (in `x`) of `y^j`. -/
abbrev IPoly2 := Array IPoly

namespace IPoly2

def coeff (P : IPoly2) (j : Nat) : IPoly := P.getD j #[]

@[extern "iv64_poly2_eval"] opaque eval2Ext (P : @& IPoly2) (X Y : @& Interval64) : Interval64
def eval2Impl (P : IPoly2) (X Y : Interval64) : Interval64 := eval2Ext P X Y

/-- `Σ_j P_j(X) Y^j` (Horner in `y`, coefficients by Horner in `x`). -/
@[implemented_by eval2Impl]
def eval2 (P : IPoly2) (X Y : Interval64) : Interval64 :=
  IPoly.hornerAux (fun j => IPoly.eval (P.coeff j) X) Y 0 P.size

def checkAux2 (P : IPoly2) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (eval2 P X Y)
  | fuel + 1, X, Y =>
    g (eval2 P X Y) ||
      (if decide (width Y ≤ width X) then
        checkAux2 P g fuel (bisect X).1 Y && checkAux2 P g fuel (bisect X).2 Y
      else
        checkAux2 P g fuel X (bisect Y).1 && checkAux2 P g fuel X (bisect Y).2)

@[extern "iv64_poly2_check"]
opaque checkAux2C (P : @& IPoly2) (mode : UInt8) (c : Float) (fuel : @& Nat) (X Y : @& Interval64) : Bool

def checkGe2Impl (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2C P 0 c fuel X Y
def checkGt2Impl (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2C P 1 c fuel X Y

/-- `c ≤ p x y` on `X × Y` (bisection of the wider side, `fuel` levels). -/
@[implemented_by checkGe2Impl]
def checkGe2 (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2 P (fun R => decide (c ≤ R.lo)) fuel X Y
@[implemented_by checkGt2Impl]
def checkGt2 (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2 P (fun R => decide (c < R.lo)) fuel X Y

end IPoly2
end Interval64
