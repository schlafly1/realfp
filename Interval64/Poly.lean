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

Everything is plain Lean over the `Interval64` operations (which run on the C kernels).
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

/-- Interval Horner evaluation. -/
def eval (P : IPoly) (X : Interval64) : Interval64 := hornerAux P.coeff X 0 P.size

/-- Build from a coefficient function. -/
def ofFn (m : Nat) (f : Nat → Interval64) : IPoly := Array.ofFn (n := m) fun k => f k.val

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

/-- Mean-value form at `m = mid X`: `P(m) + P'(X) (X - m)`, intersected with Horner
    (`dP` should be `deriv P`; Horner alone if `m` is infinite). -/
def evalMV (P dP : IPoly) (X : Interval64) : Interval64 :=
  let m := mid X
  let H := eval P X
  if m.isInf then H
  else intersect H (eval P (point m) + eval dP X * (X - point m))

/-- Enclosure of `P` on `X` by bisection to depth `fuel` (hull of the mean-value forms). -/
def rangeAux (P dP : IPoly) : Nat → Interval64 → Interval64
  | 0, X => evalMV P dP X
  | fuel + 1, X =>
    let (X₁, X₂) := bisect X
    hull (rangeAux P dP fuel X₁) (rangeAux P dP fuel X₂)

def range (P : IPoly) (X : Interval64) (fuel : Nat) : Interval64 := rangeAux P (deriv P) fuel X

/-- Adaptive bisection test of a predicate `g` on the enclosure. -/
def checkAux (P dP : IPoly) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (evalMV P dP X)
  | fuel + 1, X =>
    g (evalMV P dP X) ||
      (let (X₁, X₂) := bisect X
       checkAux P dP g fuel X₁ && checkAux P dP g fuel X₂)

/-- `c ≤ p x` for all `x ∈ X` (certificate by bisection, at most `2^fuel` boxes). -/
def checkGe (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (c ≤ R.lo)) fuel X
def checkGt (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (c < R.lo)) fuel X
def checkLe (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (R.hi ≤ c)) fuel X
def checkLt (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux P (deriv P) (fun R => decide (R.hi < c)) fuel X

end IPoly

/-- Bivariate interval polynomial: `P[j]` is the coefficient polynomial (in `x`) of `y^j`. -/
abbrev IPoly2 := Array IPoly

namespace IPoly2

def coeff (P : IPoly2) (j : Nat) : IPoly := P.getD j #[]

/-- `Σ_j P_j(X) Y^j` (Horner in `y`, coefficients by Horner in `x`). -/
def eval2 (P : IPoly2) (X Y : Interval64) : Interval64 :=
  IPoly.hornerAux (fun j => IPoly.eval (P.coeff j) X) Y 0 P.size

def checkAux2 (P : IPoly2) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (eval2 P X Y)
  | fuel + 1, X, Y =>
    g (eval2 P X Y) ||
      (if decide (width Y ≤ width X) then
        let (X₁, X₂) := bisect X
        checkAux2 P g fuel X₁ Y && checkAux2 P g fuel X₂ Y
      else
        let (Y₁, Y₂) := bisect Y
        checkAux2 P g fuel X Y₁ && checkAux2 P g fuel X Y₂)

/-- `c ≤ p x y` on `X × Y` (bisection of the wider side, `fuel` levels). -/
def checkGe2 (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2 P (fun R => decide (c ≤ R.lo)) fuel X Y
def checkGt2 (P : IPoly2) (c : Float) (X Y : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2 P (fun R => decide (c < R.lo)) fuel X Y

end IPoly2
end Interval64
