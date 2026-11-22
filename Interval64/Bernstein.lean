/-
Bernstein range enclosures for interval polynomials (1D and 2D).

For a polynomial `q(t) = Σ_{i≤n} a_i t^i` the Bernstein coefficients of degree `n` are
`β_k = Σ_{i≤k} C(k,i)/C(n,i) · a_i`, and `q(t) = Σ_k β_k · C(n,k) t^k (1-t)^{n-k}` on `[0,1]`,
a convex combination, so `q([0,1]) ⊆ hull β_k`. Taking `n` larger than the degree is degree
elevation (tighter); bisecting the domain is subdivision. A box `[lo, hi]` is mapped to `[0,1]`
by `x = lo + (hi - lo) t`.

At runtime `bernOn`, `bernRange`, `checkGtB`/`GeB`, `bern2On`, `checkGt2B` run as C routines
(`c/iv64_poly.h`, `@[implemented_by]`, bit-identical; Bernstein degree `≤ 56`, otherwise the Lean
definition runs).

Soundness: `RealFP.Bern.mem_bernOn`, `mem_bernRange`, `lt_of_checkGtB` (1D) and
`mem_bern2On`, `lt_of_checkGt2B` (2D) in the Mathlib layer.
-/
import Interval64.Poly
import Interval64.Quad

namespace Interval64

open Mat (zeroI)

namespace IPoly

/-- Binomial coefficient (`Nat.choose` is not in core). -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `C(k, i) / C(n, i)`. -/
def bernQ (n k i : Nat) : Rat := (choose k i : Rat) / (choose n i : Rat)

/-- Bernstein coefficient `β_k` (degree `n`) of the coefficient function `c`. -/
def bernCoeffF (c : Nat → Interval64) (n k : Nat) : Interval64 :=
  (List.range (k + 1)).foldl (fun acc i => acc + ofRat (bernQ n k i) * c i) zeroI

/-- Hull of `f 0, …, f n`. -/
def hullUpTo (f : Nat → Interval64) : Nat → Interval64
  | 0 => f 0
  | n + 1 => hull (hullUpTo f n) (f (n + 1))

/-- Bernstein degree: at least the degree of `P`, at least `n` (elevation). -/
def bernDeg (P : IPoly) (n : Nat) : Nat := max n (P.size - 1)

/-- Enclosure of `P` on `[0, 1]` (degree `bernDeg P n`). -/
def bern01 (P : IPoly) (n : Nat) : Interval64 :=
  let N := bernDeg P n
  hullUpTo (fun k => bernCoeffF P.coeff N k) N

/-- C kernels need exact binomials as doubles: Bernstein degree `≤ 56`. -/
def bernCOK (N : Nat) : Bool := Nat.ble N 56

@[extern "iv64_bern_on"] opaque bernOnExt (P : @& IPoly) (X : @& Interval64) (n : @& Nat) : Interval64
def bernOnImpl (P : IPoly) (X : Interval64) (n : Nat) : Interval64 :=
  if bernCOK (bernDeg P n) then bernOnExt P X n
  else if Quad.finite X.lo && Quad.finite X.hi then
    bern01 (P.comp #[point X.lo, point X.hi - point X.lo]) n
  else P.eval X

/-- Enclosure of `P` on `X` (Horner if an endpoint is not finite). -/
@[implemented_by bernOnImpl]
def bernOn (P : IPoly) (X : Interval64) (n : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then
    bern01 (P.comp #[point X.lo, point X.hi - point X.lo]) n
  else P.eval X

/-- Subdivision: hull of `bernOn` over `2^fuel` boxes. -/
def bernRangeSpec (P : IPoly) (n : Nat) : Nat → Interval64 → Interval64
  | 0, X => bernOn P X n
  | fuel + 1, X => hull (bernRangeSpec P n fuel (bisect X).1) (bernRangeSpec P n fuel (bisect X).2)

@[extern "iv64_bern_range"]
opaque bernRangeExt (P : @& IPoly) (n : @& Nat) (fuel : @& Nat) (X : @& Interval64) : Interval64
def bernRangeImpl (P : IPoly) (n : Nat) (fuel : Nat) (X : Interval64) : Interval64 :=
  if bernCOK (bernDeg P n) then bernRangeExt P n fuel X else bernRangeSpec P n fuel X

/-- Subdivision: hull of `bernOn` over `2^fuel` boxes (C kernel at runtime). -/
@[implemented_by bernRangeImpl]
def bernRange (P : IPoly) (n : Nat) : Nat → Interval64 → Interval64
  | 0, X => bernOn P X n
  | fuel + 1, X => hull (bernRange P n fuel (bisect X).1) (bernRange P n fuel (bisect X).2)

/-- Adaptive check of `g` on the Bernstein enclosures. -/
def checkAuxB (P : IPoly) (n : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (bernOn P X n)
  | fuel + 1, X =>
    g (bernOn P X n) || (checkAuxB P n g fuel (bisect X).1 && checkAuxB P n g fuel (bisect X).2)

@[extern "iv64_bern_check"]
opaque checkAuxBExt (P : @& IPoly) (n : @& Nat) (mode : UInt8) (c : Float) (fuel : @& Nat)
  (X : @& Interval64) : Bool

def checkGtBImpl (P : IPoly) (c : Float) (X : Interval64) (n fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf &&
    if bernCOK (bernDeg P n) then checkAuxBExt P n 1 c fuel X
    else checkAuxB P n (fun R => decide (c < R.lo)) fuel X
def checkGeBImpl (P : IPoly) (c : Float) (X : Interval64) (n fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf &&
    if bernCOK (bernDeg P n) then checkAuxBExt P n 0 c fuel X
    else checkAuxB P n (fun R => decide (c ≤ R.lo)) fuel X

@[implemented_by checkGtBImpl]
def checkGtB (P : IPoly) (c : Float) (X : Interval64) (n fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxB P n (fun R => decide (c < R.lo)) fuel X
@[implemented_by checkGeBImpl]
def checkGeB (P : IPoly) (c : Float) (X : Interval64) (n fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxB P n (fun R => decide (c ≤ R.lo)) fuel X

end IPoly

namespace IPoly2

def maxSizeL : List IPoly → Nat
  | [] => 0
  | Q :: Qs => max Q.size (maxSizeL Qs)

def maxSize (P : IPoly2) : Nat := maxSizeL P.toList

/-- Degrees used by `bern2On` are within the C kernel's range. -/
def bern2COK (P : IPoly2) (n m : Nat) : Bool :=
  IPoly.bernCOK (max n (maxSize P - 1)) && IPoly.bernCOK (max m (P.size - 1))

@[extern "iv64_bern2_on"]
opaque bern2OnExt (P : @& IPoly2) (X Y : @& Interval64) (n m : @& Nat) : Interval64

def bern2OnSpec (P : IPoly2) (X Y : Interval64) (n m : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then
    let Q : IPoly2 := P.map fun Pj => Pj.comp #[point X.lo, point X.hi - point X.lo]
    let N := max n (maxSize Q - 1)
    IPoly.hullUpTo (fun k =>
      IPoly.bernOn (IPoly.ofFn Q.size fun j => IPoly.bernCoeffF (Q.coeff j).coeff N k) Y m) N
  else P.eval2 X Y

def bern2OnImpl (P : IPoly2) (X Y : Interval64) (n m : Nat) : Interval64 :=
  if bern2COK P n m then bern2OnExt P X Y n m else bern2OnSpec P X Y n m

/-- Tensor Bernstein enclosure of `p(x, y) = Σ_j P_j(x) y^j` on `X × Y`: with
    `x = lo + (hi - lo) s`, each `P_j(x(s)) = Σ_k β_{k,j} B_k(s)`; for each `k` the polynomial
    `Σ_j β_{k,j} y^j` is enclosed on `Y` by the 1D Bernstein enclosure; hull over `k`. -/
@[implemented_by bern2OnImpl]
def bern2On (P : IPoly2) (X Y : Interval64) (n m : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then
    let Q : IPoly2 := P.map fun Pj => Pj.comp #[point X.lo, point X.hi - point X.lo]
    let N := max n (maxSize Q - 1)
    IPoly.hullUpTo (fun k =>
      IPoly.bernOn (IPoly.ofFn Q.size fun j => IPoly.bernCoeffF (Q.coeff j).coeff N k) Y m) N
  else P.eval2 X Y

def checkAux2B (P : IPoly2) (n m : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (bern2On P X Y n m)
  | fuel + 1, X, Y =>
    g (bern2On P X Y n m) ||
      (checkAux2B P n m g fuel (bisect X).1 (bisect Y).1 &&
        checkAux2B P n m g fuel (bisect X).1 (bisect Y).2 &&
        checkAux2B P n m g fuel (bisect X).2 (bisect Y).1 &&
        checkAux2B P n m g fuel (bisect X).2 (bisect Y).2)

@[extern "iv64_bern2_check"]
opaque checkAux2BExt (P : @& IPoly2) (n m : @& Nat) (mode : UInt8) (c : Float) (fuel : @& Nat)
  (X Y : @& Interval64) : Bool

def checkGt2BImpl (P : IPoly2) (c : Float) (X Y : Interval64) (n m fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf &&
    if bern2COK P n m then checkAux2BExt P n m 1 c fuel X Y
    else checkAux2B P n m (fun R => decide (c < R.lo)) fuel X Y

@[implemented_by checkGt2BImpl]
def checkGt2B (P : IPoly2) (c : Float) (X Y : Interval64) (n m fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAux2B P n m (fun R => decide (c < R.lo)) fuel X Y

end IPoly2

end Interval64
