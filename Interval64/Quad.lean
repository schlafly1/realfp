/-
Rigorous quadrature.

* `polyIntegral P A B` : `∫_a^b p` for `p ∈ P`, `a ∈ A`, `b ∈ B` (exact antiderivative
  `integ P`, evaluated by Horner at both ends).
* `cell0 F lo hi` : `F [lo, hi] · (hi - lo)` (`F` an interval extension of `f`).
* `cell1 F D lo hi` : second-order cell rule from a derivative enclosure `D` of `f'`:
  with `m = mid [lo, hi]`, `X = [lo, hi]`,
  `∫ f ∈ F(m) (hi - lo) + D(X) (hi - m)²/2 + (-D(X)) (m - lo)²/2`
  (mean value theorem on each half), intersected with `cell0`. Error `O(width³)` per cell.
* `quadAux cell tol fuel lo hi` : adaptive bisection (stop when the cell enclosure is narrower
  than `tol`, halving `tol` on each split; at most `fuel` levels); sum of the cells.
* `integrate cell a b tol fuel` : `whole` unless `a ≤ b` are finite.
* `IExpr` versions `integrateE0 e …`, `integrateE1 e …` (`f x = e.denote [x]`, derivative by
  `IExpr.diff 0`).
Soundness: `RealFPMathlib/Quad.lean` (Mathlib `intervalIntegral`).
-/
import Interval64.Poly
import Interval64.Kernel.Deriv

namespace Interval64.Quad

open Interval64.KF (IExpr evalI)

def polyIntegral (P : IPoly) (A B : Interval64) : Interval64 :=
  let I := P.integ
  I.eval B - I.eval A

def half : Interval64 := ofRat (1 / 2)

def cell0 (F : Interval64 → Interval64) (lo hi : Float) : Interval64 :=
  F ⟨lo, hi⟩ * (point hi - point lo)

def cell1 (F D : Interval64 → Interval64) (lo hi : Float) : Interval64 :=
  let X : Interval64 := ⟨lo, hi⟩
  let m := mid X
  if m.isInf then cell0 F lo hi
  else
    let M := point m
    let DX := D X
    let Qa := square (point hi - M) * half
    let Qb := square (M - point lo) * half
    intersect (cell0 F lo hi) (F M * (point hi - point lo) + DX * Qa + (-DX) * Qb)

def quadAux (cell : Float → Float → Interval64) : Nat → Float → Float → Float → Interval64
  | 0, _, lo, hi => cell lo hi
  | fuel + 1, tol, lo, hi =>
    let R := cell lo hi
    if decide (width R ≤ tol) then R
    else
      let m := mid ⟨lo, hi⟩
      quadAux cell fuel (tol / 2) lo m + quadAux cell fuel (tol / 2) m hi

def finite (x : Float) : Bool := !x.isNaN && !x.isInf

def integrate (cell : Float → Float → Interval64) (a b tol : Float) (fuel : Nat) : Interval64 :=
  if finite a && finite b && decide (a ≤ b) then quadAux cell fuel tol a b else whole

/-- `∫_a^b e(x) dx`, zeroth-order cells. -/
def integrateE0 (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  integrate (cell0 fun X => evalI [X] e) a b tol fuel

/-- `∫_a^b e(x) dx`, second-order cells (derivative `e.diff 0`). -/
def integrateE1 (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  integrate (cell1 (fun X => evalI [X] e) (fun X => evalI [X] (e.diff 0))) a b tol fuel

end Interval64.Quad
