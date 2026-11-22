/-
Rigorous 2D quadrature over rectangles (iterated integrals `∫_a^b ∫_c^d f x y dy dx`).

* `integrate2 F a b c d tol fuel` : outer adaptive zeroth-order rule in `x` whose integrand
  enclosure on a cell `X` is the inner adaptive rule in `y` for `Y ↦ F X Y`.
* `integrate2E0 e …` : `IExpr` in variables `0` (`x`) and `1` (`y`), zeroth-order cells.
* `integrate2E1 e …` : inner second-order cells in `y` (derivative `e.diff 1`), outer zeroth order.
Soundness: `RealFP.Quad2` (Mathlib layer), with Fubini (`setIntegral_rect_eq`).
-/
import Interval64.Quad

namespace Interval64.Quad

open Interval64.KF (IExpr evalI)

def integrate2 (F : Interval64 → Interval64 → Interval64) (a b c d tol : Float) (fuel : Nat) :
    Interval64 :=
  integrate (cell0 fun X => integrate (cell0 (F X)) c d tol fuel) a b tol fuel

def integrate2E0 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel

def integrate2E1 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate (cell0 fun X =>
    integrate (cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel)
    a b tol fuel

end Interval64.Quad
