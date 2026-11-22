/-
Rigorous 2D quadrature over rectangles (iterated integrals `∫_a^b ∫_c^d f x y dy dx`).

* `integrate2 F a b c d tol fuel` : outer adaptive zeroth-order rule in `x` whose integrand
  enclosure on a cell `X` is the inner adaptive rule in `y` for `Y ↦ F X Y`.
* `integrate2E0 e …` : `IExpr` in variables `0` (`x`) and `1` (`y`), zeroth-order cells.
* `integrate2E1 e …` : inner second-order cells in `y` (derivative `e.diff 1`), outer zeroth order.
At runtime `integrate2E0` / `integrate2E1` run in C over a tape (`c/iv64_quad.h`).
Soundness: `RealFP.Quad2` (Mathlib layer), with Fubini (`setIntegral_rect_eq`).
-/
import Interval64.Quad

namespace Interval64.Quad

open Interval64.KF (IExpr evalI)

def integrate2 (F : Interval64 → Interval64 → Interval64) (a b c d tol : Float) (fuel : Nat) :
    Interval64 :=
  integrate (cell0 fun X => integrate (cell0 (F X)) c d tol fuel) a b tol fuel

@[extern "iv64_quad_integrate2"]
opaque integrate2TapeExt (code : @& ByteArray) (consts : @& FloatArray)
  (fns : @& Array (Interval64 → Interval64)) (atan2 : @& (Interval64 → Interval64 → Interval64))
  (rF rD : UInt32) (order : UInt8) (a b c d tol : Float) (fuel : @& Nat) : Interval64

def integrate2E0Impl (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  match KF.Tape.compile [e] with
  | some t => integrate2TapeExt t.code t.consts KF.Tape.unaryFns KF.Tape.atan2Fn t.roots[0]!
      t.roots[0]! 0 a b c d tol fuel
  | none => integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel

def integrate2E1Impl (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  match KF.Tape.compile [e, e.diff 1] with
  | some t => integrate2TapeExt t.code t.consts KF.Tape.unaryFns KF.Tape.atan2Fn t.roots[0]!
      t.roots[1]! 1 a b c d tol fuel
  | none => integrate (cell0 fun X =>
      integrate (cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel)
      a b tol fuel

@[implemented_by integrate2E0Impl]
def integrate2E0 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel

@[implemented_by integrate2E1Impl]
def integrate2E1 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate (cell0 fun X =>
    integrate (cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel)
    a b tol fuel

end Interval64.Quad
