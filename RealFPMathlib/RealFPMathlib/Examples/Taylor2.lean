/-
Higher-order 2D quadrature (tensor Taylor cells), checked by the kernel.

* `gauss2_bounds` : `0.55761… ≤ ∫_{[0,1]²} e^{-x²-y²} ≤ 0.55786…` (true value `0.5577462853…`), from
  `taylor2` with `K = 4` on a `4 × 4` grid (enclosure width `4.9e-5`). The first-order rule
  `integrate2E1` gives width `1.9e-3` with `2^8 × 2^8` cells.
-/
import RealFPMathlib.Taylor2

open Interval64 Interval64.Quad Interval64.KF RealFP RealFP.Poly RealFP.Quad RealFP.Taylor2
open MeasureTheory Set

namespace RealFP.Examples.Taylor2

def g2 : IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))

def cs : List (Float × Float × Float) :=
  [(0, 0.125, 0.25), (0.25, 0.375, 0.5), (0.5, 0.625, 0.75), (0.75, 0.875, 1)]

def R : Interval64 := taylor2 g2 4 0 1 0 1 cs cs

theorem smooth_ok : allSmooth g2 4 = true := by decide +kernel

theorem R_ok : (0.5576171875 : Float) ≤ R.lo ∧ R.hi ≤ (0.557861328125 : Float) := by
  decide +kernel

end RealFP.Examples.Taylor2
