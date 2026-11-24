/-
The kernel ("KF/KI" bit-pattern) path under one namespace.

The definitions live in `Interval64.KF` (core, Mathlib-free), `Interval64.KF.KM` / `KQ`
(matrices, quadrature) and the soundness theorems in `RealFP.KM` / `RealFP.KQ`. This file
re-exports the ones needed for hand-written certificates into `RealFP`, so `open RealFP` is
enough: `KI`, `IExpr`, `IExpr.denote`, `ofRatFn`, `PDCert`, `pdCheckL`, `pdCheckK`, `ratMatOK`,
`quadK`, `quadBound`, `posDef_of_ratMat`, `posDef_of_pdCheckL`, `posDef_of_pdCheckK`,
`lt_eigenvalue_of_posDef_sub`, `integral_mem_quadK`, `integral_bounds_of_quadBound`. These are
aliases (`export`), so the original names keep working unchanged. The elaborators `ki_lit%`,
`pd_certs%`, `bits%`, `cells%` need no namespace.
-/
import RealFPMathlib.KMatrix
import RealFPMathlib.KQuad
import RealFPMathlib.IntervalSound
import Interval64.Kernel.QuadCert
import Interval64.Kernel.MatrixCert

namespace RealFP

export Interval64.KF (KI IExpr)
export Interval64.KF.KM (ofRatFn PDCert pdCheckL pdCheckK ratMatOK)
export Interval64.KF.KQ (quadK quadBound)
export RealFP.KM (posDef_of_ratMat posDef_of_pdCheckL posDef_of_pdCheckK
  lt_eigenvalue_of_posDef_sub)
export RealFP.KQ (integral_mem_quadK integral_bounds_of_quadBound)

namespace IExpr
export Interval64.KF.IExpr (denote)
end IExpr

end RealFP
