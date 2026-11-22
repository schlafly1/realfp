/-
**Optional, not built by default** (`lake build RealFPMathlibSlow`).

The first-round Float-spec 6×6 Hilbert PD example from `RealFPMathlib/Examples/MatrixPD.lean`
(`isPD` by `decide +kernel` on the Lean `Float` specification, ≈16 s of kernel type checking,
standard axioms only). The kernel-path `hilbert10_posDef` stays in the default build.
-/
import RealFPMathlib.Examples.MatrixPD

open Interval64 Interval64.Mat RealFP RealFP.Mat Matrix

namespace RealFP.Examples.MatrixPD

theorem isPD_hilbI6 : isPD (hilbI 6) = true := by decide +kernel

/-- The 6×6 Hilbert matrix is positive definite (Float-spec path). -/
theorem hilbert_posDef : (hilbert 6).PosDef :=
  posDef_of_isPD isPD_hilbI6 (hilbert_symm 6) (hilbert_mem 6)

end RealFP.Examples.MatrixPD
