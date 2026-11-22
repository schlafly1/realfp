/-
Axioms of the optional slow examples (library `RealFPMathlibSlow`, not built by default).
Run with: `scripts/check_axioms.sh RealFPMathlib RealFPMathlibSlowAxioms.lean` (from the repo root).
-/
import RealFPMathlibSlow.PolyQuad
import RealFPMathlibSlow.MatrixPD
import RealFPMathlibSlow.Taylor2
#print axioms RealFP.Examples.MatrixPD.isPD_hilbI6
#print axioms RealFP.Examples.MatrixPD.hilbert_posDef
#print axioms RealFP.Examples.PolyQuad.e4_check
#print axioms RealFP.Examples.PolyQuad.toReal_zero
#print axioms RealFP.Examples.PolyQuad.taylor_exp_pos
#print axioms RealFP.Examples.PolyQuad.R_ok
#print axioms RealFP.Examples.PolyQuad.toReal_one
#print axioms RealFP.Examples.PolyQuad.c_lo
#print axioms RealFP.Examples.PolyQuad.c_hi
#print axioms RealFP.Examples.PolyQuad.integral_mem_R
#print axioms RealFP.Examples.PolyQuad.gauss_integral_bounds
#print axioms RealFP.Examples.Taylor2.cert4
#print axioms RealFP.Examples.Taylor2.gauss2_bounds_tight
