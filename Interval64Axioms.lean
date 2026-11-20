/-
Print the axioms used by the enclosure theorems.
Run with: `lake build interval64_axioms` or `lake env lean Interval64Axioms.lean`.
-/
import Interval64Proofs

#print axioms Interval64Proofs.Add.addU_finite_lo
#print axioms Interval64Proofs.Add.addU_finite_hi
#print axioms Interval64Proofs.RoundDirected.roundDirected_lo
#print axioms Interval64Proofs.RoundDirected.roundDirected_hi
#print axioms Interval64Proofs.RoundDirected.normalizeDirected_lo
#print axioms Interval64Proofs.RoundDirected.normalizeDirected_hi
#print axioms Interval64Proofs.Pack.loEncloses_packDirected_zero
#print axioms Interval64Proofs.Pack.bitsToEVal_pack_inf
