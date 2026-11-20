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
#print axioms Interval64Proofs.Canonical.roundDirected_zero_or_shaped
#print axioms Interval64Proofs.PackFinite.bitsToEVal_pack_canonical
#print axioms Interval64Proofs.PackFinite.loEncloses_packDirected_shaped
#print axioms Interval64Proofs.PackFinite.hiEncloses_packDirected_shaped
#print axioms Interval64Proofs.AddBits.unpack_finite_is_canonical
#print axioms Interval64Proofs.AddBits.add_encloses
#print axioms Interval64Proofs.AddBits.add_mem
#print axioms Interval64Proofs.AddBits.add_exact_of_same
#print axioms Interval64Proofs.AddBits.target_eq_of_normal
