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
#print axioms Interval64Proofs.ExactAdd.add_exact
#print axioms Interval64Proofs.ExactAdd.add_exact_int
#print axioms Interval64Proofs.ExactAdd.int_le_pow53_representable
#print axioms Interval64Proofs.ExactAdd.normalizeDirected_eq_of_canonical
#print axioms Interval64Proofs.ExactAdd.roundDirected_eq_of_canonical
#print axioms Interval64Proofs.Mul.mul_encloses
#print axioms Interval64Proofs.Mul.mul_mem_nonneg
#print axioms Interval64Proofs.Mul.mul_mem_nonpos
#print axioms Interval64Proofs.Mul.mul_mem_nonneg_nonpos
#print axioms Interval64Proofs.Mul.mul_mem_nonpos_nonneg
#print axioms Interval64Proofs.Mul.mul_exact
#print axioms Interval64Proofs.Mul.mul_exact_int
#print axioms Interval64Proofs.FloatBits.hi_le_of_native
#print axioms Interval64Proofs.FloatBits.float_le_rat
#print axioms Interval64Proofs.IntervalMem.add_mem_iv
#print axioms Interval64Proofs.IntervalMem.mul_mem_iv
#print axioms Interval64Proofs.Capstone.sq_add_le
#print axioms Interval64Proofs.Capstone.sq_add_le_of_exact
#print axioms Interval64Proofs.Capstone.demoHi_le'
#print axioms Interval64.NativeDecide.demoHi_le
#print axioms Interval64Proofs.Sub.sub_encloses
#print axioms Interval64Proofs.Sub.sub_exact
#print axioms Interval64Proofs.Sub.sub_exact_int
#print axioms Interval64Proofs.Sub.sub_mem_iv
#print axioms Interval64Proofs.Sub.not_memIv_invalid
#print axioms Interval64Proofs.RoundInexact.roundDirected_lo_acc
#print axioms Interval64Proofs.RoundInexact.roundDirected_hi_acc
#print axioms Interval64Proofs.Div.memIv_whole
#print axioms Interval64Proofs.Div.mag_div_bracket
#print axioms Interval64Proofs.Div.firstRoundedAcc_norm_of_enough
#print axioms Interval64Proofs.IntervalMem.mul_mem_iv_of_finite

