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

#print axioms Interval64Proofs.Div.divCore_enough_bits
#print axioms Interval64Proofs.Div.div_encloses
#print axioms Interval64Proofs.Div.div_exact
#print axioms Interval64Proofs.Div.div_mem_iv

#print axioms Interval64Proofs.Sqrt.sqrtCore_enough_bits
#print axioms Interval64Proofs.Sqrt.sqrt_mem_rat
#print axioms Interval64Proofs.Sqrt.sqrt_mem_iv
#print axioms Interval64Proofs.Sqrt.sqrt_exact
#print axioms Interval64Proofs.Sqrt.sqrt_nine_exact


-- Representability, `ofRat` rounding, and tightness
#print axioms Interval64Proofs.OfRat.ofRatDown_isRoundDown
#print axioms Interval64Proofs.OfRat.ofRatUp_isRoundUp
#print axioms Interval64Proofs.OfRat.ofRat_exact
#print axioms Interval64Proofs.OfRat.representable_iff_ofRatDown
#print axioms Interval64Proofs.OfRat.representable_iff_ofRatUp
#print axioms Interval64Proofs.OfRat.isRepresentable_iff
#print axioms Interval64Proofs.OfRat.ofRatDown_greatest
#print axioms Interval64Proofs.OfRat.ofRatUp_least
#print axioms Interval64Proofs.OfRat.ofRatDown_negInf_iff
#print axioms Interval64Proofs.OfRat.ofRatUp_posInf_iff
#print axioms Interval64Proofs.OfRat.memIv_ofRat
#print axioms Interval64Proofs.OfRat.ofRat_tight
#print axioms Interval64Proofs.OfRat.memIv_ofRatInterval
#print axioms Interval64Proofs.RoundOpt.roundDirected_isRoundDown
#print axioms Interval64Proofs.RoundOpt.roundDirected_isRoundUp
#print axioms Interval64Proofs.Tight.add_isRoundDown
#print axioms Interval64Proofs.Tight.add_isRoundUp
#print axioms Interval64Proofs.Tight.sub_isRoundDown
#print axioms Interval64Proofs.Tight.sub_isRoundUp
#print axioms Interval64Proofs.Tight.mul_isRoundDown
#print axioms Interval64Proofs.Tight.mul_isRoundUp
#print axioms Interval64Proofs.Tight.div_isRoundDown
#print axioms Interval64Proofs.Tight.div_isRoundUp
#print axioms Interval64Proofs.Tight.add_tight
#print axioms Interval64Proofs.Tight.sub_tight
#print axioms Interval64Proofs.Tight.mul_tight
#print axioms Interval64Proofs.Tight.div_tight
#print axioms Interval64Proofs.Tight.addDown_eq_ofRatDown
#print axioms Interval64Proofs.Tight.addUp_eq_ofRatUp
#print axioms Interval64Proofs.Tight.subDown_eq_ofRatDown
#print axioms Interval64Proofs.Tight.subUp_eq_ofRatUp
#print axioms Interval64Proofs.Tight.mulDown_eq_ofRatDown
#print axioms Interval64Proofs.Tight.mulUp_eq_ofRatUp
#print axioms Interval64Proofs.Tight.divDown_eq_ofRatDown
#print axioms Interval64Proofs.Tight.divUp_eq_ofRatUp
#print axioms Interval64Proofs.TightIv.add_iv_tight
#print axioms Interval64Proofs.TightIv.sub_iv_tight
#print axioms Interval64Proofs.TightIv.add_iv_optimal
#print axioms Interval64Proofs.TightIv.sub_iv_optimal
#print axioms Interval64Proofs.TightIv.mul_iv_optimal
#print axioms Interval64Proofs.TightIv.div_iv_optimal
#print axioms Interval64Proofs.TightSqrt.sqrt_tight
#print axioms Interval64Proofs.TightSqrt.sqrtDown_float_tight
#print axioms Interval64Proofs.TightSqrt.sqrtUp_float_tight
#print axioms Interval64Proofs.TightSqrt.sqrt_iv_tight
#print axioms Interval64Proofs.TightSqrt.sqrt_iv_optimal
