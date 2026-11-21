import Interval64Proofs.KernelEq
open Float.Model Float.Model.UnpackedFloat Interval64.Spec Interval64.KF
example (b : UInt64) : (unpackMantissa (spec := spec64) b.toBitVec).toNat = b.toNat % 2^52 := by
  simp [unpackMantissa, BitVec.extractLsb'_toNat]
example (b : UInt64) : (unpackExponent (spec := spec64) b.toBitVec).toNat = b.toNat / 2^52 % 2048 := by
  simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
example (b : UInt64) : (unpackSign (spec := spec64) b.toBitVec).toNat = b.toNat / 2^63 := by
  have := b.toNat_lt
  simp [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega
example : (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit : Int) = 1075 := by decide
example : ((-1#11) : BitVec 11).toNat = 2047 := by decide
