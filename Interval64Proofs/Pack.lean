/-
`pack` / `unpack` value preservation for the forms produced by directed rounding,
and enclosure of `packDirected`.
-/
import Interval64Proofs.Add
import Init.Data.BitVec.Lemmas
import Init.Data.UInt.Lemmas

namespace Interval64Proofs.Pack

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Add
open Float.Model
open Float.Model.UnpackedFloat

@[simp]
theorem unpackSign_packComponents {spec : Format} {sign : Sign}
    {exponent : BitVec spec.exponentBits}
    {mantissa : BitVec spec.mantissaBitsWithoutImplicit} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  simp [unpackSign, packComponents, BitVec.getLsbD_append]
  have h1 : ¬ (spec.mantissaBitsWithoutImplicit + spec.exponentBits + i <
      spec.mantissaBitsWithoutImplicit) := by omega
  have h2 : ¬ (spec.mantissaBitsWithoutImplicit + spec.exponentBits + i -
      spec.mantissaBitsWithoutImplicit < spec.exponentBits) := by
    have : 0 < spec.exponentBits := Nat.lt_of_lt_of_le (by decide : 0 < 2) spec.he
    omega
  simp [h1, h2]
  have hid : spec.mantissaBitsWithoutImplicit + spec.exponentBits + i -
      spec.mantissaBitsWithoutImplicit - spec.exponentBits = i := by omega
  simp [hid, BitVec.getLsbD_eq_getElem, hi]

theorem Sign_ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> simp [Sign.ofBitVec, Sign.toBitVec]

theorem unpackBits_packBits (u : UnpackedFloat) :
    unpackBits (packBits u) = UnpackedFloat.unpack spec64 (UnpackedFloat.pack spec64 u) := by
  simp [unpackBits, packBits, UInt64.toBitVec_ofBitVec]

theorem unpack_packedZero (s : Sign) :
    unpack spec64 (packedZero spec64 s) = .zero s := by
  unfold packedZero UnpackedFloat.unpack
  simp [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents, Sign_ofBitVec_toBitVec]

theorem unpack_packedInfinity (s : Sign) :
    unpack spec64 (packedInfinity spec64 s) = .infinity s := by
  unfold packedInfinity UnpackedFloat.unpack
  simp [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents, Sign_ofBitVec_toBitVec]

theorem unpackBits_zero (s : Sign) :
    unpackBits (packBits (.zero s)) = .zero s := by
  rw [unpackBits_packBits]
  simp [UnpackedFloat.pack, unpack_packedZero]

theorem unpackBits_inf (s : Sign) :
    unpackBits (packBits (.infinity s)) = .infinity s := by
  rw [unpackBits_packBits]
  simp [UnpackedFloat.pack, unpack_packedInfinity]

theorem bitsToEVal_pack_zero (s : Sign) :
    bitsToEVal (packBits (.zero s)) = some (.rat 0) := by
  simp [bitsToEVal, unpackBits_zero]

theorem bitsToEVal_pack_inf (s : Sign) :
    bitsToEVal (packBits (.infinity s)) =
      some (match s with
        | .negative => .negInf
        | .positive => .posInf) := by
  simp [bitsToEVal, unpackBits_inf]
  cases s <;> rfl


theorem packDirected_zero (up : Bool) (s : Sign) :
    packDirected up (.zero s) = packBits (.zero s) :=
  rfl

theorem packDirected_inf (up : Bool) (s : Sign) :
    packDirected up (.infinity s) = packBits (.infinity s) :=
  rfl

theorem loEncloses_packDirected_zero (up : Bool) (s : Sign) (x : Rat) :
    loEncloses? (bitsToEVal (packDirected up (.zero s))) x ↔ 0 ≤ x := by
  simp [packDirected_zero, bitsToEVal_pack_zero, loEncloses?]

theorem hiEncloses_packDirected_zero (up : Bool) (s : Sign) (x : Rat) :
    hiEncloses? (bitsToEVal (packDirected up (.zero s))) x ↔ x ≤ 0 := by
  simp [packDirected_zero, bitsToEVal_pack_zero, hiEncloses?]

theorem loEncloses_packDirected_inf (up : Bool) (s : Sign) (x : Rat) :
    loEncloses? (bitsToEVal (packDirected up (.infinity s))) x ↔ s = .negative := by
  simp [packDirected_inf, bitsToEVal_pack_inf, loEncloses?]
  cases s <;> simp

theorem hiEncloses_packDirected_inf (up : Bool) (s : Sign) (x : Rat) :
    hiEncloses? (bitsToEVal (packDirected up (.infinity s))) x ↔ s = .positive := by
  simp [packDirected_inf, bitsToEVal_pack_inf, hiEncloses?]
  cases s <;> simp

end Interval64Proofs.Pack
