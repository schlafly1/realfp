/-
Correctness of the kernel fast path `Interval64.KF`: each `KF` operation on `Nat` bit
patterns equals the corresponding `Interval64.Spec` operation (bit for bit, all inputs).
-/
import Interval64.Kernel.Nat
import Interval64.Spec
import Interval64Proofs.RoundDirected

set_option linter.unusedSimpArgs false

namespace Interval64.KF

open Float.Model Float.Model.UnpackedFloat Interval64.Spec

theorem ifB_eq (c : Bool) (t e : Nat) :
    Bool.casesOn (motive := fun _ => Nat) c e t = if c = true then t else e := by
  cases c <;> rfl

/-! ### Raw `Nat` functions to notation -/

theorem raw_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem raw_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem raw_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem raw_div (a b : Nat) : Nat.div a b = a / b := rfl
theorem raw_mod (a b : Nat) : Nat.mod a b = a % b := rfl
theorem raw_pow (a b : Nat) : Nat.pow a b = a ^ b := rfl
theorem raw_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem raw_xor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem raw_shiftLeft (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
theorem raw_shiftRight (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
theorem raw_succ (a : Nat) : Nat.succ a = a + 1 := rfl

/-- Normal form for the raw kernel functions. -/
theorem ble_true (a b : Nat) : (Nat.ble a b = true) = (a ≤ b) := by simp [Nat.ble_eq]
theorem blt_true (a b : Nat) : (Nat.blt a b = true) = (a < b) := by simp [Nat.blt_eq]
theorem beq_true (a b : Nat) : (Nat.beq a b = true) = (a = b) := by simp [Nat.beq_eq]

/-! ### `lg` and `isqrt` -/

theorem lg_eq (n : Nat) : lg n = n.log2 := by
  unfold lg
  generalize lgGuess n = k
  simp only [ifB_eq, Bool.and_eq_true, ble_true, blt_true, raw_shiftLeft, Nat.one_mul, raw_succ]
  split
  · rename_i h
    have hn : n ≠ 0 := by have := Nat.two_pow_pos k; omega
    exact ((Nat.log2_eq_iff hn).2 h).symm
  · rfl

theorem isqrt_eq (n : Nat) : isqrt n = n.sqrt := by
  unfold isqrt
  generalize isqrtFix n (isqrtGuess n) = r
  simp only [ifB_eq, Bool.and_eq_true, ble_true, blt_true, raw_mul, raw_succ]
  split
  · rename_i h
    have h1 := Nat.sqrt_le n
    have h2 := Nat.lt_succ_sqrt n
    simp only [Nat.succ_eq_add_one] at h2
    -- uniqueness of the integer square root
    rcases Nat.lt_trichotomy r n.sqrt with hlt | heq | hgt
    · exfalso
      have : (r + 1) * (r + 1) ≤ n.sqrt * n.sqrt := Nat.mul_le_mul hlt hlt
      omega
    · exact heq
    · exfalso
      have : (n.sqrt + 1) * (n.sqrt + 1) ≤ r * r := Nat.mul_le_mul hgt hgt
      omega
  · rfl

/-! ### Fields of a bit pattern -/

theorem magB_eq (n : Nat) : magB n = n % 2 ^ 63 := by
  unfold magB
  rw [raw_land, show (0x7FFFFFFFFFFFFFFF : Nat) = 2 ^ 63 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem fr_eq (n : Nat) : fr n = n % 2 ^ 52 := by
  unfold fr
  rw [raw_land, show (0xFFFFFFFFFFFFF : Nat) = 2 ^ 52 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem ex_eq (n : Nat) : ex n = n / 2 ^ 52 % 2048 := by
  unfold ex
  rw [raw_shiftRight, magB_eq, show (2 : Nat) ^ 63 = 2 ^ 52 * 2048 by decide,
    Nat.mod_mul_right_div_self]

theorem sgn_eq (n : Nat) : sgn n = n / 2 ^ 63 := by
  unfold sgn; rw [raw_shiftRight]

theorem magB_split (n : Nat) : n % 2 ^ 63 = n / 2 ^ 52 % 2048 * 2 ^ 52 + n % 2 ^ 52 := by
  have h1 := Nat.div_add_mod (n % 2 ^ 63) (2 ^ 52)
  rw [show (2 : Nat) ^ 63 = 2 ^ 52 * 2048 by decide, Nat.mod_mul_right_div_self,
    Nat.mod_mul_right_mod] at h1
  rw [show (2 : Nat) ^ 63 = 2 ^ 52 * 2048 by decide]
  rw [Nat.mul_comm] at h1
  omega

theorem n_split (n : Nat) : n = n / 2 ^ 63 * 2 ^ 63 + (n / 2 ^ 52 % 2048 * 2 ^ 52 + n % 2 ^ 52) := by
  rw [← magB_split]; have := Nat.div_add_mod n (2 ^ 63); rw [Nat.mul_comm] at this; omega

theorem two52_eq : two52 = 2 ^ 52 := by decide
theorem two53_eq : two53 = 2 ^ 53 := by decide
theorem signBit_eq : signBit = 2 ^ 63 := by decide

theorem isNaN_iff (n : Nat) : isNaN n = true ↔ n / 2 ^ 52 % 2048 = 2047 ∧ n % 2 ^ 52 ≠ 0 := by
  unfold isNaN; rw [blt_true, magB_eq, magB_split]
  have : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have : n / 2 ^ 52 % 2048 < 2048 := Nat.mod_lt _ (by decide)
  simp only [infBits] at *
  omega

theorem isInf_iff (n : Nat) : isInf n = true ↔ n / 2 ^ 52 % 2048 = 2047 ∧ n % 2 ^ 52 = 0 := by
  unfold isInf; rw [beq_true, magB_eq, magB_split]
  have : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have : n / 2 ^ 52 % 2048 < 2048 := Nat.mod_lt _ (by decide)
  simp only [infBits] at *
  omega

theorem isZero_iff (n : Nat) : isZero n = true ↔ n / 2 ^ 52 % 2048 = 0 ∧ n % 2 ^ 52 = 0 := by
  unfold isZero; rw [beq_true, magB_eq, magB_split]
  have : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  omega

theorem mant_eq (n : Nat) :
    mant n = if n / 2 ^ 52 % 2048 = 0 then n % 2 ^ 52 else n % 2 ^ 52 + 2 ^ 52 := by
  unfold mant; simp only [ifB_eq, beq_true, ex_eq, fr_eq, raw_add, two52_eq]

theorem qexp_eq (n : Nat) :
    qexp n = if n / 2 ^ 52 % 2048 = 0 then 1 else n / 2 ^ 52 % 2048 := by
  unfold qexp; simp only [ifB_eq, beq_true, ex_eq]

/-! ### Unpacking -/

/-- Sign from the sign bit. -/
def sOf (n : Nat) : Sign := if n / 2 ^ 63 = 0 then .positive else .negative

/-- Sign bit of a `Sign`. -/
def sb : Sign → Nat
  | .negative => 1
  | .positive => 0

theorem mant_pos {n : Nat} (h : ¬ isZero n = true) : 0 < mant n := by
  rw [isZero_iff] at h
  rw [mant_eq]
  split <;> omega

/-- `Nat`-level unpacking (proof device; mirrors `UnpackedFloat.unpack`). -/
def unpackN (n : Nat) : UnpackedFloat :=
  if isNaN n then .notANumber
  else if isInf n then .infinity (sOf n)
  else if h : isZero n then .zero (sOf n)
  else .finite (sOf n) (mant n) ((qexp n : Int) - 1075) (mant_pos h)

theorem unpackBits_eq (b : UInt64) : unpackBits b = unpackN b.toNat := by
  have hb := b.toNat_lt
  have hM : (unpackMantissa (spec := spec64) b.toBitVec).toNat = b.toNat % 2 ^ 52 := by
    simp [unpackMantissa, BitVec.extractLsb'_toNat]
  have hE : (unpackExponent (spec := spec64) b.toBitVec).toNat = b.toNat / 2 ^ 52 % 2048 := by
    simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hS : (unpackSign (spec := spec64) b.toBitVec).toNat = b.toNat / 2 ^ 63 := by
    simp [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have hbias : ((spec64.exponentBias : Int) + (52 : Nat)) = 1075 := by decide
  have hsign : Sign.ofBitVec (unpackSign (spec := spec64) b.toBitVec) = sOf b.toNat := by
    unfold Sign.ofBitVec sOf
    have : (unpackSign (spec := spec64) b.toBitVec = 0#1) ↔ b.toNat / 2 ^ 63 = 0 := by
      rw [BitVec.toNat_eq, hS]; simp
    by_cases h : b.toNat / 2 ^ 63 = 0
    · rw [ite_eq_left (this.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (this.1 h')), ite_eq_right h]
  have hneg1 : ((-1#11) : BitVec 11).toNat = 2047 := by decide
  unfold unpackBits UnpackedFloat.unpack unpackN
  simp only [hsign]
  have hmv_lt : (unpackMantissa (spec := spec64) b.toBitVec).toNat < 2 ^ 52 :=
    (unpackMantissa (spec := spec64) b.toBitVec).isLt
  by_cases hNaN : isNaN b.toNat = true
  · rw [ite_eq_left hNaN]
    rw [isNaN_iff] at hNaN
    have : unpackExponent (spec := spec64) b.toBitVec = -1#_ := by rw [BitVec.toNat_eq, hE]; exact hNaN.1.trans hneg1.symm
    rw [ite_eq_left this, ite_eq_right (by rw [BitVec.toNat_eq, hM]; simpa using hNaN.2)]
  rw [ite_eq_right hNaN]
  by_cases hInf : isInf b.toNat = true
  · rw [ite_eq_left hInf]
    rw [isInf_iff] at hInf
    have : unpackExponent (spec := spec64) b.toBitVec = -1#_ := by rw [BitVec.toNat_eq, hE]; exact hInf.1.trans hneg1.symm
    rw [ite_eq_left this, ite_eq_left (by rw [BitVec.toNat_eq, hM]; simpa using hInf.2)]
  rw [ite_eq_right hInf]
  have hne : ¬ unpackExponent (spec := spec64) b.toBitVec = -1#_ := by
    rw [BitVec.toNat_eq, hE, hneg1]
    intro h; rw [isNaN_iff] at hNaN; rw [isInf_iff] at hInf
    by_cases hf : b.toNat % 2 ^ 52 = 0
    · exact hInf ⟨h, hf⟩
    · exact hNaN ⟨h, hf⟩
  rw [ite_eq_right hne]
  by_cases hZ : isZero b.toNat = true
  · rw [dite_eq_left hZ]
    rw [isZero_iff] at hZ
    have h0 : unpackExponent (spec := spec64) b.toBitVec = 0#_ := by rw [BitVec.toNat_eq, hE]; simpa using hZ.1
    rw [ite_eq_left h0, dite_eq_left (by rw [BitVec.toNat_eq, hM]; simpa using hZ.2)]
  rw [dite_eq_right hZ]
  have hmant := mant_eq b.toNat
  have hq := qexp_eq b.toNat
  by_cases hE0 : b.toNat / 2 ^ 52 % 2048 = 0
  · have h0 : unpackExponent (spec := spec64) b.toBitVec = 0#_ := by rw [BitVec.toNat_eq, hE]; simpa using hE0
    rw [isZero_iff] at hZ
    have hm0 : ¬ unpackMantissa (spec := spec64) b.toBitVec = 0#_ := by
      rw [BitVec.toNat_eq, hM]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega
    rw [ite_eq_left h0, dite_eq_right hm0]
    rw [ite_eq_left hE0] at hmant hq
    congr 1
    · rw [hmant, hM]
    · rw [hq, h0]; simp only [hbias]; decide
  · have h0 : ¬ unpackExponent (spec := spec64) b.toBitVec = 0#_ := by rw [BitVec.toNat_eq, hE]; simpa using hE0
    rw [ite_eq_right h0]
    rw [ite_eq_right hE0] at hmant hq
    congr 1
    · rw [hmant, BitVec.toNat_append_eq_mul_add, hM]; simp; omega
    · rw [hq, hbias, hE]

/-! ### Packing -/

theorem away_sb (up : Bool) (s : Sign) : away up (sb s) = awayFromZero up s := by
  cases s <;> cases up <;> rfl

theorem toNat_packBits_nan : (packBits .notANumber).toNat = qNaN := by decide

theorem toNat_packBits_inf (s : Sign) : (packBits (.infinity s)).toNat = infOf (sb s) := by
  cases s <;> decide

theorem toNat_packBits_zero (s : Sign) : (packBits (.zero s)).toNat = zeroOf (sb s) := by
  cases s <;> decide

theorem toNat_packBits_maxFinite (s : Sign) :
    (packBits (maxFinite s)).toNat = sb s * signBit + maxBits := by
  cases s <;> decide

theorem toNat_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    (UInt64.ofBitVec (packComponents spec64 s e m)).toNat = sb s * 2 ^ 63 + e.toNat * 2 ^ 52 + m.toNat := by
  unfold packComponents
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_append_eq_mul_add, BitVec.toNat_append_eq_mul_add]
  have : s.toBitVec.toNat = sb s := by cases s <;> rfl
  rw [this]
  simp only [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]

theorem log2_eq_52_iff {m : Nat} (h : m ≠ 0) : m.log2 + 1 = 53 ↔ 2 ^ 52 ≤ m ∧ m < 2 ^ 53 := by
  rw [show (m.log2 + 1 = 53) ↔ m.log2 = 52 by omega, Nat.log2_eq_iff h]

theorem toNat_packDirected_finite (up : Bool) (s : Sign) (Mf Ef : Nat) (h : 0 < Mf) :
    (packDirected up (.finite s Mf ((Ef : Int) - 4096) h)).toNat = packF (sb s) Mf Ef up := by
  have hb : ((Ef : Int) - 4096 + (spec64.exponentBias : Int) + (spec64.mantissaBitsWithoutImplicit : Int)).toNat
      = Ef - 3021 := by
    show ((Ef : Int) - 4096 + (1023 : Nat) + (52 : Nat)).toNat = Ef - 3021
    omega
  unfold packDirected packF
  simp only [ifB_eq, ble_true, Bool.and_eq_true, blt_true, raw_sub, raw_add, raw_mul, raw_mod,
    two52_eq, two53_eq, signBit_eq, away_sb]
  simp only [hb]
  by_cases hov : 2047 ≤ Ef - 3021
  · rw [ite_eq_left (show 2 ^ spec64.exponentBits ≤ Ef - 3021 + 1 by
        show 2 ^ 11 ≤ Ef - 3021 + 1; omega), ite_eq_left hov]
    split
    · rw [toNat_packBits_inf]
    · rw [toNat_packBits_maxFinite, signBit_eq]
  · rw [ite_eq_right (show ¬ 2 ^ spec64.exponentBits ≤ Ef - 3021 + 1 by
        show ¬ 2 ^ 11 ≤ Ef - 3021 + 1; omega), ite_eq_right hov]
    unfold packBits UnpackedFloat.pack
    simp only [hb]
    rw [ite_eq_right (show ¬ 2 ^ spec64.exponentBits ≤ Ef - 3021 + 1 by
        show ¬ 2 ^ 11 ≤ Ef - 3021 + 1; omega)]
    have hiff : Mf.log2 + 1 = spec64.mantissaBits ↔ 2 ^ 52 ≤ Mf ∧ Mf < 2 ^ 53 :=
      log2_eq_52_iff (Nat.pos_iff_ne_zero.1 h)
    by_cases hn : 2 ^ 52 ≤ Mf ∧ Mf < 2 ^ 53
    · rw [ite_eq_left (hiff.2 hn), ite_eq_left hn, toNat_packComponents]
      simp only [BitVec.toNat_ofNat]
    · rw [ite_eq_right (fun h' => hn (hiff.1 h')), ite_eq_right hn, toNat_packComponents]
      simp only [BitVec.toNat_ofNat]
      show sb s * 2 ^ 63 + 0 * 2 ^ 52 + Mf % 2 ^ 52 = sb s * 2 ^ 63 + Mf % 2 ^ 52
      omega

/-! ### Rounding -/

open Interval64Proofs.Round in
theorem em_shift_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero => rw [shiftRight_zero]; simp
  | succ k ih =>
    rw [shiftRight_succ, shiftRightOne_mantissa, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

open Interval64Proofs.Round in
theorem em_shift_exact (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).accuracy = .exact ↔ em.accuracy = .exact ∧ em.mantissa % 2 ^ k = 0 := by
  induction k with
  | zero => rw [shiftRight_zero]; simp [Nat.mod_one]
  | succ k ih =>
    rw [shiftRight_succ, shiftRightOne_accuracy_exact, ih, em_shift_mantissa, mod_two_pow_succ,
      Nat.shiftRight_eq_div_pow, and_assoc]

/-- `true` for an inexact accuracy. -/
def inexB : Accuracy → Bool
  | .exact => false
  | .inexact _ => true

@[simp] theorem inexB_inexact (o : Ordering) : inexB (.inexact o) = true := rfl
@[simp] theorem inexB_exact : inexB .exact = false := rfl

theorem ofMA_mantissa (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  rcases acc with _ | o
  · rfl
  · cases o <;> rfl

theorem ofMA_exact (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).accuracy = .exact ↔ inexB acc = false := by
  rcases acc with _ | o
  · simp [inexB]
  · cases o <;> simp [inexB, ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy]

theorem roundMantissaDirected_eq (M : Nat) (up : Bool) (s : Sign) (a : Accuracy) :
    roundMantissaDirected M up s a =
      if (inexB a && awayFromZero up s) = true then M + 1 else M := by
  rcases a with _ | o
  · simp [roundMantissaDirected, inexB]
  · simp [roundMantissaDirected, inexB]

theorem tgt_int (m E : Nat) :
    ((tgt m E : Nat) : Int) = spec64.targetExponent (totalExponent m ((E : Int) - 4096)) + 4096 := by
  unfold tgt maxN
  simp only [ifB_eq, ble_true, raw_sub, raw_add, lg_eq]
  unfold Format.targetExponent totalExponent
  show _ = max ((m.log2 : Int) + 1 + ((E : Int) - 4096) - (53 : Nat)) (-1074) + 4096
  split <;> omega

theorem inexB_ofMA (m : Nat) (acc : Accuracy) :
    inexB (ExtendedMantissa.ofMantissaAndAccuracy m acc).accuracy = inexB acc := by
  rcases acc with _ | o
  · rfl
  · cases o <;> rfl

theorem inexB_eq_false (a : Accuracy) : inexB a = false ↔ a = .exact := by
  cases a <;> simp [inexB]

theorem inexB_shift (em : ExtendedMantissa) (k : Nat) :
    inexB (em >>> k).accuracy = (inexB em.accuracy || em.mantissa % 2 ^ k != 0) := by
  cases h1 : inexB (em >>> k).accuracy
  · rw [inexB_eq_false, em_shift_exact] at h1
    rw [(inexB_eq_false _).2 h1.1]; simp [h1.2]
  · have hne : ¬ ((em >>> k).accuracy = .exact) := by
      rw [← inexB_eq_false]; simp [h1]
    rw [em_shift_exact] at hne
    by_cases h2 : inexB em.accuracy = true
    · simp [h2]
    · have h2' : em.accuracy = .exact := by
        rw [← inexB_eq_false]; simpa using h2
      have h3 : em.mantissa % 2 ^ k ≠ 0 := fun h => hne ⟨h2', h⟩
      simp [h2', h3, inexB]

theorem shiftTT (M E0 T : Nat) (acc : Accuracy)
    (hT : spec64.targetExponent (totalExponent M ((E0 : Int) - 4096)) = (T : Int) - 4096) :
    shiftToTargetExponent spec64 M ((E0 : Int) - 4096) acc =
      (ExtendedMantissa.ofMantissaAndAccuracy M acc >>> (T - E0),
        (((E0 + (T - E0) : Nat) : Int) - 4096)) := by
  unfold shiftToTargetExponent shiftToExponent
  dsimp only
  rw [hT]
  have : ((T : Int) - 4096 - ((E0 : Int) - 4096)).toNat = T - E0 := by omega
  rw [this]
  congr 1
  omega

theorem tgt_eq (M E : Nat) :
    spec64.targetExponent (totalExponent M ((E : Int) - 4096)) = (tgt M E : Int) - 4096 := by
  rw [tgt_int]; omega

theorem stage1 (m E : Nat) (acc : Accuracy) :
    (match acc with
      | .exact =>
        decreaseExponent m ((E : Int) - 4096)
          (spec64.targetExponent (totalExponent m ((E : Int) - 4096)))
      | .inexact _ => (m, ((E : Int) - 4096))) =
      ((if inexB acc then m else m * 2 ^ (E - tgt m E)),
        (((if inexB acc then E else min E (tgt m E) : Nat) : Int) - 4096)) := by
  rcases acc with _ | o
  · simp only [inexB, Bool.false_eq_true, ite_false]
    unfold decreaseExponent
    dsimp only
    rw [tgt_eq, Nat.shiftLeft_eq]
    have : ((E : Int) - 4096 - ((tgt m E : Int) - 4096)).toNat = E - tgt m E := by omega
    rw [this]
    congr 1
    omega
  · rfl

/-- `roundDirected` with a biased natural exponent, exact input, in closed form. -/
theorem roundDirected_char_exact (s : Sign) (m E : Nat) (up : Bool) (hm : 0 < m) :
    roundDirected s m ((E : Int) - 4096) .exact up =
      let T := tgt m E
      let M0 := m * 2 ^ (E - T)
      let E0 := min E T
      let n := T - E0
      let Q := M0 / 2 ^ n
      let R := if ((M0 % 2 ^ n != 0) && awayFromZero up s) = true then Q + 1 else Q
      let E1 := E0 + n
      let n2 := tgt R E1 - E1
      let Mf := R / 2 ^ n2
      if h : Mf = 0 then .zero s else .finite s Mf (((E1 + n2 : Nat) : Int) - 4096)
        (Nat.pos_of_ne_zero h) := by
  have hm0 : m ≠ 0 := by omega
  unfold roundDirected
  dsimp only
  unfold decreaseExponent
  dsimp only
  rw [tgt_eq]
  have hk : ((E : Int) - 4096 - ((tgt m E : Int) - 4096)).toNat = E - tgt m E := by omega
  have he : (E : Int) - 4096 - ((E - tgt m E : Nat) : Int) = ((min E (tgt m E) : Nat) : Int) - 4096 := by
    omega
  simp only [hk, he, Nat.shiftLeft_eq]
  have hT1 : spec64.targetExponent (totalExponent (m * 2 ^ (E - tgt m E))
      (((min E (tgt m E) : Nat) : Int) - 4096)) = (tgt m E : Int) - 4096 := by
    rw [← tgt_eq]
    unfold totalExponent
    rw [Interval64Proofs.RoundDirected.log2_mul_two_pow m _ hm0]
    congr 1
    omega
  simp only [shiftTT _ _ _ _ hT1]
  simp only [roundMantissaDirected_eq, em_shift_mantissa, inexB_shift, ofMA_mantissa, inexB_ofMA]
  simp only [shiftTT _ _ _ _ (tgt_eq _ _)]
  simp only [em_shift_mantissa, ofMA_mantissa, inexB_exact, Bool.false_or]

/-- `roundDirected` with a biased natural exponent, inexact input, in closed form. -/
theorem roundDirected_char_inexact (s : Sign) (m E : Nat) (o : Ordering) (up : Bool) :
    roundDirected s m ((E : Int) - 4096) (.inexact o) up =
      let T := tgt m E
      let n := T - E
      let Q := m / 2 ^ n
      let R := if awayFromZero up s = true then Q + 1 else Q
      let E1 := E + n
      let n2 := tgt R E1 - E1
      let Mf := R / 2 ^ n2
      if h : Mf = 0 then .zero s else .finite s Mf (((E1 + n2 : Nat) : Int) - 4096)
        (Nat.pos_of_ne_zero h) := by
  unfold roundDirected
  dsimp only
  simp only [shiftTT _ _ _ _ (tgt_eq _ _)]
  simp only [roundMantissaDirected_eq, em_shift_mantissa, inexB_shift, ofMA_mantissa, inexB_ofMA,
    inexB_inexact, Bool.true_or, Bool.true_and]

theorem minN_eq (a b : Nat) : minN a b = min a b := by
  unfold minN; simp only [ifB_eq, ble_true, Nat.min_def]

theorem maxN_eq (a b : Nat) : maxN a b = max a b := by
  unfold maxN; simp only [ifB_eq, ble_true, Nat.max_def]

theorem nbeq_true (a b : Nat) : ((!Nat.beq a b) = true) = (a ≠ b) := by
  cases h : Nat.beq a b
  · simp only [Bool.not_false, ne_eq, eq_iff_iff, true_iff]
    exact Nat.ne_of_beq_eq_false h
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem bne_true (a b : Nat) : ((a != b) = true) = (a ≠ b) := by
  simp

theorem away_true (up : Bool) (s : Sign) : (away up (sb s) = true) = (awayFromZero up s = true) := by
  rw [away_sb]

theorem finish_eq (s : Sign) (R E1 : Nat) (up : Bool) :
    finish (sb s) R E1 up =
      let n2 := tgt R E1 - E1
      let Mf := R / 2 ^ n2
      if Mf = 0 then zeroOf (sb s) else packF (sb s) Mf (E1 + n2) up := by
  unfold finish
  simp only [ifB_eq, beq_true, raw_sub, raw_add, raw_shiftRight]

theorem toNat_packDirected_char (up : Bool) (s : Sign) (Mf Ef : Nat) :
    (packDirected up (if h : Mf = 0 then .zero s else
      .finite s Mf ((Ef : Int) - 4096) (Nat.pos_of_ne_zero h))).toNat =
      if Mf = 0 then zeroOf (sb s) else packF (sb s) Mf Ef up := by
  split
  · exact toNat_packBits_zero s
  · exact toNat_packDirected_finite up s Mf Ef _

theorem roundPack_exact (s : Sign) (m E : Nat) (up : Bool) (hm : 0 < m) :
    (packDirected up (roundDirected s m ((E : Int) - 4096) .exact up)).toNat =
      roundPack (sb s) m E false up := by
  rw [roundDirected_char_exact s m E up hm]
  unfold roundPack
  simp only [ifB_eq, raw_sub, raw_add, raw_shiftRight, raw_shiftLeft,
    raw_mod, raw_succ, Nat.one_mul, minN_eq, Bool.false_or, Bool.and_eq_true, nbeq_true,
    bne_true, away_true, finish_eq]
  exact toNat_packDirected_char _ _ _ _

theorem roundPack_inexact (s : Sign) (m E : Nat) (o : Ordering) (up : Bool) :
    (packDirected up (roundDirected s m ((E : Int) - 4096) (.inexact o) up)).toNat =
      roundPack (sb s) m E true up := by
  rw [roundDirected_char_inexact s m E o up]
  unfold roundPack
  simp only [ifB_eq, raw_sub, raw_add, raw_shiftRight, raw_shiftLeft,
    raw_mod, raw_succ, Nat.one_mul, Bool.true_or, Bool.true_and, away_true, finish_eq]
  exact toNat_packDirected_char _ _ _ _

/-! ### Signs -/

theorem sgn_sb {n : Nat} (h : n < 2 ^ 64) : sgn n = sb (sOf n) := by
  rw [sgn_eq]; unfold sOf
  split
  · rename_i h'; rw [h']; rfl
  · show n / 2 ^ 63 = 1; omega

theorem sb_mul (s t : Sign) : sb (s * t) = Nat.xor (sb s) (sb t) := by
  cases s <;> cases t <;> rfl

theorem sb_div (s t : Sign) : sb (s / t) = Nat.xor (sb s) (sb t) := by
  cases s <;> cases t <;> rfl

theorem xs_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : xs a b = sb (sOf a * sOf b) := by
  unfold xs; rw [sgn_sb ha, sgn_sb hb, sb_mul]

theorem packDirected_nan (up : Bool) : (packDirected up .notANumber).toNat = qNaN :=
  toNat_packBits_nan
theorem packDirected_inf (up : Bool) (s : Sign) : (packDirected up (.infinity s)).toNat = infOf (sb s) :=
  toNat_packBits_inf s
theorem packDirected_zero (up : Bool) (s : Sign) : (packDirected up (.zero s)).toNat = zeroOf (sb s) :=
  toNat_packBits_zero s

/-! ### Multiplication -/

theorem mulU_nan_right (x : UnpackedFloat) (up : Bool) : mulU x .notANumber up = .notANumber := by
  cases x <;> rfl

theorem mul_eq (a b : UInt64) (up : Bool) : (Spec.mul a b up).toNat = mul a.toNat b.toNat up := by
  unfold Spec.mul
  rw [unpackBits_eq, unpackBits_eq]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  unfold mul unpackN
  simp only [ifB_eq, Bool.or_eq_true, xs_eq ha hb]
  by_cases hxn : isNaN x = true
  · simp [hxn, mulU, packDirected_nan]
  by_cases hyn : isNaN y = true
  · simp only [hyn, ite_true, mulU_nan_right, packDirected_nan, or_true]
  simp only [hxn, hyn, ite_false, Bool.false_eq_true, or_self]
  by_cases hxi : isInf x = true
  · by_cases hyz : isZero y = true
    · have hyi : ¬ isInf y = true := by
        rw [isInf_iff]; rw [isZero_iff] at hyz; omega
      simp [hxi, hyz, hyi, mulU, packDirected_nan]
    · by_cases hyi : isInf y = true
      · simp [hxi, hyz, hyi, mulU, packDirected_inf]
      · simp [hxi, hyz, hyi, mulU, packDirected_inf]
  by_cases hyi : isInf y = true
  · by_cases hxz : isZero x = true
    · simp [hxi, hxz, hyi, mulU, packDirected_nan]
    · simp [hxi, hxz, hyi, mulU, packDirected_inf]
  by_cases hxz : isZero x = true
  · by_cases hyz : isZero y = true
    · simp [hxi, hxz, hyi, hyz, mulU, packDirected_zero]
    · simp [hxi, hxz, hyi, hyz, mulU, packDirected_zero]
  by_cases hyz : isZero y = true
  · simp [hxi, hxz, hyi, hyz, mulU, packDirected_zero]
  simp only [hxi, hxz, hyi, hyz, ite_false, Bool.false_eq_true, or_self, dite_false]
  unfold mulU mulFin
  simp only [raw_add, raw_mul, xs_eq ha hb]
  have he : ((qexp x : Int) - 1075) + ((qexp y : Int) - 1075) =
      (((qexp x + qexp y + 1946 : Nat)) : Int) - 4096 := by omega
  rw [he]
  exact roundPack_exact _ _ _ _ (Nat.mul_pos (mant_pos hxz) (mant_pos hyz))

/-! ### Re-packing an unpacked finite value -/

/-- A finite nonzero pattern is not NaN / Inf / zero. -/
structure IsFin (n : Nat) : Prop where
  lt : n < 2 ^ 64
  nan : ¬ isNaN n = true
  inf : ¬ isInf n = true
  zero : ¬ isZero n = true

theorem IsFin.ex_lt {n : Nat} (h : IsFin n) : n / 2 ^ 52 % 2048 < 2047 := by
  have h1 := h.nan; have h2 := h.inf
  rw [isNaN_iff] at h1; rw [isInf_iff] at h2
  have : n / 2 ^ 52 % 2048 < 2048 := Nat.mod_lt _ (by decide)
  by_cases hf : n % 2 ^ 52 = 0 <;> omega

theorem IsFin.qexp_le {n : Nat} (h : IsFin n) : qexp n ≤ 2046 := by
  have := h.ex_lt; rw [qexp_eq]; split <;> omega

theorem mant_lt (n : Nat) : mant n < 2 ^ 53 := by
  have : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [mant_eq]; split <;> omega

theorem packDirected_unpackN {n : Nat} (h : IsFin n) (up : Bool) :
    (packDirected up (.finite (sOf n) (mant n) ((qexp n : Int) - 1075) (mant_pos h.zero))).toNat = n := by
  have he : (qexp n : Int) - 1075 = ((qexp n + 3021 : Nat) : Int) - 4096 := by omega
  simp only [he]
  rw [toNat_packDirected_finite]
  unfold packF
  have hex := h.ex_lt
  have hsplit := n_split n
  have hlt := h.lt
  have hsb : sb (sOf n) = n / 2 ^ 63 := by rw [← sgn_sb hlt, sgn_eq]
  have hF : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  simp only [ifB_eq, ble_true, Bool.and_eq_true, blt_true, raw_sub, raw_add, raw_mul, raw_mod,
    two52_eq, two53_eq, signBit_eq, hsb]
  have hq : qexp n + 3021 - 3021 = qexp n := by omega
  rw [hq]
  have hqle := h.qexp_le
  rw [ite_eq_right (by omega)]
  rw [mant_eq, qexp_eq] at *
  by_cases hE : n / 2 ^ 52 % 2048 = 0
  · simp only [hE, ite_true]
    rw [ite_eq_right (by omega)]
    rw [Nat.mod_eq_of_lt hF]
    omega
  · simp only [hE, ite_false]
    rw [ite_eq_left (by omega)]
    rw [Nat.mod_eq_of_lt (show n / 2 ^ 52 % 2048 < 2048 by omega),
      show (n % 2 ^ 52 + 2 ^ 52) % 2 ^ 52 = n % 2 ^ 52 by omega]
    omega

/-! ### Addition -/

theorem addU_nan_right (x : UnpackedFloat) (up : Bool) : addU x .notANumber up = .notANumber := by
  cases x <;> rfl

theorem cancelSign_eq (up : Bool) : cancelSign up = sb (cancelZero up) := by
  cases up <;> rfl

theorem sOf_eq_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    sOf x = sOf y ↔ sgn x = sgn y := by
  rw [sgn_sb hx, sgn_sb hy]
  cases sOf x <;> cases sOf y <;> simp [sb]

/-- The finite-finite case of `addU`. -/
theorem addFin_eq {x y : Nat} (hx : IsFin x) (hy : IsFin y) (up : Bool) :
    (packDirected up (addU (.finite (sOf x) (mant x) ((qexp x : Int) - 1075) (mant_pos hx.zero))
      (.finite (sOf y) (mant y) ((qexp y : Int) - 1075) (mant_pos hy.zero)) up)).toNat =
      addFin x y up := by
  unfold addU normalizeDirected decreaseExponent addFin
  dsimp only
  simp only [ifB_eq, beq_true, blt_true, raw_sub, raw_add, raw_shiftLeft, minN_eq,
    sgn_sb hx.lt, sgn_sb hy.lt, cancelSign_eq]
  have hmin : min ((qexp x : Int) - 1075) ((qexp y : Int) - 1075) =
      ((min (qexp x) (qexp y) + 3021 : Nat) : Int) - 4096 := by omega
  have hkx : ((qexp x : Int) - 1075 - (((min (qexp x) (qexp y) + 3021 : Nat) : Int) - 4096)).toNat
      = qexp x - min (qexp x) (qexp y) := by omega
  have hky : ((qexp y : Int) - 1075 - (((min (qexp x) (qexp y) + 3021 : Nat) : Int) - 4096)).toNat
      = qexp y - min (qexp x) (qexp y) := by omega
  rw [hmin, hkx, hky, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hA : 0 < mant x * 2 ^ (qexp x - min (qexp x) (qexp y)) :=
    Nat.mul_pos (mant_pos hx.zero) (Nat.two_pow_pos _)
  have hB : 0 < mant y * 2 ^ (qexp y - min (qexp x) (qexp y)) :=
    Nat.mul_pos (mant_pos hy.zero) (Nat.two_pow_pos _)
  generalize mant x * 2 ^ (qexp x - min (qexp x) (qexp y)) = A at hA ⊢
  generalize mant y * 2 ^ (qexp y - min (qexp x) (qexp y)) = B at hB ⊢
  generalize min (qexp x) (qexp y) + 3021 = E
  have hpos : ∀ (s : Sign) (m : Nat), 0 < m →
      (packDirected up (roundDirected s m ((E : Int) - 4096) .exact up)).toNat =
        roundPack (sb s) m E false up := fun s m hm => roundPack_exact s m E up hm
  have sbn : sb .negative = 1 := rfl
  have sbp : sb .positive = 0 := rfl
  cases sOf x <;> cases sOf y <;> simp only [Sign.apply, sbn, sbp, ite_true, Nat.one_ne_zero,
    Nat.zero_ne_one, ite_false]
  · rw [Int.compare_eq_lt.mpr (by omega)]
    dsimp only
    rw [show (-(-(A : Int) + -(B : Int))).toNat = A + B by omega, hpos _ _ (by omega)]; rfl
  · rcases Nat.lt_trichotomy A B with h | h | h
    · rw [Int.compare_eq_gt.mpr (by omega), ite_eq_right (by omega), ite_eq_left h]
      dsimp only
      rw [show (-(A : Int) + (B : Int)).toNat = B - A by omega, hpos _ _ (by omega)]; rfl
    · subst h
      rw [Int.compare_eq_eq.mpr (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact packDirected_zero up _
    · rw [Int.compare_eq_lt.mpr (by omega), ite_eq_left h]
      dsimp only
      rw [show (-(-(A : Int) + (B : Int))).toNat = A - B by omega, hpos _ _ (by omega)]; rfl
  · rcases Nat.lt_trichotomy A B with h | h | h
    · rw [Int.compare_eq_lt.mpr (by omega), ite_eq_right (by omega), ite_eq_left h]
      dsimp only
      rw [show (-((A : Int) + -(B : Int))).toNat = B - A by omega, hpos _ _ (by omega)]; rfl
    · subst h
      rw [Int.compare_eq_eq.mpr (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact packDirected_zero up _
    · rw [Int.compare_eq_gt.mpr (by omega), ite_eq_left h]
      dsimp only
      rw [show ((A : Int) + -(B : Int)).toNat = A - B by omega, hpos _ _ (by omega)]; rfl
  · rw [Int.compare_eq_gt.mpr (by omega)]
    dsimp only
    rw [show ((A : Int) + (B : Int)).toNat = A + B by omega, hpos _ _ (by omega)]; rfl

theorem sb_inj {s t : Sign} : sb s = sb t ↔ s = t := by
  cases s <;> cases t <;> simp [sb]

theorem add_eq (a b : UInt64) (up : Bool) : (Spec.add a b up).toNat = add a.toNat b.toNat up := by
  unfold Spec.add
  rw [unpackBits_eq, unpackBits_eq]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  unfold add unpackN
  simp only [ifB_eq, Bool.or_eq_true, Bool.and_eq_true, nbeq_true, beq_true, sgn_sb ha, sgn_sb hb]
  by_cases hxn : isNaN x = true
  · simp [hxn, addU, packDirected_nan]
  by_cases hyn : isNaN y = true
  · simp only [hyn, ite_true, addU_nan_right, packDirected_nan, or_true]
  simp only [hxn, hyn, ite_false, Bool.false_eq_true, or_self]
  by_cases hs : sOf x = sOf y
  · have hs' : sb (sOf x) = sb (sOf y) := by rw [hs]
    by_cases hxi : isInf x = true
    · by_cases hyi : isInf y = true
      · simp [hxi, hyi, hs, addU, packDirected_inf]
      · by_cases hyz : isZero y = true
        · simp [hxi, hyi, hyz, addU, packDirected_inf]
        · simp [hxi, hyi, hyz, addU, packDirected_inf]
    by_cases hyi : isInf y = true
    · by_cases hxz : isZero x = true
      · simp [hxi, hxz, hyi, addU, packDirected_inf]
      · simp [hxi, hxz, hyi, addU, packDirected_inf]
    by_cases hxz : isZero x = true
    · by_cases hyz : isZero y = true
      · simp [hxi, hxz, hyi, hyz, hs, addU, packDirected_zero]
      · simp only [hxi, hxz, hyi, hyz, ite_true, ite_false, dite_true, dite_false,
          Bool.false_eq_true, addU]
        exact packDirected_unpackN ⟨hb, hyn, hyi, hyz⟩ up
    by_cases hyz : isZero y = true
    · simp only [hxi, hxz, hyi, hyz, ite_true, ite_false, dite_true, dite_false, Bool.false_eq_true,
        addU]
      exact packDirected_unpackN ⟨ha, hxn, hxi, hxz⟩ up
    simp only [hxi, hxz, hyi, hyz, ite_false, dite_false, Bool.false_eq_true]
    exact addFin_eq ⟨ha, hxn, hxi, hxz⟩ ⟨hb, hyn, hyi, hyz⟩ up
  · have hs' : sb (sOf x) ≠ sb (sOf y) := fun h => hs (sb_inj.1 h)
    by_cases hxi : isInf x = true
    · by_cases hyi : isInf y = true
      · simp [hxi, hyi, hs, hs', addU, packDirected_nan]
      · by_cases hyz : isZero y = true
        · simp [hxi, hyi, hyz, addU, packDirected_inf]
        · simp [hxi, hyi, hyz, addU, packDirected_inf]
    by_cases hyi : isInf y = true
    · by_cases hxz : isZero x = true
      · simp [hxi, hxz, hyi, addU, packDirected_inf]
      · simp [hxi, hxz, hyi, addU, packDirected_inf]
    by_cases hxz : isZero x = true
    · by_cases hyz : isZero y = true
      · simp [hxi, hxz, hyi, hyz, hs, hs', addU, packDirected_zero, cancelSign_eq]
      · simp only [hxi, hxz, hyi, hyz, ite_true, ite_false, dite_true, dite_false,
          Bool.false_eq_true, addU]
        exact packDirected_unpackN ⟨hb, hyn, hyi, hyz⟩ up
    by_cases hyz : isZero y = true
    · simp only [hxi, hxz, hyi, hyz, ite_true, ite_false, dite_true, dite_false, Bool.false_eq_true,
        addU]
      exact packDirected_unpackN ⟨ha, hxn, hxi, hxz⟩ up
    simp only [hxi, hxz, hyi, hyz, ite_false, dite_false, Bool.false_eq_true]
    exact addFin_eq ⟨ha, hxn, hxi, hxz⟩ ⟨hb, hyn, hyi, hyz⟩ up

/-! ### Negation and subtraction -/

theorem negBits_fields {n : Nat} (h : n < 2 ^ 64) :
    negBits n < 2 ^ 64 ∧ negBits n / 2 ^ 52 % 2048 = n / 2 ^ 52 % 2048 ∧
      negBits n % 2 ^ 52 = n % 2 ^ 52 ∧ negBits n / 2 ^ 63 = 1 - n / 2 ^ 63 := by
  unfold negBits
  rw [raw_xor, signBit_eq]
  have hm : (n ^^^ 2 ^ 63) % 2 ^ 63 = n % 2 ^ 63 := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have hd : (n ^^^ 2 ^ 63) / 2 ^ 63 = 1 - n / 2 ^ 63 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (Nat.two_pow_pos _)]
    have : n / 2 ^ 63 < 2 := by omega
    rcases (show n / 2 ^ 63 = 0 ∨ n / 2 ^ 63 = 1 by omega) with h | h <;> rw [h] <;> rfl
  have s1 := magB_split n
  have s2 := magB_split (n ^^^ 2 ^ 63)
  have l1 : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have l2 : (n ^^^ 2 ^ 63) % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hF : (n ^^^ 2 ^ 63) % 2 ^ 52 = n % 2 ^ 52 := by
    rw [Nat.xor_mod_two_pow, show (2 : Nat) ^ 63 % 2 ^ 52 = 0 by decide, Nat.xor_zero]
  refine ⟨Nat.xor_lt_two_pow h (by decide), ?_, hF, hd⟩
  rw [hm, hF] at s2
  have : (n ^^^ 2 ^ 63) / 2 ^ 52 % 2048 * 2 ^ 52 = n / 2 ^ 52 % 2048 * 2 ^ 52 := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 52) this

theorem bool_congr_iff {a b : Bool} {P Q : Prop} (ha : a = true ↔ P) (hb : b = true ↔ Q)
    (h : P ↔ Q) : a = b := by
  cases a <;> cases b <;> simp_all

theorem unpackN_neg {n : Nat} (h : n < 2 ^ 64) : unpackN (negBits n) = (unpackN n).neg := by
  obtain ⟨-, hE, hF, hS⟩ := negBits_fields h
  have e1 : isNaN (negBits n) = isNaN n :=
    bool_congr_iff (isNaN_iff _) (isNaN_iff _) (by rw [hE, hF])
  have e2 : isInf (negBits n) = isInf n :=
    bool_congr_iff (isInf_iff _) (isInf_iff _) (by rw [hE, hF])
  have e3 : isZero (negBits n) = isZero n :=
    bool_congr_iff (isZero_iff _) (isZero_iff _) (by rw [hE, hF])
  have e4 : mant (negBits n) = mant n := by rw [mant_eq, mant_eq, hE, hF]
  have e5 : qexp (negBits n) = qexp n := by rw [qexp_eq, qexp_eq, hE]
  have e6 : sOf (negBits n) = -sOf n := by
    unfold sOf; rw [hS]
    by_cases h0 : n / 2 ^ 63 = 0
    · rw [h0]; rfl
    · rw [ite_eq_left (by omega), ite_eq_right h0]; rfl
  unfold unpackN
  simp only [e1, e2, e3, e6]
  by_cases hn : isNaN n = true
  · simp [hn, UnpackedFloat.neg]
  by_cases hi : isInf n = true
  · simp [hn, hi, UnpackedFloat.neg]
  by_cases hz : isZero n = true
  · simp [hn, hi, hz, UnpackedFloat.neg]
  simp only [hn, hi, hz, ite_false, dite_false, Bool.false_eq_true, UnpackedFloat.neg]
  congr 1 <;> simp [e5]

theorem sub_eq (a b : UInt64) (up : Bool) : (Spec.sub a b up).toNat = sub a.toNat b.toNat up := by
  have hb := b.toNat_lt
  obtain ⟨hlt, -⟩ := negBits_fields hb
  have := add_eq a (UInt64.ofNat (negBits b.toNat)) up
  rw [UInt64.toNat_ofNat_of_lt' hlt] at this
  unfold sub; rw [← this]
  unfold Spec.sub Spec.add
  rw [unpackBits_eq b, unpackBits_eq (UInt64.ofNat _), UInt64.toNat_ofNat_of_lt' hlt, unpackN_neg hb]

/-! ### Division -/

theorem log2_mant_le (n : Nat) : (mant n).log2 ≤ 52 := by
  have := mant_lt n
  by_cases h : mant n = 0
  · rw [h]; simp
  · have := Nat.lt_log2_self (n := mant n)
    exact Nat.le_of_lt_succ ((Nat.log2_lt h).2 (mant_lt n))

theorem divFin_eq {x y : Nat} (hx : IsFin x) (hy : IsFin y) (up : Bool) :
    (packDirected up (divU (.finite (sOf x) (mant x) ((qexp x : Int) - 1075) (mant_pos hx.zero))
      (.finite (sOf y) (mant y) ((qexp y : Int) - 1075) (mant_pos hy.zero)) up)).toNat =
      divFin x y up := by
  unfold divU divCore divFin
  dsimp only
  simp only [raw_sub, raw_add, raw_shiftLeft, raw_div, raw_mod, lg_eq, minN_eq, maxN_eq]
  have hxs : xs x y = sb (sOf x / sOf y) := by
    unfold xs; rw [sgn_sb hx.lt, sgn_sb hy.lt, sb_div]
  rw [hxs]
  have l1 := log2_mant_le y
  have l2 := hy.qexp_le
  have hTE : min ((qexp x : Int) - 1075 - ((qexp y : Int) - 1075))
      (spec64.targetExponent (totalExponent (mant x) ((qexp x : Int) - 1075) -
        totalExponent (mant y) ((qexp y : Int) - 1075))) =
      ((min (qexp x + 4096 - qexp y) (max ((mant x).log2 + qexp x + 4096 - ((mant y).log2 + qexp y) - 53) 3022)
        : Nat) : Int) - 4096 := by
    unfold Format.targetExponent totalExponent
    show min _ (max (_ - ((53 : Nat) : Int)) (-1074 : Int)) = _
    omega
  rw [hTE]
  generalize hT : min (qexp x + 4096 - qexp y)
    (max ((mant x).log2 + qexp x + 4096 - ((mant y).log2 + qexp y) - 53) 3022) = T at *
  have hTd : T ≤ qexp x + 4096 - qexp y := by rw [← hT]; exact Nat.min_le_left _ _
  have hsh : ((qexp x : Int) - 1075 - ((qexp y : Int) - 1075) - ((T : Int) - 4096)).toNat =
      qexp x + 4096 - qexp y - T := by omega
  rw [hsh, Nat.shiftLeft_eq]
  have hM : 0 < mant x * 2 ^ (qexp x + 4096 - qexp y - T) :=
    Nat.mul_pos (mant_pos hx.zero) (Nat.two_pow_pos _)
  generalize mant x * 2 ^ (qexp x + 4096 - qexp y - T) = M at *
  have hmy := mant_pos hy.zero
  unfold accuracyOfFraction
  by_cases hr : M % mant y = 0
  · rw [ite_eq_left hr, hr]
    have hq : 0 < M / mant y := by
      have := Nat.div_add_mod M (mant y)
      rcases Nat.eq_zero_or_pos (M / mant y) with h | h
      · rw [h, hr] at this; omega
      · exact h
    exact roundPack_exact _ _ _ up hq
  · rw [ite_eq_right hr]
    have : (!(M % mant y).beq 0) = true := by
      cases h : (M % mant y).beq 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hr
    rw [this]
    exact roundPack_inexact _ _ _ _ up

theorem divU_nan_right (x : UnpackedFloat) (up : Bool) : divU x .notANumber up = .notANumber := by
  cases x <;> rfl

theorem xs_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : xs a b = sb (sOf a / sOf b) := by
  unfold xs; rw [sgn_sb ha, sgn_sb hb, sb_div]

theorem div_eq (a b : UInt64) (up : Bool) : (Spec.div a b up).toNat = div a.toNat b.toNat up := by
  unfold Spec.div
  rw [unpackBits_eq, unpackBits_eq]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  unfold div unpackN
  simp only [ifB_eq, Bool.or_eq_true, xs_div ha hb]
  by_cases hxn : isNaN x = true
  · simp [hxn, divU, packDirected_nan]
  by_cases hyn : isNaN y = true
  · simp only [hyn, ite_true, divU_nan_right, packDirected_nan, or_true]
  simp only [hxn, hyn, ite_false, Bool.false_eq_true, or_self]
  by_cases hxi : isInf x = true
  · by_cases hyi : isInf y = true
    · simp [hxi, hyi, divU, packDirected_nan]
    · by_cases hyz : isZero y = true
      · simp [hxi, hyz, hyi, divU, packDirected_inf]
      · simp [hxi, hyz, hyi, divU, packDirected_inf]
  by_cases hyi : isInf y = true
  · by_cases hxz : isZero x = true
    · simp [hxi, hxz, hyi, divU, packDirected_zero]
    · simp [hxi, hxz, hyi, divU, packDirected_zero]
  by_cases hyz : isZero y = true
  · by_cases hxz : isZero x = true
    · simp [hxi, hxz, hyi, hyz, divU, packDirected_nan]
    · simp [hxi, hxz, hyi, hyz, divU, packDirected_inf]
  by_cases hxz : isZero x = true
  · simp [hxi, hxz, hyi, hyz, divU, packDirected_zero]
  simp only [hxi, hxz, hyi, hyz, ite_false, Bool.false_eq_true, dite_false]
  exact divFin_eq ⟨ha, hxn, hxi, hxz⟩ ⟨hb, hyn, hyi, hyz⟩ up

/-! ### Square root -/

theorem sqrtFin_eq {x : Nat} (hx : IsFin x) (up : Bool) :
    (packDirected up (sqrtU (.finite .positive (mant x) ((qexp x : Int) - 1075) (mant_pos hx.zero))
      up)).toNat = sqrtFin x up := by
  unfold sqrtU sqrtCore sqrtFin
  dsimp only
  simp only [raw_sub, raw_add, raw_mul, raw_shiftLeft, raw_div, lg_eq, isqrt_eq, minN_eq, maxN_eq]
  have l2 := hx.qexp_le
  have l1 := log2_mant_le x
  have hTE : min (((qexp x : Int) - 1075).ediv 2)
      (spec64.targetExponent ((totalExponent (mant x) ((qexp x : Int) - 1075) + 1).ediv 2)) =
      ((min ((qexp x + 1125) / 2 + 2996) (max (((mant x).log2 + qexp x + 1127) / 2 + 2943) 3022)
        : Nat) : Int) - 4096 := by
    unfold Format.targetExponent totalExponent
    show min ((((qexp x : Int) - 1075)) / 2)
      (max ((((mant x).log2 : Int) + 1 + ((qexp x : Int) - 1075) + 1) / 2 - ((53 : Nat) : Int))
        (-1074 : Int)) = _
    omega
  rw [hTE]
  generalize hT : min ((qexp x + 1125) / 2 + 2996)
    (max (((mant x).log2 + qexp x + 1127) / 2 + 2943) 3022) = T at *
  have hTd : T ≤ (qexp x + 1125) / 2 + 2996 := by rw [← hT]; exact Nat.min_le_left _ _
  have hsh : ((qexp x : Int) - 1075 - 2 * ((T : Int) - 4096)).toNat = qexp x + 7117 - 2 * T := by
    omega
  rw [hsh, Nat.shiftLeft_eq]
  have hM : 0 < mant x * 2 ^ (qexp x + 7117 - 2 * T) :=
    Nat.mul_pos (mant_pos hx.zero) (Nat.two_pow_pos _)
  generalize mant x * 2 ^ (qexp x + 7117 - 2 * T) = M at *
  have hsq := Nat.lt_succ_sqrt M
  have hle := Nat.sqrt_le M
  by_cases hr : M - M.sqrt * M.sqrt = 0
  · rw [ite_eq_left hr, hr]
    have hq : 0 < M.sqrt := by
      rcases Nat.eq_zero_or_pos M.sqrt with h | h
      · rw [h] at hsq; simp at hsq; omega
      · exact h
    exact roundPack_exact .positive _ _ up hq
  · rw [ite_eq_right hr]
    have : (!(M - M.sqrt * M.sqrt).beq 0) = true := by
      cases h : (M - M.sqrt * M.sqrt).beq 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hr
    rw [this]
    exact roundPack_inexact .positive _ _ _ up

theorem zero_bits {n : Nat} (h : n < 2 ^ 64) (hz : isZero n = true) : zeroOf (sb (sOf n)) = n := by
  rw [isZero_iff] at hz
  have := n_split n
  rw [← sgn_sb h, sgn_eq]
  unfold zeroOf; rw [raw_mul, signBit_eq]
  omega

theorem sqrt_eq (a : UInt64) (up : Bool) : (Spec.sqrt a up).toNat = sqrt a.toNat up := by
  unfold Spec.sqrt
  rw [unpackBits_eq]
  have ha := a.toNat_lt
  generalize a.toNat = x at *
  unfold sqrt unpackN
  simp only [ifB_eq, beq_true, sgn_sb ha]
  by_cases hxn : isNaN x = true
  · simp [hxn, sqrtU, packDirected_nan]
  simp only [hxn, ite_false, Bool.false_eq_true]
  by_cases hxi : isInf x = true
  · cases hs : sOf x
    · simp [hxi, sqrtU, packDirected_nan, sb]
    · simp [hxi, sqrtU, packDirected_inf, sb]; rfl
  by_cases hxz : isZero x = true
  · simp only [hxi, hxz, ite_true, ite_false, dite_true, Bool.false_eq_true, sqrtU,
      packDirected_zero]
    exact zero_bits ha hxz
  simp only [hxi, hxz, ite_false, dite_false, Bool.false_eq_true]
  cases hs : sOf x
  · simp [sqrtU, packDirected_nan, sb]
  · simp only [sb, Nat.zero_ne_one, ite_false]
    exact sqrtFin_eq ⟨ha, hxn, hxi, hxz⟩ up

/-! ### Comparisons -/

/-- KF comparison codes: 0 = lt, 1 = eq, 2 = gt, 3 = unordered. -/
def codeOf : Option Ordering → Nat
  | none => 3
  | some .lt => 0
  | some .eq => 1
  | some .gt => 2

theorem codeOf_swap (o : Ordering) : codeOf (some o.swap) = 2 - codeOf (some o) := by
  cases o <;> rfl

theorem cmpMag_eq (x y : Nat) :
    cmpMag x y = codeOf (some ((compare ((qexp x : Int) - 1075) ((qexp y : Int) - 1075)).then
      (compare (mant x) (mant y)))) := by
  unfold cmpMag
  simp only [ifB_eq, blt_true]
  rcases Nat.lt_trichotomy (qexp x) (qexp y) with h | h | h
  · rw [Int.compare_eq_lt.mpr (by omega), ite_eq_left h]; rfl
  · rw [h, Int.compare_eq_eq.mpr rfl, ite_eq_right (Nat.lt_irrefl _), ite_eq_right (Nat.lt_irrefl _)]
    rcases Nat.lt_trichotomy (mant x) (mant y) with h' | h' | h'
    · rw [Nat.compare_eq_lt.mpr h', ite_eq_left h']; rfl
    · rw [h', Nat.compare_eq_eq.mpr rfl, ite_eq_right (Nat.lt_irrefl _),
        ite_eq_right (Nat.lt_irrefl _)]; rfl
    · rw [Nat.compare_eq_gt.mpr h', ite_eq_right (by omega), ite_eq_left h']; rfl
  · rw [Int.compare_eq_gt.mpr (by omega), ite_eq_right (by omega), ite_eq_left h]; rfl

theorem compare_nan_right (u : UnpackedFloat) : u.compare .notANumber = none := by
  cases u <;> rfl

theorem cmp_eq (a b : UInt64) :
    cmp a.toNat b.toNat = codeOf ((unpackBits a).compare (unpackBits b)) := by
  rw [unpackBits_eq, unpackBits_eq]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  unfold cmp unpackN
  simp only [ifB_eq, Bool.or_eq_true, beq_true, sgn_sb ha, sgn_sb hb]
  by_cases hxn : isNaN x = true
  · simp [hxn, UnpackedFloat.compare, codeOf]
  by_cases hyn : isNaN y = true
  · simp only [hyn, or_true, ite_true, compare_nan_right]; rfl
  simp only [hxn, hyn, ite_false, Bool.false_eq_true, or_self]
  have hx := (fun h1 h2 => (⟨ha, hxn, h1, h2⟩ : IsFin x))
  have hy := (fun h1 h2 => (⟨hb, hyn, h1, h2⟩ : IsFin y))
  by_cases hxi : isInf x = true
  · by_cases hyi : isInf y = true
    · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, UnpackedFloat.compare, codeOf, sb] <;> rfl
    · by_cases hyz : isZero y = true
      · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hyz, UnpackedFloat.compare, codeOf, sb]
      · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hyz, UnpackedFloat.compare, codeOf, sb]
  by_cases hyi : isInf y = true
  · by_cases hxz : isZero x = true
    · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hxz, UnpackedFloat.compare, codeOf, sb]
    · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hxz, UnpackedFloat.compare, codeOf, sb]
  by_cases hxz : isZero x = true
  · by_cases hyz : isZero y = true
    · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hxz, hyz, UnpackedFloat.compare, codeOf, sb]
    · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hxz, hyz, UnpackedFloat.compare, codeOf, sb]
  by_cases hyz : isZero y = true
  · cases sOf x <;> cases sOf y <;> simp [hxi, hyi, hxz, hyz, UnpackedFloat.compare, codeOf, sb]
  simp only [hxi, hyi, hxz, hyz, ite_false, dite_false, Bool.false_eq_true]
  rw [cmpMag_eq]
  cases sOf x <;> cases sOf y <;> simp [UnpackedFloat.compare, codeOf, sb]
  generalize Ordering.then _ _ = o
  cases o <;> rfl

end Interval64.KF
