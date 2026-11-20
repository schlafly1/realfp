/-
Value preservation of `unpack ∘ pack` on canonical finites, and enclosure
of `packDirected` including overflow to ±∞ / ±MaxFinite.
-/
import Interval64Proofs.Pack
import Interval64Proofs.Canonical
import Init.Data.BitVec.Lemmas
import Init.Data.UInt.Lemmas

namespace Interval64Proofs.PackFinite

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.Add
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Biased exponent of a canonical normal -/

theorem biased_int_eq {e : Int}
    (hle : spec64.minExponent ≤ e) (_hlt : e < overflowExponent) :
    (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit : Int) =
      ((e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat : Int) := by
  rw [exponentBias_spec64, mantissaBitsWithoutImplicit_spec64]
  have hle' : (-1074 : Int) ≤ e := by
    have hm : spec64.minExponent = -1074 := minExponent_spec64
    rw [hm] at hle
    exact hle
  have hpos : (0 : Int) ≤ e + 1023 + 52 :=
    Int.le_trans (by decide : (0 : Int) ≤ (-1074 : Int) + 1023 + 52)
      (Int.add_le_add_right (Int.add_le_add_right hle' 1023) 52)
  exact (Int.toNat_of_nonneg hpos).symm

theorem biased_bounds {e : Int}
    (hle : spec64.minExponent ≤ e) (hlt : e < overflowExponent) :
    0 < (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat ∧
      (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat < 2 ^ 11 - 1 := by
  have heq := biased_int_eq hle hlt
  have hlo' : (1 : Int) ≤ e + 1075 := by
    simp [minExponent_spec64] at hle
    omega
  have hhi' : e + 1075 < (2047 : Int) := by
    simp [overflowExponent] at hlt
    omega
  have hcast : (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit : Int) = e + 1075 := by
    simp [exponentBias_spec64]
    omega
  constructor
  · have : (0 : Int) < ((e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat : Int) := by
      rw [← heq, hcast]
      omega
    exact Int.natCast_pos.mp this
  · have : ((e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat : Int) < 2047 := by
      rw [← heq, hcast]
      exact hhi'
    exact Int.ofNat_lt.mp this

theorem exponentBits_pow : 2 ^ spec64.exponentBits = 2048 := by
  rw [exponentBits_spec64]

theorem not_overflow_of_normal {m : Nat} {e : Int} (hn : IsNormal m e) :
    ¬ (2 ^ spec64.exponentBits ≤
        (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat + 1) := by
  have ⟨hle, hlt, _, _⟩ := hn
  have hb := (biased_bounds hle hlt).2
  rw [exponentBits_pow]
  omega

theorem overflow_of_ge {e : Int} (hov : overflowExponent ≤ e) :
    2 ^ spec64.exponentBits ≤
      (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat + 1 := by
  have hpos : (0 : Int) ≤ e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit := by
    simp [overflowExponent] at hov
    omega
  have heq : ((e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat : Int) =
      e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit :=
    Int.toNat_of_nonneg hpos
  have hge : (2047 : Int) ≤ e + 1075 := by
    simp [overflowExponent] at hov
    omega
  have : (2047 : Int) ≤ ((e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat : Int) := by
    rw [heq]
    simp [exponentBias_spec64]
    omega
  simp
  have : 2047 ≤ (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat :=
    Int.ofNat_le.mp this
  omega

/-! ### BitVec packing of a 53-bit mantissa -/

theorem toNat_ofNat_52_of_lt {m : Nat} (h : m < 2 ^ 52) :
    (BitVec.ofNat 52 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_one1 : (1#1).toNat = 1 := rfl

theorem implicit_toNat (v : BitVec 52) :
    (1#1 ++ v).toNat = 2 ^ 52 + v.toNat := by
  rw [BitVec.toNat_append_eq_mul_add, toNat_one1, Nat.one_mul]

theorem mod_pow52_of_normal {m : Nat} (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) :
    m % 2 ^ 52 = m - 2 ^ 52 := by
  have hsub : m - 2 ^ 52 < 2 ^ 52 := by
    have : m < 2 ^ 52 + 2 ^ 52 := by
      have : (2 ^ 53 : Nat) = 2 ^ 52 + 2 ^ 52 := by decide
      omega
    omega
  have : m = 2 ^ 52 * 1 + (m - 2 ^ 52) := by omega
  conv => lhs; rw [this]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]

theorem implicit_mantissa {m : Nat} (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) :
    (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
  rw [implicit_toNat, BitVec.toNat_ofNat, mod_pow52_of_normal hlo hhi]
  exact Nat.add_sub_of_le hlo

theorem ofNat11_ne_negOne {n : Nat} (h : n < 2 ^ 11 - 1) :
    BitVec.ofNat 11 n ≠ -1#11 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at ht
  have hlt : n < 2 ^ 11 := Nat.lt_trans h (by decide)
  rw [Nat.mod_eq_of_lt hlt] at ht
  omega

theorem ofNat11_ne_zero {n : Nat} (h : 0 < n) (h2 : n < 2 ^ 11) :
    BitVec.ofNat 11 n ≠ 0#11 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero] at ht
  rw [Nat.mod_eq_of_lt h2] at ht
  omega

theorem finite_congr (s : Sign) {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (hm : m₁ = m₂) (he : e₁ = e₂) :
    UnpackedFloat.finite s m₁ e₁ h₁ = .finite s m₂ e₂ h₂ := by
  cases hm
  cases he
  rfl

/-! ### `pack` of a canonical normal is the component encoding -/

theorem pack_normal_eq (s : Sign) {m : Nat} {e : Int} (h : 0 < m) (hn : IsNormal m e) :
    UnpackedFloat.pack spec64 (.finite s m e h) =
      packComponents spec64 s
        (BitVec.ofNat spec64.exponentBits
          (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat)
        (BitVec.ofNat spec64.mantissaBitsWithoutImplicit m) := by
  have ⟨hle, hlt, hlo, hhi⟩ := hn
  have hlog : m.log2 + 1 = spec64.mantissaBits := by
    rw [log2_eq_52 hlo hhi, mantissaBits_spec64]
  have hnov := not_overflow_of_normal hn
  unfold UnpackedFloat.pack
  simp only [hnov, ↓reduceIte]
  simp only [hlog, ↓reduceIte]

theorem unpack_pack_normal (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hn : IsNormal m e) :
    UnpackedFloat.unpack spec64 (UnpackedFloat.pack spec64 (.finite s m e h)) = .finite s m e h := by
  have ⟨hle, hlt, hlo, hhi⟩ := hn
  have hb := biased_bounds hle hlt
  rw [pack_normal_eq s h hn]
  unfold UnpackedFloat.unpack
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents, Sign_ofBitVec_toBitVec]
  have hne1 : BitVec.ofNat spec64.exponentBits
      (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat ≠ -1#_ := by
    simp only [exponentBits_spec64]
    exact ofNat11_ne_negOne hb.2
  have hne0 : BitVec.ofNat spec64.exponentBits
      (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat ≠ 0#_ := by
    simp only [exponentBits_spec64]
    exact ofNat11_ne_zero hb.1 (Nat.lt_trans hb.2 (by decide))
  simp only [hne1, ↓reduceIte, hne0, ↓reduceIte]
  have hmant : (1#1 ++ BitVec.ofNat spec64.mantissaBitsWithoutImplicit m).toNat = m := by
    simp only [mantissaBitsWithoutImplicit_spec64]
    exact implicit_mantissa hlo hhi
  have hexp :
      ((BitVec.ofNat spec64.exponentBits
          (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat).toNat : Int) -
        (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) = e := by
    have hlt11 : (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat < 2 ^ 11 :=
      Nat.lt_trans hb.2 (by decide)
    simp only [exponentBits_spec64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt11]
    have heq := biased_int_eq hle hlt
    rw [← heq]
    simp [exponentBias_spec64]
    omega
  exact finite_congr s _ h hmant hexp

/-! ### `pack` of a canonical subnormal -/

theorem log2_lt_52 {m : Nat} (hm : 0 < m) (h : m < 2 ^ 52) : m.log2 < 52 :=
  (Nat.log2_lt (Nat.ne_of_gt hm)).mpr h

theorem not_normal_bits_of_subnormal {m : Nat} {e : Int} (hs : IsSubnormal m e) :
    m.log2 + 1 ≠ spec64.mantissaBits := by
  have ⟨_, hm, hhi⟩ := hs
  have := log2_lt_52 hm hhi
  simp [mantissaBits_spec64]
  omega

theorem not_overflow_of_subnormal {m : Nat} {e : Int} (hs : IsSubnormal m e) :
    ¬ (2 ^ spec64.exponentBits ≤
        (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat + 1) := by
  have ⟨he, _, _⟩ := hs
  rw [he]
  simp [minExponent_spec64, exponentBias_spec64]

theorem pack_subnormal_eq (s : Sign) {m : Nat} {e : Int} (h : 0 < m) (hs : IsSubnormal m e) :
    UnpackedFloat.pack spec64 (.finite s m e h) =
      packComponents spec64 s 0#_
        (BitVec.ofNat spec64.mantissaBitsWithoutImplicit m) := by
  have hnov := not_overflow_of_subnormal hs
  have hbits := not_normal_bits_of_subnormal hs
  unfold UnpackedFloat.pack
  simp only [hnov, ↓reduceIte, hbits, ↓reduceIte]

theorem unpack_pack_subnormal (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e) :
    UnpackedFloat.unpack spec64 (UnpackedFloat.pack spec64 (.finite s m e h)) = .finite s m e h := by
  have ⟨he, hm, hhi⟩ := hs
  rw [pack_subnormal_eq s h hs]
  unfold UnpackedFloat.unpack
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents, Sign_ofBitVec_toBitVec]
  have hne1 : (0#_ : BitVec spec64.exponentBits) ≠ -1#_ := by
    simp [exponentBits_spec64, BitVec.neg_one_eq_allOnes]
  simp only [hne1, ↓reduceIte]
  have hmnz : BitVec.ofNat spec64.mantissaBitsWithoutImplicit m ≠ 0#_ := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    simp [mantissaBitsWithoutImplicit_spec64, BitVec.toNat_ofNat] at ht
    rw [Nat.mod_eq_of_lt hhi] at ht
    exact Nat.ne_of_gt hm ht
  simp only [hmnz, ↓reduceDIte]
  have hmant : (BitVec.ofNat spec64.mantissaBitsWithoutImplicit m).toNat = m := by
    simp [mantissaBitsWithoutImplicit_spec64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi]
  have hexp : ((0#_ : BitVec spec64.exponentBits).toNat : Int) -
      (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) + 1 = e := by
    simp [exponentBits_spec64, exponentBias_spec64, he,
      minExponent_spec64]
  exact finite_congr s _ h hmant hexp

theorem unpackBits_pack_normal (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hn : IsNormal m e) :
    unpackBits (packBits (.finite s m e h)) = .finite s m e h := by
  rw [unpackBits_packBits, unpack_pack_normal s h hn]

theorem unpackBits_pack_subnormal (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e) :
    unpackBits (packBits (.finite s m e h)) = .finite s m e h := by
  rw [unpackBits_packBits, unpack_pack_subnormal s h hs]

theorem bitsToEVal_pack_canonical (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hc : IsCanonicalFinite m e) :
    bitsToEVal (packBits (.finite s m e h)) = some (.rat (signedVal s m e)) := by
  cases hc with
  | inl hs => simp [bitsToEVal, unpackBits_pack_subnormal s h hs]
  | inr hn => simp [bitsToEVal, unpackBits_pack_normal s h hn]


/-! ### Overflow packing and MaxFinite -/

theorem pow2_ge_one {e : Int} (h : 0 ≤ e) : (1 : Rat) ≤ pow2 e := by
  have he : (e.toNat : Int) = e := Int.toNat_of_nonneg h
  rw [pow2_eq_zpow, ← he, Rat.zpow_natCast]
  induction e.toNat with
  | zero => simp
  | succ n ih =>
    have : (2 : Rat) ^ (n + 1) = (2 : Rat) ^ n * 2 := by
      rw [Rat.pow_succ]
    rw [this]
    exact Rat.le_trans ih (by
      have hnn : (0 : Rat) ≤ (2 : Rat) ^ n := Rat.le_trans (by decide : (0 : Rat) ≤ 1) ih
      have hmul : (2 : Rat) ^ n * 1 ≤ (2 : Rat) ^ n * 2 :=
        Rat.mul_le_mul_of_nonneg_left (by decide : (1 : Rat) ≤ 2) hnn
      simpa [Rat.mul_one] using hmul)

theorem pow2_le {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  have hnn : 0 ≤ b - a := Int.sub_nonneg_of_le h
  have hsplit : pow2 b = pow2 a * pow2 (b - a) := by
    have hab : a + (b - a) = b := by omega
    rw [← pow2_add, hab]
  rw [hsplit]
  have h1 : (1 : Rat) ≤ pow2 (b - a) := pow2_ge_one hnn
  have : pow2 a * 1 ≤ pow2 a * pow2 (b - a) :=
    Rat.mul_le_mul_of_nonneg_left h1 (pow2_nonneg a)
  simpa [Rat.mul_one] using this

theorem mag_mono_exp {m : Nat} {e₁ e₂ : Int} (h : e₁ ≤ e₂) :
    mag m e₁ ≤ mag m e₂ :=
  Rat.mul_le_mul_of_nonneg_left (pow2_le h) (Rat.natCast_nonneg)

theorem mag_maxFinite_lt_overflow :
    mag (2 ^ 53 - 1) 971 < mag (2 ^ 52) 972 := by
  have hadd : mag ((2 ^ 53 - 1) + 1) 971 = mag (2 ^ 53 - 1) 971 + mag 1 971 :=
    mag_add (2 ^ 53 - 1) 1 971
  have h53 : (2 ^ 53 - 1 + 1 : Nat) = 2 ^ 53 := by decide
  have hpow : mag (2 ^ 53) 971 = mag (2 ^ 52) 972 := by
    have : (2 ^ 53 : Nat) = 2 ^ 52 * 2 ^ 1 := by decide
    rw [this, mag_mul_two_pow_add]
    rfl
  have heq : mag (2 ^ 53 - 1) 971 + mag 1 971 = mag (2 ^ 52) 972 := by
    rw [← hadd, h53, hpow]
  have hpos : (0 : Rat) < mag 1 971 := by
    rw [mag_one]
    exact pow2_pos _
  have hlt : mag (2 ^ 53 - 1) 971 + 0 < mag (2 ^ 53 - 1) 971 + mag 1 971 :=
    (Rat.add_lt_add_left (a := 0) (b := mag 1 971)
      (c := mag (2 ^ 53 - 1) 971)).mpr hpos
  rw [Rat.add_zero, heq] at hlt
  exact hlt

theorem mag_le_of_overflow {m : Nat} {e : Int} (h : IsOverflowNormal m e) :
    mag (2 ^ 53 - 1) 971 ≤ mag m e := by
  have ⟨hov, hlo, _⟩ := h
  have h1 : mag (2 ^ 53 - 1) 971 < mag (2 ^ 52) 972 := mag_maxFinite_lt_overflow
  have h2 : mag (2 ^ 52) 972 ≤ mag (2 ^ 52) e := mag_mono_exp hov
  have h3 : mag (2 ^ 52) e ≤ mag m e := mag_le_mag hlo
  exact Rat.le_trans (Rat.le_of_lt h1) (Rat.le_trans h2 h3)

theorem isNormal_maxFinite : IsNormal (2 ^ 53 - 1) 971 := by
  simp [IsNormal, minExponent_spec64, overflowExponent]

theorem bitsToEVal_pack_maxFinite (s : Sign) :
    bitsToEVal (packBits (maxFinite s)) = some (.rat (signedVal s (2 ^ 53 - 1) 971)) := by
  unfold maxFinite
  exact bitsToEVal_pack_canonical s (by decide) (Or.inr isNormal_maxFinite)

theorem packDirected_eq_pack_of_canonical (up : Bool) (s : Sign) {m : Nat} {e : Int}
    (h : 0 < m) (hc : IsCanonicalFinite m e) :
    packDirected up (.finite s m e h) = packBits (.finite s m e h) := by
  unfold packDirected
  have hnov : ¬ (2 ^ spec64.exponentBits ≤
      (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat + 1) := by
    cases hc with
    | inl hs => exact not_overflow_of_subnormal hs
    | inr hn => exact not_overflow_of_normal hn
  simp only [hnov, ↓reduceIte]

theorem packDirected_eq_overflow (up : Bool) (s : Sign) {m : Nat} {e : Int}
    (h : 0 < m) (hov : overflowExponent ≤ e) :
    packDirected up (.finite s m e h) =
      if awayFromZero up s then packBits (.infinity s) else packBits (maxFinite s) := by
  unfold packDirected
  have ho := overflow_of_ge hov
  simp only [ho, ↓reduceIte]

/-- Lower pack of a shaped finite encloses its exact signed value. -/
theorem loEncloses_packDirected_shaped (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e) :
    loEncloses? (bitsToEVal (packDirected false (.finite s m e h))) (signedVal s m e) := by
  rcases hs with hsub | hnorm | hov
  · rw [packDirected_eq_pack_of_canonical false s h (Or.inl hsub),
      bitsToEVal_pack_canonical s h (Or.inl hsub)]
    simp [loEncloses?, loEncloses]
  · rw [packDirected_eq_pack_of_canonical false s h (Or.inr hnorm),
      bitsToEVal_pack_canonical s h (Or.inr hnorm)]
    simp [loEncloses?, loEncloses]
  · have ⟨he, hlo, _⟩ := hov
    rw [packDirected_eq_overflow false s h he]
    cases s with
    | negative =>
      simp [awayFromZero, bitsToEVal_pack_inf, loEncloses?]
    | positive =>
      simp [awayFromZero, bitsToEVal_pack_maxFinite, loEncloses?, loEncloses, signedVal]
      exact mag_le_of_overflow hov

theorem hiEncloses_packDirected_shaped (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e) :
    hiEncloses? (bitsToEVal (packDirected true (.finite s m e h))) (signedVal s m e) := by
  rcases hs with hsub | hnorm | hov
  · rw [packDirected_eq_pack_of_canonical true s h (Or.inl hsub),
      bitsToEVal_pack_canonical s h (Or.inl hsub)]
    simp [hiEncloses?, hiEncloses]
  · rw [packDirected_eq_pack_of_canonical true s h (Or.inr hnorm),
      bitsToEVal_pack_canonical s h (Or.inr hnorm)]
    simp [hiEncloses?, hiEncloses]
  · have ⟨he, hlo, _⟩ := hov
    rw [packDirected_eq_overflow true s h he]
    cases s with
    | positive =>
      simp [awayFromZero, bitsToEVal_pack_inf, hiEncloses?]
    | negative =>
      simp [awayFromZero, bitsToEVal_pack_maxFinite, hiEncloses?, hiEncloses, signedVal]
      exact mag_le_of_overflow hov

/-! ### Lifting enclosure through `packDirected` for add/normalize output -/

theorem loEncloses_packDirected_zero_val (up : Bool) (z : Sign) (x : Rat)
    (hx : loEncloses? (toEVal (.zero z)) x) :
    loEncloses? (bitsToEVal (packDirected up (.zero z))) x := by
  simpa [packDirected_zero, bitsToEVal_pack_zero, toEVal] using hx

theorem hiEncloses_packDirected_zero_val (up : Bool) (z : Sign) (x : Rat)
    (hx : hiEncloses? (toEVal (.zero z)) x) :
    hiEncloses? (bitsToEVal (packDirected up (.zero z))) x := by
  simpa [packDirected_zero, bitsToEVal_pack_zero, toEVal] using hx

theorem loEncloses_trans {v : Option EVal} {a b : Rat}
    (h : loEncloses? v a) (hle : a ≤ b) : loEncloses? v b := by
  cases v with
  | none => exact h
  | some ev =>
    cases ev with
    | negInf => trivial
    | posInf => exact h
    | rat q => exact Rat.le_trans h hle

theorem hiEncloses_trans {v : Option EVal} {a b : Rat}
    (h : hiEncloses? v a) (hle : b ≤ a) : hiEncloses? v b := by
  cases v with
  | none => exact h
  | some ev =>
    cases ev with
    | posInf => trivial
    | negInf => exact h
    | rat q => exact Rat.le_trans hle h

theorem loEncloses_packDirected_of_shaped (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e) (x : Rat)
    (hx : loEncloses? (toEVal (.finite s m e h)) x) :
    loEncloses? (bitsToEVal (packDirected false (.finite s m e h))) x :=
  loEncloses_trans (loEncloses_packDirected_shaped s h hs) (by
    simpa [toEVal, loEncloses?, loEncloses] using hx)

theorem hiEncloses_packDirected_of_shaped (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hs : IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e) (x : Rat)
    (hx : hiEncloses? (toEVal (.finite s m e h)) x) :
    hiEncloses? (bitsToEVal (packDirected true (.finite s m e h))) x :=
  hiEncloses_trans (hiEncloses_packDirected_shaped s h hs) (by
    simpa [toEVal, hiEncloses?, hiEncloses] using hx)

end Interval64Proofs.PackFinite
