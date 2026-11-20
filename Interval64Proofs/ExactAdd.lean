/-
If the exact sum is a representable binary64 value, directed add is exact.
Integer corollary for `|a|`, `|b|`, `|a+b| ≤ 2^53`.
-/
import Interval64Proofs.AddBits

namespace Interval64Proofs.ExactAdd

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.Add
open Interval64Proofs.AddBits
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Equality of magnitudes implies a power-of-two shift -/

theorem rat_eq_nat_mul_pow {m m' k : Nat}
    (h : (m : Rat) = (m' : Rat) * (2 : Rat) ^ k) :
    m = m' * 2 ^ k := by
  have : (m : Rat) = ((m' * 2 ^ k : Nat) : Rat) := by
    rw [h, Rat.natCast_mul, Rat.natCast_pow]
    rfl
  exact Rat.natCast_inj.mp this

theorem mag_eq_cases {m m' : Nat} {e e' : Int} (_hm : 0 < m) (_hm' : 0 < m')
    (h : mag m e = mag m' e') :
    (e ≤ e' ∧ m = m' * 2 ^ (e' - e).toNat) ∨
      (e' ≤ e ∧ m' = m * 2 ^ (e - e').toNat) := by
  cases Int.le_total e e' with
  | inl hle =>
    refine Or.inl ⟨hle, ?_⟩
    have hk : 0 ≤ e' - e := Int.sub_nonneg_of_le hle
    have hpow : pow2 e' = pow2 e * pow2 (e' - e) := by
      have : e + (e' - e) = e' := by omega
      rw [← pow2_add, this]
    have hmul : (m : Rat) * pow2 e = ((m' : Rat) * pow2 (e' - e)) * pow2 e := by
      unfold mag at h
      calc
        (m : Rat) * pow2 e = (m' : Rat) * pow2 e' := h
        _ = (m' : Rat) * (pow2 e * pow2 (e' - e)) := by rw [hpow]
        _ = (m' : Rat) * (pow2 (e' - e) * pow2 e) := by rw [Rat.mul_comm (pow2 e)]
        _ = ((m' : Rat) * pow2 (e' - e)) * pow2 e := by rw [Rat.mul_assoc]
    have hcancel : (m : Rat) = (m' : Rat) * pow2 (e' - e) := by
      have hp := pow2_ne_zero e
      calc
        (m : Rat) = (m : Rat) * pow2 e * (pow2 e)⁻¹ := by
          rw [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 e) hp, Rat.mul_one]
        _ = ((m' : Rat) * pow2 (e' - e)) * pow2 e * (pow2 e)⁻¹ := by rw [hmul]
        _ = (m' : Rat) * pow2 (e' - e) := by
          rw [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 e) hp, Rat.mul_one]
    have hpow' : pow2 (e' - e) = (2 : Rat) ^ (e' - e).toNat := by
      have this := pow2_nat (e' - e).toNat
      exact (Int.toNat_of_nonneg hk).symm ▸ this
    rw [hpow'] at hcancel
    exact rat_eq_nat_mul_pow hcancel
  | inr hle =>
    refine Or.inr ⟨hle, ?_⟩
    have hk : 0 ≤ e - e' := Int.sub_nonneg_of_le hle
    have hpow : pow2 e = pow2 e' * pow2 (e - e') := by
      have : e' + (e - e') = e := by omega
      rw [← pow2_add, this]
    have hmul : (m' : Rat) * pow2 e' = ((m : Rat) * pow2 (e - e')) * pow2 e' := by
      unfold mag at h
      calc
        (m' : Rat) * pow2 e' = (m : Rat) * pow2 e := h.symm
        _ = (m : Rat) * (pow2 e' * pow2 (e - e')) := by rw [hpow]
        _ = (m : Rat) * (pow2 (e - e') * pow2 e') := by rw [Rat.mul_comm (pow2 e')]
        _ = ((m : Rat) * pow2 (e - e')) * pow2 e' := by rw [Rat.mul_assoc]
    have hcancel : (m' : Rat) = (m : Rat) * pow2 (e - e') := by
      have hp := pow2_ne_zero e'
      calc
        (m' : Rat) = (m' : Rat) * pow2 e' * (pow2 e')⁻¹ := by
          rw [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 e') hp, Rat.mul_one]
        _ = ((m : Rat) * pow2 (e - e')) * pow2 e' * (pow2 e')⁻¹ := by rw [hmul]
        _ = (m : Rat) * pow2 (e - e') := by
          rw [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 e') hp, Rat.mul_one]
    have hpow' : pow2 (e - e') = (2 : Rat) ^ (e - e').toNat := by
      have this := pow2_nat (e - e').toNat
      exact (Int.toNat_of_nonneg hk).symm ▸ this
    rw [hpow'] at hcancel
    exact rat_eq_nat_mul_pow hcancel

theorem signedVal_eq_of_same_sign {s : Sign} {m m' : Nat} {e e' : Int}
    (h : signedVal s m e = signedVal s m' e') : mag m e = mag m' e' := by
  cases s with
  | positive => simpa [signedVal] using h
  | negative =>
    have := congrArg (fun q => -q) h
    simpa [signedVal, Rat.neg_neg] using this



theorem mag_pos {m : Nat} {e : Int} (h : 0 < m) : (0 : Rat) < mag m e :=
  Rat.mul_pos (Rat.natCast_pos.mpr h) (pow2_pos e)

theorem signedVal_eq_implies_sign {s s' : Sign} {m m' : Nat} {e e' : Int}
    (hm : 0 < m) (hm' : 0 < m')
    (h : signedVal s m e = signedVal s' m' e') : s = s' := by
  cases s with
  | positive =>
    cases s' with
    | positive => rfl
    | negative =>
      simp [signedVal] at h
      have hp : (0 : Rat) < -mag m' e' := h ▸ mag_pos hm
      have hn : mag m' e' < 0 := by
        have := Rat.neg_lt_neg hp
        simpa [Rat.neg_neg, Rat.neg_zero] using this
      exact ((Rat.lt_iff_le_and_not_ge.mp hn).2 (Rat.le_of_lt (mag_pos hm'))).elim
  | negative =>
    cases s' with
    | negative => rfl
    | positive =>
      simp [signedVal] at h
      have hp : (0 : Rat) < -mag m e := h.symm ▸ mag_pos hm'
      have hn : mag m e < 0 := by
        have := Rat.neg_lt_neg hp
        simpa [Rat.neg_neg, Rat.neg_zero] using this
      exact ((Rat.lt_iff_le_and_not_ge.mp hn).2 (Rat.le_of_lt (mag_pos hm))).elim

theorem totalExponent_eq_of_shift {m m' : Nat} {e e' : Int} (hm' : m' ≠ 0)
    (hle : e ≤ e') (hm : m = m' * 2 ^ (e' - e).toNat) :
    totalExponent m e = totalExponent m' e' := by
  have hk : ((e' - e).toNat : Int) = e' - e := Int.toNat_of_nonneg (Int.sub_nonneg_of_le hle)
  unfold totalExponent
  rw [hm, log2_mul_two_pow m' _ hm']
  omega

theorem target_eq_of_canonical {m : Nat} {e : Int} (hc : IsCanonicalFinite m e) :
    spec64.targetExponent (totalExponent m e) = e :=
  hc.elim target_eq_of_subnormal target_eq_of_normal

theorem target_eq_of_eq_canonical {s : Sign} {m m' : Nat} {e e' : Int}
    (hm : 0 < m) (hm' : 0 < m') (hc : IsCanonicalFinite m' e')
    (hv : signedVal s m e = signedVal s m' e') :
    spec64.targetExponent (totalExponent m e) = e' := by
  have hmag := signedVal_eq_of_same_sign hv
  have htar : spec64.targetExponent (totalExponent m' e') = e' :=
    target_eq_of_canonical hc
  rcases mag_eq_cases hm hm' hmag with ⟨hle, hsh⟩ | ⟨hle, hsh⟩
  · have : totalExponent m e = totalExponent m' e' :=
      totalExponent_eq_of_shift (Nat.ne_of_gt hm') hle hsh
    rw [this, htar]
  · have : totalExponent m' e' = totalExponent m e :=
      totalExponent_eq_of_shift (Nat.ne_of_gt hm) hle hsh
    rw [← this, htar]


theorem canonical_minExp_le {m : Nat} {e : Int} (hc : IsCanonicalFinite m e) :
    spec64.minExponent ≤ e :=
  hc.elim (fun hs => Int.le_of_eq hs.1.symm) (fun hn => hn.1)

theorem canonical_mantissa_lt {m : Nat} {e : Int} (hc : IsCanonicalFinite m e) :
    m < 2 ^ 53 :=
  hc.elim (fun hs => Nat.lt_trans hs.2.2 (by decide)) (fun hn => hn.2.2.2)

theorem decrease_to_canonical {m m' : Nat} {e e' : Int}
    (hle : e' ≤ e) (hsh : m' = m * 2 ^ (e - e').toNat) :
    decreaseExponent m e e' = (m', e') := by
  have hk : ((e - e').toNat : Int) = e - e' := Int.toNat_of_nonneg (Int.sub_nonneg_of_le hle)
  simp only [decreaseExponent, Nat.shiftLeft_eq, hsh]
  have : e - (e - e').toNat = e' := by omega
  rw [this]

theorem firstRounded_eq_of_rshift (s : Sign) (m : Nat) (e : Int) (up : Bool)
    {m' : Nat} {e' : Int}
    (htar : spec64.targetExponent (totalExponent m e) = e')
    (hle : e ≤ e') (hsh : m = m' * 2 ^ (e' - e).toNat) :
    firstRounded s m e up = (m', e') := by
  have hdec : decreaseExponent m e (spec64.targetExponent (totalExponent m e)) = (m, e) := by
    rw [htar]
    have : (e - e').toNat = 0 := (Int.toNat_sub_eq_zero_iff e e').mpr hle
    simp [decreaseExponent, this, Nat.shiftLeft_zero]
  have hk : (spec64.targetExponent (totalExponent m e) - e).toNat = (e' - e).toNat := by
    rw [htar]
  have hmnt : (shiftToTargetExponent spec64 m e Accuracy.exact).1.mantissa = m' := by
    rw [shiftToTargetExponent_exact_mantissa, hk, hsh, Nat.shiftRight_eq_div_pow,
      Nat.mul_div_left _ (Nat.two_pow_pos _)]
  have hexp : (shiftToTargetExponent spec64 m e Accuracy.exact).2 = e' := by
    rw [shiftToTargetExponent_exact_exponent, hk]
    have : ((e' - e).toNat : Int) = e' - e := Int.toNat_of_nonneg (Int.sub_nonneg_of_le hle)
    omega
  have hacc : (shiftToTargetExponent spec64 m e Accuracy.exact).1.accuracy = .exact := by
    rw [shiftToTargetExponent, shiftToExponent]
    exact (shiftRight_exact_accuracy m _).mpr (by
      rw [hk, hsh, Nat.mul_mod_left])
  unfold firstRounded
  simp only [hdec]
  rw [hmnt, hexp, hacc]
  simp [roundMantissaDirected]

theorem firstRounded_eq_of_lshift (s : Sign) (m : Nat) (e : Int) (up : Bool)
    {m' : Nat} {e' : Int} (hc : IsCanonicalFinite m' e')
    (htar : spec64.targetExponent (totalExponent m e) = e')
    (hle : e' ≤ e) (hsh : m' = m * 2 ^ (e - e').toNat) :
    firstRounded s m e up = (m', e') := by
  have hdec : decreaseExponent m e (spec64.targetExponent (totalExponent m e)) = (m', e') := by
    rw [htar]
    exact decrease_to_canonical hle hsh
  have hz : (spec64.targetExponent (totalExponent m' e') - e').toNat = 0 := by
    rw [target_eq_of_canonical hc, Int.sub_self]
    simp
  have hmnt : (shiftToTargetExponent spec64 m' e' Accuracy.exact).1.mantissa = m' := by
    rw [shiftToTargetExponent_exact_mantissa, hz, Nat.shiftRight_zero]
  have hexp : (shiftToTargetExponent spec64 m' e' Accuracy.exact).2 = e' := by
    rw [shiftToTargetExponent_exact_exponent, hz, Int.natCast_zero, Int.add_zero]
  have hacc : (shiftToTargetExponent spec64 m' e' Accuracy.exact).1.accuracy = .exact := by
    rw [shiftToTargetExponent, shiftToExponent]
    exact (shiftRight_exact_accuracy m' _).mpr (by
      rw [hz, Nat.mod_one])
  unfold firstRounded
  simp only [hdec]
  rw [hmnt, hexp, hacc]
  simp [roundMantissaDirected]

theorem signedVal_ne_zero_of_pos {s : Sign} {m : Nat} {e : Int} (hm : 0 < m) :
    signedVal s m e ≠ 0 := by
  intro hz
  have hp : (0 : Rat) < mag m e := mag_pos hm
  cases s with
  | positive =>
    simp [signedVal] at hz
    rw [hz] at hp
    exact Rat.lt_irrefl hp
  | negative =>
    simp [signedVal] at hz
    have : mag m e = 0 := by
      have := congrArg (fun q => -q) hz
      simpa [Rat.neg_neg, Rat.neg_zero] using this
    rw [this] at hp
    exact Rat.lt_irrefl hp

theorem pos_of_signedVal_eq_canonical {s : Sign} {m m' : Nat} {e e' : Int}
    (h' : 0 < m') (hv : signedVal s m e = signedVal s m' e') : 0 < m := by
  refine Nat.pos_of_ne_zero ?_
  intro h0
  have h1 : signedVal s m e = 0 := by
    rw [h0]
    exact signedVal_zero s e
  have h2 : signedVal s m' e' = 0 := hv.symm.trans h1
  exact signedVal_ne_zero_of_pos h' h2


theorem roundDirected_eq_of_canonical (s : Sign) (m : Nat) (e : Int) (up : Bool)
    {m' : Nat} {e' : Int} (h' : 0 < m') (hc : IsCanonicalFinite m' e')
    (hv : signedVal s m e = signedVal s m' e') :
    roundDirected s m e .exact up = .finite s m' e' h' := by
  have hm : 0 < m := pos_of_signedVal_eq_canonical h' hv
  have htar := target_eq_of_eq_canonical (s := s) hm h' hc hv
  have hmag := signedVal_eq_of_same_sign hv
  have hfr : firstRounded s m e up = (m', e') := by
    rcases mag_eq_cases hm h' hmag with ⟨hle, hsh⟩ | ⟨hle, hsh⟩
    · exact firstRounded_eq_of_rshift s m e up htar hle hsh
    · exact firstRounded_eq_of_lshift s m e up hc htar hle hsh
  rw [roundDirected_eq_shift_of_rounded]
  -- after unfolding lets, firstRounded appears
  have hz : (spec64.targetExponent (totalExponent m' e') - e').toNat = 0 := by
    rw [target_eq_of_canonical hc, Int.sub_self]
    simp
  have hmnt : (shiftToTargetExponent spec64 (firstRounded s m e up).1
      (firstRounded s m e up).2 Accuracy.exact).1.mantissa = m' := by
    rw [hfr, shiftToTargetExponent_exact_mantissa, hz, Nat.shiftRight_zero]
  have hexp : (shiftToTargetExponent spec64 (firstRounded s m e up).1
      (firstRounded s m e up).2 Accuracy.exact).2 = e' := by
    rw [hfr, shiftToTargetExponent_exact_exponent, hz, Int.natCast_zero, Int.add_zero]
  have hne : (shiftToTargetExponent spec64 (firstRounded s m e up).1
      (firstRounded s m e up).2 Accuracy.exact).1.mantissa ≠ 0 := by
    rw [hmnt]
    exact Nat.ne_of_gt h'
  dsimp
  rw [dite_eq_right hne]
  exact finite_congr s _ h' hmnt hexp

theorem signedVal_of_pos_toNat (mant : Int) (e : Int) (h : 0 < mant) :
    signedVal .positive mant.toNat e = (mant : Rat) * pow2 e := by
  have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (Int.le_of_lt h)
  simp only [signedVal, mag]
  rw [← Rat.intCast_natCast, hnat]

theorem signedVal_of_neg_toNat (mant : Int) (e : Int) (h : mant < 0) :
    signedVal .negative (-mant).toNat e = (mant : Rat) * pow2 e := by
  have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (by omega)
  simp only [signedVal, mag]
  rw [← Rat.intCast_natCast, hnat, Rat.intCast_neg, ← Rat.neg_mul, Rat.neg_neg]

theorem normalizeDirected_eq_of_canonical (mant : Int) (e : Int) (z : Sign) (up : Bool)
    {s : Sign} {m' : Nat} {e' : Int} (h' : 0 < m') (hc : IsCanonicalFinite m' e')
    (hv : (mant : Rat) * pow2 e = signedVal s m' e') :
    normalizeDirected mant e z up = .finite s m' e' h' := by
  unfold normalizeDirected
  cases hc0 : compare mant 0 with
  | eq =>
    have heq : mant = 0 := (Int.compare_eq_eq).mp hc0
    have : (0 : Rat) = signedVal s m' e' := by
      simpa [heq] using hv
    exact (signedVal_ne_zero_of_pos h' this.symm).elim
  | lt =>
    have hlt : mant < 0 := (Int.compare_eq_lt).mp hc0
    have hpos : 0 < (-mant).toNat := by
      have : 0 < -mant := by omega
      have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (Int.le_of_lt this)
      exact Int.natCast_pos.mp (by omega)
    have hv' : signedVal .negative (-mant).toNat e = signedVal s m' e' := by
      rw [signedVal_of_neg_toNat mant e hlt, hv]
    have hs : s = .negative :=
      (signedVal_eq_implies_sign (s := .negative) (s' := s) hpos h' hv').symm
    subst hs
    exact roundDirected_eq_of_canonical .negative (-mant).toNat e up h' hc hv'
  | gt =>
    have hgt : 0 < mant := (Int.compare_eq_gt).mp hc0
    have hpos : 0 < mant.toNat := by
      have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (Int.le_of_lt hgt)
      exact Int.natCast_pos.mp (by omega)
    have hv' : signedVal .positive mant.toNat e = signedVal s m' e' := by
      rw [signedVal_of_pos_toNat mant e hgt, hv]
    have hs : s = .positive :=
      (signedVal_eq_implies_sign (s := .positive) (s' := s) hpos h' hv').symm
    subst hs
    exact roundDirected_eq_of_canonical .positive mant.toNat e up h' hc hv'

theorem normalizeDirected_of_value_zero (mant : Int) (e : Int) (z : Sign) (up : Bool)
    (hv : (mant : Rat) * pow2 e = 0) :
    ∃ s, normalizeDirected mant e z up = .zero s := by
  have hmant : mant = 0 := by
    have hp := pow2_ne_zero e
    have : (mant : Rat) = 0 := by
      have := congrArg (fun x => x * (pow2 e)⁻¹) hv
      have hl : (mant : Rat) * pow2 e * (pow2 e)⁻¹ = (mant : Rat) := by
        rw [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 e) hp, Rat.mul_one]
      have hr : (0 : Rat) * (pow2 e)⁻¹ = 0 := by simp
      rw [hl, hr] at this
      exact this
    exact Rat.intCast_eq_zero_iff.mp this
  unfold normalizeDirected
  rw [hmant]
  exact ⟨z, rfl⟩


/-! ### Packing a canonical (or zero) result preserves its rational value -/

theorem bitsToRat?_pack_canonical (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hc : IsCanonicalFinite m e) :
    bitsToRat? (packBits (.finite s m e h)) = some (signedVal s m e) := by
  have := bitsToEVal_pack_canonical s h hc
  have heq := bitsToRat?_eq_bitsToEVal (packBits (.finite s m e h))
  simp [this] at heq
  exact heq

theorem bitsToRat?_packDirected_canonical (up : Bool) (s : Sign) {m : Nat} {e : Int}
    (h : 0 < m) (hc : IsCanonicalFinite m e) :
    bitsToRat? (packDirected up (.finite s m e h)) = some (signedVal s m e) := by
  rw [packDirected_eq_pack_of_canonical up s h hc]
  exact bitsToRat?_pack_canonical s h hc

theorem bitsToRat?_packDirected_zero (up : Bool) (s : Sign) :
    bitsToRat? (packDirected up (.zero s)) = some 0 := by
  simp [packDirected_zero, bitsToRat?, unpackBits_zero, toRat?]

theorem representable_cases {q : Rat} (h : ∃ c, bitsToRat? c = some q) :
    q = 0 ∨ ∃ s m e, ∃ _hp : 0 < m, IsCanonicalFinite m e ∧ q = signedVal s m e := by
  rcases h with ⟨c, hc⟩
  rcases bitsToRat?_cases hc with h0 | hf
  · rcases h0 with ⟨_, _, rfl⟩
    exact Or.inl rfl
  · rcases hf with ⟨s, m, e, hp, _, rfl, hcan⟩
    exact Or.inr ⟨s, m, e, hp, hcan, rfl⟩

/-! ### Finite add is exact when the sum is representable -/

theorem add_exact {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hrep : ∃ c, bitsToRat? c = some (qa + qb)) :
    bitsToRat? (addDown a b) = some (qa + qb) ∧
    bitsToRat? (addUp a b) = some (qa + qb) := by
  rcases representable_cases hrep with hq0 | hqf
  · have hdown : bitsToRat? (addDown a b) = some 0 ∧
        bitsToRat? (addUp a b) = some 0 := by
      simp only [addDown, addUp, Interval64.Spec.add]
      rcases bitsToRat?_cases ha with hza | hfa
      · rcases hza with ⟨s1, hu1, rfl⟩
        rcases bitsToRat?_cases hb with hzb | hfb
        · rcases hzb with ⟨s2, hu2, rfl⟩
          rw [hu1, hu2]
          simp only [addU]
          constructor <;> (split <;> exact bitsToRat?_packDirected_zero _ _)
        · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
          have : signedVal s2 m2 e2 = 0 := by
            have h := hq0
            rw [Rat.zero_add] at h
            exact h
          exact (signedVal_ne_zero_of_pos h2 this).elim
      · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
        rcases bitsToRat?_cases hb with hzb | hfb
        · rcases hzb with ⟨s2, hu2, rfl⟩
          have : signedVal s1 m1 e1 = 0 := by
            have h := hq0
            rw [Rat.add_zero] at h
            exact h
          exact (signedVal_ne_zero_of_pos h1 this).elim
        · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
          rw [hu1, hu2]
          have hv : ((s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
              s2.apply (decreaseExponent m2 e2 (min e1 e2)).1 : Int) : Rat) *
              pow2 (min e1 e2) = 0 := by
            have := aligned_sum_eq s1 s2 m1 m2 e1 e2
            rw [this, hq0]
          constructor
          · have ⟨z, hz⟩ := normalizeDirected_of_value_zero
              (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
              (min e1 e2) (cancelZero false) false hv
            have hadd :
                addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
                  normalizeDirected
                    (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                      s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
                    (min e1 e2) (cancelZero false) false := rfl
            rw [hadd, hz]
            exact bitsToRat?_packDirected_zero _ _
          · have ⟨z, hz⟩ := normalizeDirected_of_value_zero
              (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
              (min e1 e2) (cancelZero true) true hv
            have hadd :
                addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
                  normalizeDirected
                    (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                      s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
                    (min e1 e2) (cancelZero true) true := rfl
            rw [hadd, hz]
            exact bitsToRat?_packDirected_zero _ _
    rw [hq0]
    exact hdown
  · rcases hqf with ⟨s, m', e', h', hc, hvq⟩
    simp only [addDown, addUp, Interval64.Spec.add]
    rcases bitsToRat?_cases ha with hza | hfa
    · rcases hza with ⟨s1, hu1, rfl⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨s2, hu2, rfl⟩
        have : signedVal s m' e' = 0 := by
          have h := hvq.symm
          rw [Rat.add_zero] at h
          exact h
        exact (signedVal_ne_zero_of_pos h' this).elim
      · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
        constructor
        · rw [hu1, hu2, addU_zero_finite s1 s2 m2 e2 h2 false]
          rw [bitsToRat?_packDirected_canonical false s2 h2 hc2, Rat.zero_add]
        · rw [hu1, hu2, addU_zero_finite s1 s2 m2 e2 h2 true]
          rw [bitsToRat?_packDirected_canonical true s2 h2 hc2, Rat.zero_add]
    · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨s2, hu2, rfl⟩
        constructor
        · rw [hu1, hu2, addU_finite_zero s1 s2 m1 e1 h1 false]
          rw [bitsToRat?_packDirected_canonical false s1 h1 hc1, Rat.add_zero]
        · rw [hu1, hu2, addU_finite_zero s1 s2 m1 e1 h1 true]
          rw [bitsToRat?_packDirected_canonical true s1 h1 hc1, Rat.add_zero]
      · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
        rw [hu1, hu2]
        have hv : ((s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
            s2.apply (decreaseExponent m2 e2 (min e1 e2)).1 : Int) : Rat) *
            pow2 (min e1 e2) = signedVal s m' e' := by
          have := aligned_sum_eq s1 s2 m1 m2 e1 e2
          rw [this, hvq]
        constructor
        · have heq := normalizeDirected_eq_of_canonical
            (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
              s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
            (min e1 e2) (cancelZero false) false h' hc hv
          have hadd :
              addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
                normalizeDirected
                  (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                    s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
                  (min e1 e2) (cancelZero false) false := rfl
          rw [hadd, heq, bitsToRat?_packDirected_canonical false s h' hc, hvq]
        · have heq := normalizeDirected_eq_of_canonical
            (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
              s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
            (min e1 e2) (cancelZero true) true h' hc hv
          have hadd :
              addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
                normalizeDirected
                  (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                    s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
                  (min e1 e2) (cancelZero true) true := rfl
          rw [hadd, heq, bitsToRat?_packDirected_canonical true s h' hc, hvq]


/-! ### Integers with absolute value at most `2^53` are representable -/

theorem mag_exp0 (n : Nat) : mag n 0 = n := by
  simp [mag, pow2_zero]

theorem mag_pow52_exp1 : mag (2 ^ 52) 1 = (2 ^ 53 : Nat) := by
  simp only [mag, pow2_one]
  have h : ((2 ^ 52 : Nat) : Rat) * 2 = ((2 ^ 52 * 2 : Nat) : Rat) := by
    rw [Rat.natCast_mul]
    rfl
  rw [h, ← Nat.pow_succ]

theorem two_pow_52_lt_53 : 2 ^ 52 < 2 ^ 53 := by
  have hpow : 2 ^ 53 = 2 ^ 52 * 2 := Nat.pow_succ 2 52
  have hlt : 2 ^ 52 < 2 ^ 52 * 2 := by
    have hp : 0 < 2 ^ 52 := Nat.two_pow_pos 52
    omega
  rwa [← hpow] at hlt

theorem isNormal_of_int53_mid {n : Nat} (hlo : 2 ^ 52 ≤ n) (hhi : n < 2 ^ 53) :
    IsNormal n 0 := by
  refine ⟨?_, ?_, hlo, hhi⟩
  · simp [minExponent_spec64]
  · simp [overflowExponent]

theorem isNormal_of_int53_max : IsNormal (2 ^ 52) 1 := by
  refine ⟨?_, ?_, Nat.le_refl _, two_pow_52_lt_53⟩
  · simp [minExponent_spec64]
  · simp [overflowExponent]

theorem isNormal_of_int53_small {n : Nat} (hpos : 0 < n) (hhi : n < 2 ^ 52) :
    IsNormal (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int)) := by
  have hne : n ≠ 0 := Nat.ne_of_gt hpos
  have hlog : n.log2 + 1 ≤ 53 := by
    have : n.log2 < 52 := log2_lt_52 hpos hhi
    omega
  have ⟨hmlo, hmhi⟩ := mul_pow_log_range hne hlog
  have hk : 53 - (n.log2 + 1) = 52 - n.log2 := by omega
  rw [hk] at hmlo hmhi
  refine ⟨?_, ?_, hmlo, hmhi⟩
  · simp [minExponent_spec64]
    omega
  · simp [overflowExponent]
    omega

theorem signedVal_pos_int53_small {n : Nat} (_hpos : 0 < n) (_hhi : n < 2 ^ 52) :
    signedVal .positive (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int)) = n := by
  simp only [signedVal]
  have := mag_shiftLeft n (52 - n.log2) 0
  rw [Int.zero_sub] at this
  rw [this, mag_exp0]

theorem pack_int53 (s : Sign) {n : Nat} (hpos : 0 < n) (hn : n ≤ 2 ^ 53) :
    ∃ c, bitsToRat? c = some
      (match s with
       | .positive => (n : Rat)
       | .negative => - (n : Rat)) := by
  cases Nat.lt_or_ge n (2 ^ 52) with
  | inl hsmall =>
    have hm : 0 < n <<< (52 - n.log2) := by
      have : 0 < 2 ^ (52 - n.log2) := Nat.two_pow_pos _
      rw [Nat.shiftLeft_eq]
      exact Nat.mul_pos hpos this
    have hc : IsCanonicalFinite (n <<< (52 - n.log2))
        (-((52 - n.log2 : Nat) : Int)) :=
      Or.inr (isNormal_of_int53_small hpos hsmall)
    refine ⟨packDirected false
        (.finite s (n <<< (52 - n.log2)) (-((52 - n.log2 : Nat) : Int)) hm), ?_⟩
    rw [bitsToRat?_packDirected_canonical false s hm hc]
    apply congrArg some
    cases s with
    | positive => exact signedVal_pos_int53_small hpos hsmall
    | negative =>
      simp only [signedVal]
      exact congrArg (fun q => -q) (signedVal_pos_int53_small hpos hsmall)
  | inr hge =>
    cases Nat.lt_or_eq_of_le hn with
    | inl hlt =>
      have hc : IsCanonicalFinite n 0 := Or.inr (isNormal_of_int53_mid hge hlt)
      refine ⟨packDirected false (.finite s n 0 hpos), ?_⟩
      rw [bitsToRat?_packDirected_canonical false s hpos hc]
      apply congrArg some
      cases s with
      | positive => simp [signedVal, mag_exp0]
      | negative => simp [signedVal, mag_exp0]
    | inr heq =>
      have hm : 0 < 2 ^ 52 := Nat.two_pow_pos 52
      have hc : IsCanonicalFinite (2 ^ 52) 1 := Or.inr isNormal_of_int53_max
      refine ⟨packDirected false (.finite s (2 ^ 52) 1 hm), ?_⟩
      rw [bitsToRat?_packDirected_canonical false s hm hc]
      apply congrArg some
      cases s with
      | positive =>
        simp only [signedVal]
        rw [heq]
        exact mag_pow52_exp1
      | negative =>
        simp only [signedVal]
        rw [heq]
        exact congrArg (fun q => -q) mag_pow52_exp1

theorem nat_le_pow53_representable (n : Nat) (hn : n ≤ 2 ^ 53) :
    ∃ c, bitsToRat? c = some (n : Rat) := by
  cases Nat.eq_zero_or_pos n with
  | inl h0 =>
    subst h0
    exact ⟨packDirected false (.zero .positive), bitsToRat?_packDirected_zero false .positive⟩
  | inr hpos =>
    exact pack_int53 .positive hpos hn

theorem int_le_pow53_representable (n : Int) (hn : n.natAbs ≤ 2 ^ 53) :
    ∃ c, bitsToRat? c = some (n : Rat) := by
  by_cases h0 : n = 0
  · subst h0
    exact ⟨packDirected false (.zero .positive), bitsToRat?_packDirected_zero false .positive⟩
  · have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr h0
    cases Int.lt_or_le n 0 with
    | inl hneg =>
      have : n = - (n.natAbs : Int) := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hneg)
      rw [this, Rat.intCast_neg, Rat.intCast_natCast]
      exact pack_int53 .negative hpos hn
    | inr hnonneg =>
      have : (n.natAbs : Int) = n := Int.natAbs_of_nonneg hnonneg
      rw [← this, Rat.intCast_natCast]
      exact pack_int53 .positive hpos hn

/-! ### Integer corollary of `add_exact` -/

theorem add_exact_int {a b : UInt64} {na nb : Int}
    (ha : bitsToRat? a = some (na : Rat)) (hb : bitsToRat? b = some (nb : Rat))
    (_hna : na.natAbs ≤ 2 ^ 53) (_hnb : nb.natAbs ≤ 2 ^ 53)
    (hsum : (na + nb).natAbs ≤ 2 ^ 53) :
    bitsToRat? (addDown a b) = some ((na + nb : Int) : Rat) ∧
    bitsToRat? (addUp a b) = some ((na + nb : Int) : Rat) := by
  rcases int_le_pow53_representable (na + nb) hsum with ⟨c, hc⟩
  have hcast : ((na : Rat) + (nb : Rat)) = ((na + nb : Int) : Rat) :=
    (Rat.intCast_add na nb).symm
  have hrep : ∃ c, bitsToRat? c = some ((na : Rat) + (nb : Rat)) :=
    ⟨c, hc.trans (congrArg some hcast.symm)⟩
  have hadd := add_exact ha hb hrep
  rw [hcast] at hadd
  exact hadd

end Interval64Proofs.ExactAdd
