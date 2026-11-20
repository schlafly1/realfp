/-
`roundDirected` and `normalizeDirected` enclose an exact dyadic value.
-/
import Interval64Proofs.Round

namespace Interval64Proofs.RoundDirected

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Float.Model
open Float.Model.UnpackedFloat

theorem targetExponent_ge_min (te : Int) :
    spec64.minExponent ≤ spec64.targetExponent te :=
  Int.le_max_right _ _

theorem shiftToTarget_exponent_ge_min (m : Nat) (e : Int) :
    spec64.minExponent ≤ (shiftToTargetExponent spec64 m e .exact).2 := by
  rw [shiftToTargetExponent_exact_exponent, add_toNat_sub]
  exact Int.le_trans (targetExponent_ge_min _) (Int.le_max_right _ _)

theorem log2_mul_two_pow (m k : Nat) (h : m ≠ 0) :
    (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero h (Nat.ne_of_gt (Nat.two_pow_pos k))
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (m * 2 ^ k) 2, Nat.log2_two_mul hne, ih,
      Nat.add_assoc]

theorem totalExponent_decreaseExponent {m : Nat} {e t : Int} (hm : m ≠ 0) :
    totalExponent (decreaseExponent m e t).1 (decreaseExponent m e t).2 =
      totalExponent m e := by
  simp only [decreaseExponent, totalExponent]
  rw [Nat.shiftLeft_eq, log2_mul_two_pow m _ hm]
  omega

theorem toNat_eq_max (n : Int) : (n.toNat : Int) = max n 0 := by
  by_cases h : 0 ≤ n
  · rw [Int.toNat_of_nonneg h, Int.max_eq_left h]
  · have h' : n ≤ 0 := Int.le_of_not_le h
    rw [Int.toNat_of_nonpos h', Int.max_eq_right h']
    simp

/-- After shifting an exact value to the format target, the mantissa has
    fewer than `2^53` units. -/
theorem shiftToTarget_mantissa_lt (m : Nat) (e : Int) :
    (shiftToTargetExponent spec64 m e .exact).1.mantissa < 2 ^ 53 := by
  rw [shiftToTargetExponent_exact_mantissa]
  let k := (spec64.targetExponent (totalExponent m e) - e).toNat
  have hiff : m >>> k < 2 ^ 53 ↔ m < 2 ^ 53 * 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k))
  refine hiff.mpr ?_
  rw [← Nat.pow_add]
  have hlt : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  refine Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ?_)
  have hbits : (spec64.mantissaBits : Int) = 53 := by
    simp [mantissaBits_spec64]
  have hge : (m.log2 + 1 : Int) ≤ 53 + k := by
    have hk : (k : Int) = max (spec64.targetExponent (totalExponent m e) - e) 0 :=
      toNat_eq_max _
    have ht :
        totalExponent m e - spec64.mantissaBits - e ≤
          spec64.targetExponent (totalExponent m e) - e := by
      have hmax :
          totalExponent m e - spec64.mantissaBits ≤
            spec64.targetExponent (totalExponent m e) := by
        unfold Format.targetExponent
        exact Int.le_max_left _ _
      omega
    have hte : totalExponent m e - spec64.mantissaBits - e = (m.log2 + 1 : Nat) - 53 := by
      unfold totalExponent
      omega
    omega
  exact Int.ofNat_le.mp (by
    have : ((m.log2 + 1 : Nat) : Int) ≤ ((53 + k : Nat) : Int) := by
      simpa using hge
    exact this)

theorem rounded_le_pow53 (s : Sign) (up : Bool) (m k : Nat)
    (hm : m >>> k < 2 ^ 53) :
    roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa
        up s
        ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy ≤
      2 ^ 53 := by
  have hm' :
      ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa = m >>> k :=
    shiftRight_exact_mantissa m k
  cases hacc : ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy with
  | exact =>
    simp [hm']
    exact Nat.le_of_lt hm
  | inexact o =>
    simp [roundMantissaDirected_inexact, hm']
    split
    · exact Nat.succ_le_of_lt hm
    · exact Nat.le_of_lt hm

theorem shiftToTarget_short_ne_zero {m : Nat} {e : Int}
    (he : spec64.minExponent ≤ e) (hm : m ≤ 2 ^ 53) (h0 : m ≠ 0) :
    (shiftToTargetExponent spec64 m e .exact).1.mantissa ≠ 0 := by
  have hmnt := shiftToTargetExponent_exact_mantissa spec64 m e
  rw [hmnt]
  cases Nat.lt_or_eq_of_le hm with
  | inl hlt =>
    rw [shiftAmount_of_short he hlt, Nat.shiftRight_zero]
    exact h0
  | inr heq =>
    subst heq
    rw [targetExponent_pow53 he]
    have : (e + 1 - e : Int).toNat = 1 := by
      have : e + 1 - e = (1 : Int) := by omega
      simp [this]
    rw [this, Nat.shiftRight_eq_div_pow]
    decide

/-! ### Enclosure of `roundDirected` on exact values -/
theorem shiftToTargetExponent_exact_em (spec : Format) (m : Nat) (e : Int) :
    (shiftToTargetExponent spec m e .exact).1 =
      ExtendedMantissa.ofMantissaAndAccuracy m .exact >>>
        (spec.targetExponent (totalExponent m e) - e).toNat :=
  rfl


def firstRounded (s : Sign) (m : Nat) (e : Int) (up : Bool) : Nat × Int :=
  let p := decreaseExponent m e (spec64.targetExponent (totalExponent m e))
  let sh := shiftToTargetExponent spec64 p.1 p.2 Accuracy.exact
  (roundMantissaDirected sh.1.mantissa up s sh.1.accuracy, sh.2)

theorem firstRounded_snd_ge_min (s : Sign) (m : Nat) (e : Int) (up : Bool) :
    spec64.minExponent ≤ (firstRounded s m e up).2 := by
  unfold firstRounded
  exact shiftToTarget_exponent_ge_min _ _

theorem firstRounded_fst_le_pow53 (s : Sign) (m : Nat) (e : Int) (up : Bool) :
    (firstRounded s m e up).1 ≤ 2 ^ 53 := by
  unfold firstRounded
  let t := spec64.targetExponent (totalExponent m e)
  let p := decreaseExponent m e t
  have hlt := shiftToTarget_mantissa_lt p.1 p.2
  have hmnt := shiftToTargetExponent_exact_mantissa spec64 p.1 p.2
  have : (shiftToTargetExponent spec64 p.1 p.2 Accuracy.exact).1.mantissa =
      p.1 >>> (spec64.targetExponent (totalExponent p.1 p.2) - p.2).toNat := hmnt
  -- reuse rounded_le_pow53 with k = (target(p)-e0).toNat, after identifying em
  apply rounded_le_pow53 (s := s) (up := up) (m := p.1)
    (k := (spec64.targetExponent (totalExponent p.1 p.2) - p.2).toNat)
  simpa [shiftToTargetExponent_exact_mantissa] using hlt

theorem signedVal_firstRounded_lo (s : Sign) (m : Nat) (e : Int) :
    signedVal s (firstRounded s m e false).1 (firstRounded s m e false).2 ≤
      signedVal s m e := by
  unfold firstRounded
  dsimp
  rw [shiftToTargetExponent_exact_em, shiftToTargetExponent_exact_exponent]
  generalize hw : decreaseExponent m e (spec64.targetExponent (totalExponent m e)) = p
  refine Rat.le_trans (signedVal_round_lo s p.1
      (spec64.targetExponent (totalExponent p.1 p.2) - p.2).toNat p.2) ?_
  rw [← hw, decreaseExponent_signedVal]
  exact Rat.le_refl

theorem signedVal_firstRounded_hi (s : Sign) (m : Nat) (e : Int) :
    signedVal s m e ≤
      signedVal s (firstRounded s m e true).1 (firstRounded s m e true).2 := by
  unfold firstRounded
  dsimp
  rw [shiftToTargetExponent_exact_em, shiftToTargetExponent_exact_exponent]
  generalize hw : decreaseExponent m e (spec64.targetExponent (totalExponent m e)) = p
  refine Rat.le_trans ?_ (signedVal_round_hi s p.1
      (spec64.targetExponent (totalExponent p.1 p.2) - p.2).toNat p.2)
  rw [← hw, decreaseExponent_signedVal]
  exact Rat.le_refl

theorem roundDirected_eq_shift_of_rounded (s : Sign) (m : Nat) (e : Int) (up : Bool) :
    roundDirected s m e .exact up =
      let r := firstRounded s m e up
      let (em, e') := shiftToTargetExponent spec64 r.1 r.2 Accuracy.exact
      if h : em.mantissa = 0 then
        .zero s
      else
        .finite s em.mantissa e' (Nat.pos_of_ne_zero h) := by
  unfold roundDirected firstRounded
  rfl

theorem signedVal_zero (s : Sign) (e : Int) : signedVal s 0 e = 0 := by
  cases s <;> simp [signedVal, mag]

theorem roundDirected_lo (s : Sign) (m : Nat) (e : Int) :
    loEncloses? (toEVal (roundDirected s m e .exact false)) (signedVal s m e) := by
  rw [roundDirected_eq_shift_of_rounded]
  have he := firstRounded_snd_ge_min s m e false
  have hm := firstRounded_fst_le_pow53 s m e false
  have hv := signedVal_firstRounded_lo s m e
  by_cases h0 : (firstRounded s m e false).1 = 0
  · have hshift0 :
        (shiftToTargetExponent spec64 (firstRounded s m e false).1
          (firstRounded s m e false).2 Accuracy.exact).1.mantissa = 0 := by
      rw [h0, shiftToTargetExponent_exact_mantissa, shiftAmount_of_short he (by decide),
        Nat.shiftRight_zero]
    dsimp
    rw [dite_eq_left hshift0]
    have hz : signedVal s 0 (firstRounded s m e false).2 = 0 :=
      signedVal_zero s _
    have hv0 : (0 : Rat) ≤ signedVal s m e := by
      rw [← hz, ← h0]
      exact hv
    simpa [loEncloses?, toEVal] using hv0
  · have hne :
        (shiftToTargetExponent spec64 (firstRounded s m e false).1
          (firstRounded s m e false).2 Accuracy.exact).1.mantissa ≠ 0 :=
      shiftToTarget_short_ne_zero he hm h0
    dsimp
    rw [dite_eq_right hne]
    have hpres := signedVal_shiftToTarget_short s he hm
    have : signedVal s
        (shiftToTargetExponent spec64 (firstRounded s m e false).1
          (firstRounded s m e false).2 Accuracy.exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRounded s m e false).1
          (firstRounded s m e false).2 Accuracy.exact).2 ≤
        signedVal s m e := by
      rwa [hpres]
    simpa [loEncloses?, toEVal] using this

theorem roundDirected_hi (s : Sign) (m : Nat) (e : Int) :
    hiEncloses? (toEVal (roundDirected s m e .exact true)) (signedVal s m e) := by
  rw [roundDirected_eq_shift_of_rounded]
  have he := firstRounded_snd_ge_min s m e true
  have hm := firstRounded_fst_le_pow53 s m e true
  have hv := signedVal_firstRounded_hi s m e
  by_cases h0 : (firstRounded s m e true).1 = 0
  · have hshift0 :
        (shiftToTargetExponent spec64 (firstRounded s m e true).1
          (firstRounded s m e true).2 Accuracy.exact).1.mantissa = 0 := by
      rw [h0, shiftToTargetExponent_exact_mantissa, shiftAmount_of_short he (by decide),
        Nat.shiftRight_zero]
    dsimp
    rw [dite_eq_left hshift0]
    have hz : signedVal s 0 (firstRounded s m e true).2 = 0 :=
      signedVal_zero s _
    have hv0 : signedVal s m e ≤ 0 := by
      rw [← hz, ← h0]
      exact hv
    simpa [hiEncloses?, toEVal] using hv0
  · have hne :
        (shiftToTargetExponent spec64 (firstRounded s m e true).1
          (firstRounded s m e true).2 Accuracy.exact).1.mantissa ≠ 0 :=
      shiftToTarget_short_ne_zero he hm h0
    dsimp
    rw [dite_eq_right hne]
    have hpres := signedVal_shiftToTarget_short s he hm
    have : signedVal s m e ≤
        signedVal s
          (shiftToTargetExponent spec64 (firstRounded s m e true).1
            (firstRounded s m e true).2 Accuracy.exact).1.mantissa
          (shiftToTargetExponent spec64 (firstRounded s m e true).1
            (firstRounded s m e true).2 Accuracy.exact).2 := by
      rwa [hpres]
    simpa [hiEncloses?, toEVal] using this

theorem normalizeDirected_lo (mant : Int) (e : Int) (z : Sign) :
    loEncloses? (toEVal (normalizeDirected mant e z false))
      ((mant : Rat) * pow2 e) := by
  unfold normalizeDirected
  cases hc : compare mant 0 with
  | lt =>
    -- roundDirected negative (-mant).toNat
    have hlt : mant < 0 := (Int.compare_eq_lt).mp hc
    have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .negative (-mant).toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat, Rat.intCast_neg, ← Rat.neg_mul, Rat.neg_neg]
    have := roundDirected_lo .negative (-mant).toNat e
    -- need loEncloses? of that = signedVal negative = (mant:Rat)*pow2
    simpa [hv] using this
  | eq =>
    have heq : mant = 0 := (Int.compare_eq_eq).mp hc
    simp [heq, loEncloses?, toEVal]
  | gt =>
    have hgt : 0 < mant := (Int.compare_eq_gt).mp hc
    have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .positive mant.toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat]
    have := roundDirected_lo .positive mant.toNat e
    simpa [hv] using this



theorem normalizeDirected_hi (mant : Int) (e : Int) (z : Sign) :
    hiEncloses? (toEVal (normalizeDirected mant e z true))
      ((mant : Rat) * pow2 e) := by
  unfold normalizeDirected
  cases hc : compare mant 0 with
  | lt =>
    have hlt : mant < 0 := (Int.compare_eq_lt).mp hc
    have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .negative (-mant).toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat, Rat.intCast_neg, ← Rat.neg_mul, Rat.neg_neg]
    have := roundDirected_hi .negative (-mant).toNat e
    simpa [hv] using this
  | eq =>
    have heq : mant = 0 := (Int.compare_eq_eq).mp hc
    simp [heq, hiEncloses?, toEVal]
  | gt =>
    have hgt : 0 < mant := (Int.compare_eq_gt).mp hc
    have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .positive mant.toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat]
    have := roundDirected_hi .positive mant.toNat e
    simpa [hv] using this

end Interval64Proofs.RoundDirected
