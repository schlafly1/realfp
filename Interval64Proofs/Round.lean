/-
Directed rounding preserves enclosure of an exact dyadic value.
-/
import Interval64Proofs.Value

namespace Interval64Proofs.Round

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Right-shifting an exact extended mantissa -/

@[simp] theorem ofMantissaAndAccuracy_exact_mantissa (m : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy m .exact).mantissa = m :=
  rfl

@[simp] theorem ofMantissaAndAccuracy_exact_accuracy (m : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy m .exact).accuracy = .exact :=
  rfl

theorem shiftRight_zero (em : ExtendedMantissa) :
    em >>> (0 : Nat) = em :=
  rfl

theorem shiftRight_succ (em : ExtendedMantissa) (k : Nat) :
    em >>> (k + 1) = ExtendedMantissa.shiftRightOne (em >>> k) :=
  rfl

theorem shiftRightOne_mantissa (em : ExtendedMantissa) :
    (ExtendedMantissa.shiftRightOne em).mantissa = em.mantissa / 2 :=
  rfl

theorem shiftRight_exact_mantissa (m k : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa = m >>> k := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    rw [shiftRight_succ, shiftRightOne_mantissa, ih, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (2 ^ k)]

theorem accuracy_eq_exact_iff (em : ExtendedMantissa) :
    em.accuracy = .exact ↔ em.roundBit = false ∧ em.stickyBit = false := by
  rcases em with ⟨_m, rb, sb⟩
  cases rb <;> cases sb <;> simp [ExtendedMantissa.accuracy]

theorem mod_two_bne_false (n : Nat) : (n % 2 != 0) = false ↔ n % 2 = 0 := by
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h => simp [h]
  | inr h => simp [h]

theorem shiftRightOne_accuracy_exact (em : ExtendedMantissa) :
    (ExtendedMantissa.shiftRightOne em).accuracy = .exact ↔
      em.accuracy = .exact ∧ em.mantissa % 2 = 0 := by
  rw [accuracy_eq_exact_iff, accuracy_eq_exact_iff]
  rcases em with ⟨mant, rb, sb⟩
  simp [ExtendedMantissa.shiftRightOne]
  cases rb <;> cases sb <;> simp

theorem two_pow_succ_dvd_iff (m k : Nat) :
    2 ^ (k + 1) ∣ m ↔ 2 ^ k ∣ m ∧ 2 ∣ m / 2 ^ k := by
  constructor
  · intro h
    have hk : 2 ^ k ∣ m :=
      Nat.dvd_trans (by rw [Nat.pow_succ]; exact Nat.dvd_mul_right (2 ^ k) 2) h
    refine ⟨hk, ?_⟩
    rcases h with ⟨t, ht⟩
    have : m / 2 ^ k = 2 * t := by
      rw [ht, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
    rw [this]
    exact Nat.dvd_mul_right 2 t
  · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hdiv : m / 2 ^ k = u := by
      rw [hu, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
    refine ⟨v, ?_⟩
    calc
      m = 2 ^ k * u := hu
      _ = 2 ^ k * (m / 2 ^ k) := by rw [hdiv]
      _ = 2 ^ k * (2 * v) := by rw [hv]
      _ = 2 ^ (k + 1) * v := by
        rw [Nat.pow_succ, Nat.mul_assoc]

theorem mod_two_pow_succ (m k : Nat) :
    m % 2 ^ (k + 1) = 0 ↔ m % 2 ^ k = 0 ∧ (m >>> k) % 2 = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
  exact two_pow_succ_dvd_iff m k

theorem shiftRight_exact_accuracy (m k : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy = .exact ↔
      m % 2 ^ k = 0 := by
  induction k with
  | zero =>
    simp [shiftRight_zero, Nat.mod_one]
  | succ k ih =>
    rw [shiftRight_succ, shiftRightOne_accuracy_exact, ih, shiftRight_exact_mantissa,
      mod_two_pow_succ]

theorem mag_shiftRight_eq (m k : Nat) (e : Int) (h : m % 2 ^ k = 0) :
    mag (m >>> k) (e + k) = mag m e := by
  rw [mag_split m k e, h, mag_zero, Rat.add_zero]

theorem signedVal_shiftRight_eq (s : Sign) (m k : Nat) (e : Int) (h : m % 2 ^ k = 0) :
    signedVal s (m >>> k) (e + k) = signedVal s m e := by
  simp [signedVal, mag_shiftRight_eq m k e h]

/-! ### `roundMantissaDirected` -/

@[simp] theorem roundMantissaDirected_exact (m : Nat) (up : Bool) (s : Sign) :
    roundMantissaDirected m up s .exact = m :=
  rfl

theorem roundMantissaDirected_inexact (m : Nat) (up : Bool) (s : Sign) (o : Ordering) :
    roundMantissaDirected m up s (.inexact o) =
      if awayFromZero up s then m + 1 else m :=
  rfl

theorem awayFromZero_false_positive : awayFromZero false .positive = false := rfl
theorem awayFromZero_false_negative : awayFromZero false .negative = true := rfl
theorem awayFromZero_true_positive : awayFromZero true .positive = true := rfl
theorem awayFromZero_true_negative : awayFromZero true .negative = false := rfl

/-- Rounding toward -∞ never increases a positive magnitude, and increases a
    negative one exactly when the residual is inexact. -/
theorem signedVal_round_lo (s : Sign) (m k : Nat) (e : Int) :
    signedVal s
        (roundMantissaDirected
          ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa
          false s
          ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy)
        (e + k) ≤
      signedVal s m e := by
  let em := (ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k
  have hm : em.mantissa = m >>> k := shiftRight_exact_mantissa m k
  cases s with
  | positive =>
    have hr : roundMantissaDirected em.mantissa false .positive em.accuracy =
        em.mantissa := by
      cases hacc : em.accuracy with
      | exact => simp
      | inexact o => simp [roundMantissaDirected_inexact, awayFromZero_false_positive]
    rw [hr, hm]
    simpa [signedVal] using mag_shiftRight_le m k e
  | negative =>
    by_cases hex : em.accuracy = .exact
    · have hr : roundMantissaDirected em.mantissa false .negative em.accuracy =
          em.mantissa := by
        simp [hex]
      have hrem : m % 2 ^ k = 0 := (shiftRight_exact_accuracy m k).mp hex
      rw [hr, hm, signedVal_shiftRight_eq .negative m k e hrem]
      exact Rat.le_refl
    · have hinex : ∃ o, em.accuracy = .inexact o := by
        cases hacc : em.accuracy with
        | exact => exact absurd hacc hex
        | inexact o => exact ⟨o, rfl⟩
      rcases hinex with ⟨o, ho⟩
      have hr : roundMantissaDirected em.mantissa false .negative em.accuracy =
          em.mantissa + 1 := by
        simp [ho, roundMantissaDirected_inexact, awayFromZero_false_negative]
      have hrem : m % 2 ^ k ≠ 0 := by
        intro hz
        exact hex ((shiftRight_exact_accuracy m k).mpr hz)
      rw [hr, hm]
      have hlt : mag m e < mag ((m >>> k) + 1) (e + k) :=
        mag_lt_shiftRight_succ m k e hrem
      have hlt' :
          signedVal .negative ((m >>> k) + 1) (e + k) < signedVal .negative m e := by
        simpa [signedVal] using (Rat.neg_lt_neg_iff.mpr hlt)
      exact Rat.le_of_lt hlt'

/-- Rounding toward +∞ never decreases a positive magnitude, and never increases
    a negative one. -/
theorem signedVal_round_hi (s : Sign) (m k : Nat) (e : Int) :
    signedVal s m e ≤
      signedVal s
        (roundMantissaDirected
          ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa
          true s
          ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy)
        (e + k) := by
  let em := (ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k
  have hm : em.mantissa = m >>> k := shiftRight_exact_mantissa m k
  cases s with
  | positive =>
    by_cases hex : em.accuracy = .exact
    · have hr : roundMantissaDirected em.mantissa true .positive em.accuracy =
          em.mantissa := by simp [hex]
      have hrem : m % 2 ^ k = 0 := (shiftRight_exact_accuracy m k).mp hex
      rw [hr, hm, signedVal_shiftRight_eq .positive m k e hrem]
      exact Rat.le_refl
    · have hinex : ∃ o, em.accuracy = .inexact o := by
        cases hacc : em.accuracy with
        | exact => exact absurd hacc hex
        | inexact o => exact ⟨o, rfl⟩
      rcases hinex with ⟨o, ho⟩
      have hr : roundMantissaDirected em.mantissa true .positive em.accuracy =
          em.mantissa + 1 := by
        simp [ho, roundMantissaDirected_inexact, awayFromZero_true_positive]
      have hrem : m % 2 ^ k ≠ 0 := by
        intro hz
        exact hex ((shiftRight_exact_accuracy m k).mpr hz)
      rw [hr, hm]
      have hlt : mag m e < mag ((m >>> k) + 1) (e + k) :=
        mag_lt_shiftRight_succ m k e hrem
      exact Rat.le_of_lt (by simpa [signedVal] using hlt)
  | negative =>
    have hr : roundMantissaDirected em.mantissa true .negative em.accuracy =
        em.mantissa := by
      cases hacc : em.accuracy with
      | exact => simp
      | inexact o => simp [roundMantissaDirected_inexact, awayFromZero_true_negative]
    rw [hr, hm]
    -- -mag (m>>>k) (e+k) ≥ -mag m e
    have hle : mag (m >>> k) (e + k) ≤ mag m e := mag_shiftRight_le m k e
    simpa [signedVal] using (neg_le_neg_iff.mpr hle)

/-! ### `shiftToTargetExponent` for exact inputs -/

theorem add_toNat_sub (a b : Int) : a + (b - a).toNat = max a b := by
  by_cases h : a ≤ b
  · have : 0 ≤ b - a := Int.sub_nonneg_of_le h
    rw [Int.toNat_of_nonneg this]
    have : a + (b - a) = b := by omega
    have : max a b = b := Int.max_eq_right h
    omega
  · have hba : b ≤ a := Int.le_of_not_le h
    have hz : (b - a).toNat = 0 := (Int.toNat_sub_eq_zero_iff b a).mpr hba
    simp [hz, Int.max_eq_left hba]

theorem shiftToExponent_fst_mantissa (m : Nat) (e target : Int) (acc : Accuracy) :
    (shiftToExponent m e acc target).1.mantissa =
      (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> (target - e).toNat).mantissa :=
  rfl

theorem shiftToExponent_snd (m : Nat) (e target : Int) (acc : Accuracy) :
    (shiftToExponent m e acc target).2 = e + (target - e).toNat :=
  rfl

theorem shiftToTargetExponent_exact_mantissa (spec : Format) (m : Nat) (e : Int) :
    (shiftToTargetExponent spec m e .exact).1.mantissa =
      m >>> (spec.targetExponent (totalExponent m e) - e).toNat := by
  simp [shiftToTargetExponent, shiftToExponent, shiftRight_exact_mantissa]

theorem shiftToTargetExponent_exact_exponent (spec : Format) (m : Nat) (e : Int) :
    (shiftToTargetExponent spec m e .exact).2 =
      e + (spec.targetExponent (totalExponent m e) - e).toNat :=
  rfl

theorem log2_lt_mantissaBits {m : Nat} (h : m < 2 ^ 53) : m.log2 < 53 ∨ m = 0 := by
  by_cases hz : m = 0
  · exact Or.inr hz
  · exact Or.inl ((Nat.log2_lt hz).mpr h)

theorem targetExponent_le_of_short {m : Nat} {e : Int}
    (he : spec64.minExponent ≤ e) (hm : m < 2 ^ 53) :
    spec64.targetExponent (totalExponent m e) ≤ e := by
  unfold Format.targetExponent totalExponent
  have hlog : (m.log2 + 1 : Int) ≤ 53 := by
    by_cases hz : m = 0
    · subst hz
      simp [Nat.log2_zero]
    · have : m.log2 < 53 := (Nat.log2_lt hz).mpr hm
      omega
  have hbits : (spec64.mantissaBits : Int) = 53 := by
    simp [mantissaBits_spec64]
  have h1 : (m.log2 + 1 : Int) + e - spec64.mantissaBits ≤ e := by omega
  have : max ((m.log2 + 1 : Int) + e - spec64.mantissaBits) spec64.minExponent ≤ e := by
    simp [Int.max_def]
    split <;> assumption
  -- totalExponent uses Nat addition m.log2 + 1 before adding e
  exact this

theorem shiftAmount_of_short {m : Nat} {e : Int}
    (he : spec64.minExponent ≤ e) (hm : m < 2 ^ 53) :
    (spec64.targetExponent (totalExponent m e) - e).toNat = 0 :=
  (Int.toNat_sub_eq_zero_iff _ _).mpr (targetExponent_le_of_short he hm)

theorem targetExponent_pow53 {e : Int} (he : spec64.minExponent ≤ e) :
    spec64.targetExponent (totalExponent (2 ^ 53) e) = e + 1 := by
  unfold Format.targetExponent totalExponent
  rw [Nat.log2_two_pow, mantissaBits_spec64]
  have hs : ((53 : Nat) : Int) + 1 + e - (53 : Nat) = e + 1 := by omega
  rw [hs]
  exact Int.max_eq_left (Int.le_trans he (Int.le_add_of_nonneg_right (by decide)))

/-- A mantissa of at most `2^53`, at an exponent already at least
    `minExponent`, shifts by at most one bit, and the residual is exact. -/
theorem shiftToTarget_short_exact {m : Nat} {e : Int}
    (he : spec64.minExponent ≤ e) (hm : m ≤ 2 ^ 53) :
    ((shiftToTargetExponent spec64 m e .exact).1).accuracy = .exact := by
  rw [shiftToTargetExponent, shiftToExponent]
  have hacc := shiftRight_exact_accuracy m (spec64.targetExponent (totalExponent m e) - e).toNat
  rw [hacc]
  cases Nat.lt_or_eq_of_le hm with
  | inl hlt =>
    rw [shiftAmount_of_short he hlt, Nat.mod_one]
  | inr heq =>
    subst heq
    rw [targetExponent_pow53 he]
    have h1 : e + 1 - e = (1 : Int) := by omega
    rw [h1]
    decide

theorem signedVal_shiftToTarget_short (s : Sign) {m : Nat} {e : Int}
    (he : spec64.minExponent ≤ e) (hm : m ≤ 2 ^ 53) :
    signedVal s ((shiftToTargetExponent spec64 m e .exact).1.mantissa)
        ((shiftToTargetExponent spec64 m e .exact).2) =
      signedVal s m e := by
  have hacc := shiftToTarget_short_exact (m := m) (e := e) he hm
  have hmnt := shiftToTargetExponent_exact_mantissa spec64 m e
  have hexp := shiftToTargetExponent_exact_exponent spec64 m e
  have hrem :
      m % 2 ^ (spec64.targetExponent (totalExponent m e) - e).toNat = 0 :=
    (shiftRight_exact_accuracy _ _).mp (by
      -- accuracy of the shifted em is exact
      simpa [shiftToTargetExponent, shiftToExponent] using hacc)
  rw [hmnt, hexp, signedVal_shiftRight_eq s m _ e hrem]

/-! ### `decreaseExponent` preserves signed value -/

theorem decreaseExponent_signedVal (s : Sign) (m : Nat) (e t : Int) :
    signedVal s (decreaseExponent m e t).1 (decreaseExponent m e t).2 =
      signedVal s m e := by
  simp only [decreaseExponent]
  cases s with
  | positive =>
    simpa [signedVal] using mag_shiftLeft m (e - t).toNat e
  | negative =>
    simpa [signedVal] using congrArg (fun q => -q) (mag_shiftLeft m (e - t).toNat e)


end Interval64Proofs.Round
