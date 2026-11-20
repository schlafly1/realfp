/-
Directed rounding encloses a value that may sit strictly between two
consecutive dyadics (`Accuracy.inexact` residuals from `divCore`/`sqrtCore`).
-/
import Interval64Proofs.RoundDirected
import Interval64Proofs.Canonical
import Interval64Proofs.PackFinite

namespace Interval64Proofs.RoundInexact

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Canonical
open Interval64Proofs.PackFinite
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Shift lemmas for an arbitrary initial accuracy -/

theorem ofMantissaAndAccuracy_mantissa (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem shiftRight_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa >>> k := by
  induction k with
  | zero =>
    rw [shiftRight_zero, Nat.shiftRight_zero]
  | succ k ih =>
    rw [shiftRight_succ, shiftRightOne_mantissa, ih, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (2 ^ k)]

theorem shiftRight_of_acc_mantissa (m k : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> k).mantissa = m >>> k := by
  rw [shiftRight_mantissa, ofMantissaAndAccuracy_mantissa]

theorem ofMantissaAndAccuracy_inexact_ne_exact (m : Nat) (o : Ordering) :
    (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)).accuracy ≠ .exact := by
  cases o <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy]

theorem shiftRightOne_preserves_inexact (em : ExtendedMantissa)
    (h : em.accuracy ≠ .exact) :
    (ExtendedMantissa.shiftRightOne em).accuracy ≠ .exact := by
  intro hex
  have hst : (ExtendedMantissa.shiftRightOne em).roundBit = false ∧
      (ExtendedMantissa.shiftRightOne em).stickyBit = false :=
    (accuracy_eq_exact_iff _).mp hex
  have hbits : em.roundBit = false ∧ em.stickyBit = false := by
    simp [ExtendedMantissa.shiftRightOne] at hst
    cases hr : em.roundBit <;> cases hs : em.stickyBit
    · exact ⟨rfl, rfl⟩
    · simp [hr, hs] at hst
    · simp [hr, hs] at hst
    · simp [hr, hs] at hst
  exact h ((accuracy_eq_exact_iff em).mpr hbits)

theorem shiftRight_of_inexact_accuracy (m k : Nat) (o : Ordering) :
    ∃ o', (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o) >>> k).accuracy =
      .inexact o' := by
  induction k with
  | zero =>
    refine ⟨o, ?_⟩
    rw [shiftRight_zero]
    cases o <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy]
  | succ k ih =>
    rcases ih with ⟨o₁, ho₁⟩
    rw [shiftRight_succ]
    have hne :
        (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o) >>> k).accuracy ≠
          .exact := by
      rw [ho₁]
      intro h
      cases h
    have hne' := shiftRightOne_preserves_inexact _ hne
    cases hacc : (ExtendedMantissa.shiftRightOne
        (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o) >>> k)).accuracy with
    | exact => exact (hne' hacc).elim
    | inexact o' => exact ⟨o', rfl⟩

/-! ### Magnitude of the next dyadic after a right shift -/

theorem mag_succ_le_shiftRight_succ (m k : Nat) (e : Int) :
    mag (m + 1) e ≤ mag ((m >>> k) + 1) (e + k) := by
  have hdecomp : m = (m >>> k) * 2 ^ k + m % 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact (Nat.div_add_mod m (2 ^ k)).symm
  have hmod : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (Nat.two_pow_pos k)
  have hle : m + 1 ≤ ((m >>> k) + 1) * 2 ^ k := by
    have hsum : m + 1 = (m >>> k) * 2 ^ k + (m % 2 ^ k + 1) := by
      conv => lhs; rw [hdecomp]
      rw [Nat.add_assoc]
    rw [hsum, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.succ_le_of_lt hmod) _
  have hmag : mag (m + 1) e ≤ mag (((m >>> k) + 1) * 2 ^ k) e :=
    mag_le_mag hle
  have : mag (((m >>> k) + 1) * 2 ^ k) e = mag ((m >>> k) + 1) (e + k) :=
    mag_mul_two_pow_add _ _ _
  rwa [this] at hmag

/-! ### Rounding a possibly inexact residual toward ±∞ -/

/-- Magnitude of a signed value: `v` if `s` is positive, `-v` if negative. -/
def signedMag (s : Sign) (v : Rat) : Rat :=
  match s with
  | .positive => v
  | .negative => -v

/-- The true magnitude sits strictly between `m * 2^e` and `(m+1) * 2^e`. -/
def inexactMag (m : Nat) (e : Int) (vmag : Rat) : Prop :=
  mag m e < vmag ∧ vmag < mag (m + 1) e

theorem signedVal_round_lo_inexact (s : Sign) (m k : Nat) (e : Int) (o : Ordering)
    {v : Rat} (hv : inexactMag m e (signedMag s v)) :
    signedVal s
        (roundMantissaDirected
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
          false s
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy)
        (e + k) ≤ v := by
  have hm :
      ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa = m >>> k :=
    shiftRight_of_acc_mantissa m k (.inexact o)
  rcases shiftRight_of_inexact_accuracy m k o with ⟨o', ho'⟩
  cases s with
  | positive =>
    have hr : roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
        false .positive
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa := by
      simp [ho', roundMantissaDirected_inexact, awayFromZero_false_positive]
    rw [hr, hm]
    have hle : mag (m >>> k) (e + k) ≤ mag m e := mag_shiftRight_le m k e
    exact Rat.le_trans hle (Rat.le_of_lt hv.1)
  | negative =>
    have hr : roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
        false .negative
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa + 1 := by
      simp [ho', roundMantissaDirected_inexact, awayFromZero_false_negative]
    rw [hr, hm]
    have hge : mag (m + 1) e ≤ mag ((m >>> k) + 1) (e + k) :=
      mag_succ_le_shiftRight_succ m k e
    have hlt : -mag ((m >>> k) + 1) (e + k) ≤ -mag (m + 1) e :=
      (Rat.neg_le_neg_iff).mpr hge
    have hlt' : -mag (m + 1) e < v := by
      have hvm : signedMag .negative v = -v := rfl
      have : mag (m + 1) e > -v := by
        simpa [hvm] using hv.2
      have : -mag (m + 1) e < -(-v) := (Rat.neg_lt_neg_iff).mpr this
      simpa [Rat.neg_neg] using this
    exact Rat.le_trans hlt (Rat.le_of_lt hlt')

theorem signedVal_round_hi_inexact (s : Sign) (m k : Nat) (e : Int) (o : Ordering)
    {v : Rat} (hv : inexactMag m e (signedMag s v)) :
    v ≤
      signedVal s
        (roundMantissaDirected
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
          true s
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy)
        (e + k) := by
  have hm :
      ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa = m >>> k :=
    shiftRight_of_acc_mantissa m k (.inexact o)
  rcases shiftRight_of_inexact_accuracy m k o with ⟨o', ho'⟩
  cases s with
  | positive =>
    have hr : roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
        true .positive
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa + 1 := by
      simp [ho', roundMantissaDirected_inexact, awayFromZero_true_positive]
    rw [hr, hm]
    have hge : mag (m + 1) e ≤ mag ((m >>> k) + 1) (e + k) :=
      mag_succ_le_shiftRight_succ m k e
    exact Rat.le_trans (Rat.le_of_lt hv.2) hge
  | negative =>
    have hr : roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
        true .negative
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa := by
      simp [ho', roundMantissaDirected_inexact, awayFromZero_true_negative]
    rw [hr, hm]
    have hle : mag (m >>> k) (e + k) ≤ mag m e := mag_shiftRight_le m k e
    have hv' : v < -mag m e := by
      have hvm : signedMag .negative v = -v := rfl
      have : mag m e < -v := by simpa [hvm] using hv.1
      have := (Rat.neg_lt_neg_iff).mpr this
      simpa [Rat.neg_neg] using this
    have hge : -mag m e ≤ -mag (m >>> k) (e + k) := (Rat.neg_le_neg_iff).mpr hle
    exact Rat.le_trans (Rat.le_of_lt hv') hge

/-! ### `firstRounded` for a general accuracy, and `roundDirected` enclosure -/

/-- First shift+round step of `roundDirected`, for any initial accuracy. -/
def firstRoundedAcc (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (up : Bool) :
    Nat × Int :=
  let p :=
    match acc with
    | .exact => decreaseExponent m e (spec64.targetExponent (totalExponent m e))
    | .inexact _ => (m, e)
  let sh := shiftToTargetExponent spec64 p.1 p.2 acc
  (roundMantissaDirected sh.1.mantissa up s sh.1.accuracy, sh.2)

theorem firstRoundedAcc_exact (s : Sign) (m : Nat) (e : Int) (up : Bool) :
    firstRoundedAcc s m e .exact up = firstRounded s m e up :=
  rfl

theorem shiftToTargetExponent_em (spec : Format) (m : Nat) (e : Int) (acc : Accuracy) :
    (shiftToTargetExponent spec m e acc).1 =
      ExtendedMantissa.ofMantissaAndAccuracy m acc >>>
        (spec.targetExponent (totalExponent m e) - e).toNat :=
  rfl

theorem shiftToTargetExponent_exp (spec : Format) (m : Nat) (e : Int) (acc : Accuracy) :
    (shiftToTargetExponent spec m e acc).2 =
      e + (spec.targetExponent (totalExponent m e) - e).toNat :=
  rfl

theorem shiftToTarget_exponent_ge_min_acc (m : Nat) (e : Int) (acc : Accuracy) :
    spec64.minExponent ≤ (shiftToTargetExponent spec64 m e acc).2 := by
  rw [shiftToTargetExponent_exp, add_toNat_sub]
  exact Int.le_trans (targetExponent_ge_min _) (Int.le_max_right _ _)

theorem shiftToTarget_mantissa_lt_acc (m : Nat) (e : Int) (acc : Accuracy) :
    (shiftToTargetExponent spec64 m e acc).1.mantissa < 2 ^ 53 := by
  rw [shiftToTargetExponent_em, shiftRight_of_acc_mantissa]
  simpa [shiftToTargetExponent_exact_mantissa] using shiftToTarget_mantissa_lt m e

theorem rounded_le_pow53_acc (s : Sign) (up : Bool) (m k : Nat) (acc : Accuracy)
    (hm : m >>> k < 2 ^ 53) :
    roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m acc) >>> k).mantissa
        up s
        ((ExtendedMantissa.ofMantissaAndAccuracy m acc) >>> k).accuracy ≤
      2 ^ 53 := by
  have hm' :
      ((ExtendedMantissa.ofMantissaAndAccuracy m acc) >>> k).mantissa = m >>> k :=
    shiftRight_of_acc_mantissa m k acc
  cases hacc : ((ExtendedMantissa.ofMantissaAndAccuracy m acc) >>> k).accuracy with
  | exact =>
    simp [hm']
    exact Nat.le_of_lt hm
  | inexact o =>
    simp [roundMantissaDirected_inexact, hm']
    split
    · exact Nat.succ_le_of_lt hm
    · exact Nat.le_of_lt hm

theorem firstRoundedAcc_snd_ge_min (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (up : Bool) :
    spec64.minExponent ≤ (firstRoundedAcc s m e acc up).2 := by
  unfold firstRoundedAcc
  cases acc with
  | exact => exact shiftToTarget_exponent_ge_min _ _
  | inexact o => exact shiftToTarget_exponent_ge_min_acc m e (.inexact o)

theorem firstRoundedAcc_fst_le_pow53 (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (up : Bool) :
    (firstRoundedAcc s m e acc up).1 ≤ 2 ^ 53 := by
  unfold firstRoundedAcc
  cases acc with
  | exact => exact firstRounded_fst_le_pow53 s m e up
  | inexact o =>
    apply rounded_le_pow53_acc (s := s) (up := up) (m := m)
      (k := (spec64.targetExponent (totalExponent m e) - e).toNat)
      (acc := .inexact o)
    simpa [shiftToTargetExponent_em, shiftRight_of_acc_mantissa] using
      shiftToTarget_mantissa_lt m e

theorem signedVal_firstRoundedAcc_lo_inexact (s : Sign) (m : Nat) (e : Int)
    (o : Ordering) {v : Rat}
    (hv : inexactMag m e (signedMag s v)) :
    signedVal s (firstRoundedAcc s m e (.inexact o) false).1
      (firstRoundedAcc s m e (.inexact o) false).2 ≤ v := by
  unfold firstRoundedAcc
  dsimp
  rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
  exact signedVal_round_lo_inexact s m
    (spec64.targetExponent (totalExponent m e) - e).toNat e o hv

theorem signedVal_firstRoundedAcc_hi_inexact (s : Sign) (m : Nat) (e : Int)
    (o : Ordering) {v : Rat}
    (hv : inexactMag m e (signedMag s v)) :
    v ≤
      signedVal s (firstRoundedAcc s m e (.inexact o) true).1
        (firstRoundedAcc s m e (.inexact o) true).2 := by
  unfold firstRoundedAcc
  dsimp
  rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
  exact signedVal_round_hi_inexact s m
    (spec64.targetExponent (totalExponent m e) - e).toNat e o hv

theorem roundDirected_eq_shift_of_rounded_acc (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (up : Bool) :
    roundDirected s m e acc up =
      let r := firstRoundedAcc s m e acc up
      let (em, e') := shiftToTargetExponent spec64 r.1 r.2 Accuracy.exact
      if h : em.mantissa = 0 then
        .zero s
      else
        .finite s em.mantissa e' (Nat.pos_of_ne_zero h) := by
  unfold roundDirected firstRoundedAcc
  cases acc <;> rfl

theorem shiftToTarget_short_ne_zero_of_first {s : Sign} {m : Nat} {e : Int}
    {acc : Accuracy} {up : Bool}
    (h0 : (firstRoundedAcc s m e acc up).1 ≠ 0) :
    (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
      (firstRoundedAcc s m e acc up).2 Accuracy.exact).1.mantissa ≠ 0 :=
  shiftToTarget_short_ne_zero
    (firstRoundedAcc_snd_ge_min s m e acc up)
    (firstRoundedAcc_fst_le_pow53 s m e acc up) h0

theorem shiftToTarget_short_zero_of_first {s : Sign} {m : Nat} {e : Int}
    {acc : Accuracy} {up : Bool}
    (h0 : (firstRoundedAcc s m e acc up).1 = 0) :
    (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
      (firstRoundedAcc s m e acc up).2 Accuracy.exact).1.mantissa = 0 := by
  have he := firstRoundedAcc_snd_ge_min s m e acc up
  rw [h0, shiftToTargetExponent_exact_mantissa, shiftAmount_of_short he (by decide),
    Nat.shiftRight_zero]

/-- `roundDirected` toward −∞ encloses a value whose magnitude is either
    exactly `m * 2^e`, or strictly between `m * 2^e` and `(m+1) * 2^e`. -/
theorem roundDirected_lo_acc (s : Sign) (m : Nat) (e : Int) (acc : Accuracy)
    (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o →
      inexactMag m e (signedMag s v)) :
    loEncloses? (toEVal (roundDirected s m e acc false)) v := by
  rw [roundDirected_eq_shift_of_rounded_acc]
  have he := firstRoundedAcc_snd_ge_min s m e acc false
  have hm := firstRoundedAcc_fst_le_pow53 s m e acc false
  have hv : signedVal s (firstRoundedAcc s m e acc false).1
      (firstRoundedAcc s m e acc false).2 ≤ v := by
    cases hacc : acc with
    | exact =>
      have : v = signedVal s m e := hex hacc
      rw [this, firstRoundedAcc_exact]
      exact signedVal_firstRounded_lo s m e
    | inexact o =>
      exact signedVal_firstRoundedAcc_lo_inexact s m e o (hin o hacc)
  by_cases h0 : (firstRoundedAcc s m e acc false).1 = 0
  · have hshift0 := shiftToTarget_short_zero_of_first h0
    dsimp
    rw [dite_eq_left hshift0]
    have hz : signedVal s 0 (firstRoundedAcc s m e acc false).2 = 0 :=
      signedVal_zero s _
    have hv0 : (0 : Rat) ≤ v := by
      rw [← hz, ← h0]
      exact hv
    simpa [loEncloses?, toEVal] using hv0
  · have hne := shiftToTarget_short_ne_zero_of_first h0
    dsimp
    rw [dite_eq_right hne]
    have hpres := signedVal_shiftToTarget_short s he hm
    have : signedVal s
        (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc false).1
          (firstRoundedAcc s m e acc false).2 Accuracy.exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc false).1
          (firstRoundedAcc s m e acc false).2 Accuracy.exact).2 ≤ v := by
      rwa [hpres]
    simpa [loEncloses?, toEVal] using this

theorem roundDirected_hi_acc (s : Sign) (m : Nat) (e : Int) (acc : Accuracy)
    (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o →
      inexactMag m e (signedMag s v)) :
    hiEncloses? (toEVal (roundDirected s m e acc true)) v := by
  rw [roundDirected_eq_shift_of_rounded_acc]
  have he := firstRoundedAcc_snd_ge_min s m e acc true
  have hm := firstRoundedAcc_fst_le_pow53 s m e acc true
  have hv : v ≤ signedVal s (firstRoundedAcc s m e acc true).1
      (firstRoundedAcc s m e acc true).2 := by
    cases hacc : acc with
    | exact =>
      have : v = signedVal s m e := hex hacc
      rw [this, firstRoundedAcc_exact]
      exact signedVal_firstRounded_hi s m e
    | inexact o =>
      exact signedVal_firstRoundedAcc_hi_inexact s m e o (hin o hacc)
  by_cases h0 : (firstRoundedAcc s m e acc true).1 = 0
  · have hshift0 := shiftToTarget_short_zero_of_first h0
    dsimp
    rw [dite_eq_left hshift0]
    have hz : signedVal s 0 (firstRoundedAcc s m e acc true).2 = 0 :=
      signedVal_zero s _
    have hv0 : v ≤ 0 := by
      rw [← hz, ← h0]
      exact hv
    simpa [hiEncloses?, toEVal] using hv0
  · have hne := shiftToTarget_short_ne_zero_of_first h0
    dsimp
    rw [dite_eq_right hne]
    have hpres := signedVal_shiftToTarget_short s he hm
    have : v ≤ signedVal s
        (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc true).1
          (firstRoundedAcc s m e acc true).2 Accuracy.exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc true).1
          (firstRoundedAcc s m e acc true).2 Accuracy.exact).2 := by
      rwa [hpres]
    simpa [hiEncloses?, toEVal] using this

theorem roundDirected_zero_or_shaped_acc (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (up : Bool)
    (hnorm : (firstRoundedAcc s m e acc up).1 ≠ 0 →
      (firstRoundedAcc s m e acc up).2 = spec64.minExponent ∨
        2 ^ 52 ≤ (firstRoundedAcc s m e acc up).1) :
    (∃ z, roundDirected s m e acc up = .zero z) ∨
      (∃ m' e' h, roundDirected s m e acc up = .finite s m' e' h ∧
          (IsSubnormal m' e' ∨ IsNormal m' e' ∨ IsOverflowNormal m' e')) := by
  rw [roundDirected_eq_shift_of_rounded_acc]
  have he : spec64.minExponent ≤ (firstRoundedAcc s m e acc up).2 :=
    firstRoundedAcc_snd_ge_min s m e acc up
  have hle : (firstRoundedAcc s m e acc up).1 ≤ 2 ^ 53 :=
    firstRoundedAcc_fst_le_pow53 s m e acc up
  by_cases h0 : (firstRoundedAcc s m e acc up).1 = 0
  · have hshift0 := shiftToTarget_short_zero_of_first h0
    dsimp
    rw [dite_eq_left hshift0]
    refine Or.inl ⟨s, rfl⟩
  · have hne := shiftToTarget_short_ne_zero_of_first h0
    dsimp
    rw [dite_eq_right hne]
    refine Or.inr ?_
    refine ⟨(shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
        (firstRoundedAcc s m e acc up).2 Accuracy.exact).1.mantissa,
      (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
        (firstRoundedAcc s m e acc up).2 Accuracy.exact).2,
      Nat.pos_of_ne_zero hne, rfl, ?_⟩
    cases Nat.lt_or_eq_of_le hle with
    | inl hlt =>
      have hk0 : (spec64.targetExponent (totalExponent (firstRoundedAcc s m e acc up).1
          (firstRoundedAcc s m e acc up).2) - (firstRoundedAcc s m e acc up).2).toNat = 0 :=
        shiftAmount_of_short he hlt
      have hmnt : (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
          (firstRoundedAcc s m e acc up).2 Accuracy.exact).1.mantissa =
          (firstRoundedAcc s m e acc up).1 := by
        rw [shiftToTargetExponent_exact_mantissa, hk0, Nat.shiftRight_zero]
      have hexp : (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
          (firstRoundedAcc s m e acc up).2 Accuracy.exact).2 =
          (firstRoundedAcc s m e acc up).2 := by
        rw [shiftToTargetExponent_exact_exponent, hk0, Int.natCast_zero, Int.add_zero]
      rw [hmnt, hexp]
      cases hnorm h0 with
      | inl hmin =>
        by_cases hsub : (firstRoundedAcc s m e acc up).1 < 2 ^ 52
        · exact Or.inl ⟨hmin, Nat.pos_of_ne_zero h0, hsub⟩
        · have hge : 2 ^ 52 ≤ (firstRoundedAcc s m e acc up).1 := Nat.le_of_not_lt hsub
          have hminle : spec64.minExponent ≤ (firstRoundedAcc s m e acc up).2 :=
            Int.le_of_eq hmin.symm
          have hovlt : (firstRoundedAcc s m e acc up).2 < overflowExponent := by
            rw [hmin]
            simp [minExponent_spec64, overflowExponent]
          exact Or.inr (Or.inl ⟨hminle, hovlt, hge, hlt⟩)
      | inr hge =>
        by_cases hov : overflowExponent ≤ (firstRoundedAcc s m e acc up).2
        · exact Or.inr (Or.inr ⟨hov, hge, hlt⟩)
        · exact Or.inr (Or.inl ⟨he, Int.lt_of_not_ge hov, hge, hlt⟩)
    | inr heq =>
      have hpow := targetExponent_pow53 (e := (firstRoundedAcc s m e acc up).2) he
      have hmnt : (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
          (firstRoundedAcc s m e acc up).2 Accuracy.exact).1.mantissa = 2 ^ 52 := by
        rw [shiftToTargetExponent_exact_mantissa, heq, hpow]
        have : ((firstRoundedAcc s m e acc up).2 + 1 -
            (firstRoundedAcc s m e acc up).2 : Int).toNat = 1 := by
          have h1 : (firstRoundedAcc s m e acc up).2 + 1 - (firstRoundedAcc s m e acc up).2 =
              (1 : Int) := by omega
          simp [h1]
        rw [this, Nat.shiftRight_eq_div_pow]
      have hexp : (shiftToTargetExponent spec64 (firstRoundedAcc s m e acc up).1
          (firstRoundedAcc s m e acc up).2 Accuracy.exact).2 =
          (firstRoundedAcc s m e acc up).2 + 1 := by
        rw [shiftToTargetExponent_exact_exponent, heq, hpow]
        have : ((firstRoundedAcc s m e acc up).2 + 1 -
            (firstRoundedAcc s m e acc up).2 : Int).toNat = 1 := by
          have h1 : (firstRoundedAcc s m e acc up).2 + 1 - (firstRoundedAcc s m e acc up).2 =
              (1 : Int) := by omega
          simp [h1]
        rw [this]
        rfl
      rw [hmnt, hexp]
      have hge : 2 ^ 52 ≤ 2 ^ 52 := Nat.le_refl _
      have hhi : (2 ^ 52 : Nat) < 2 ^ 53 := by decide
      have he2 : spec64.minExponent ≤ (firstRoundedAcc s m e acc up).2 + 1 :=
        Int.le_trans he (Int.le_add_of_nonneg_right (by decide))
      by_cases hov : overflowExponent ≤ (firstRoundedAcc s m e acc up).2 + 1
      · exact Or.inr (Or.inr ⟨hov, hge, hhi⟩)
      · exact Or.inr (Or.inl ⟨he2, Int.lt_of_not_ge hov, hge, hhi⟩)

end Interval64Proofs.RoundInexact
