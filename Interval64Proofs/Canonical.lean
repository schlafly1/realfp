/-
Shape of `roundDirected` output: zero, a canonical subnormal, a canonical
normal, or a normal that overflows the binary64 exponent range.
-/
import Interval64Proofs.RoundDirected

namespace Interval64Proofs.Canonical

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Float.Model
open Float.Model.UnpackedFloat

/-- Canonical subnormal: exponent is `minExponent`, mantissa fits in 52 bits. -/
def IsSubnormal (m : Nat) (e : Int) : Prop :=
  e = spec64.minExponent ∧ 0 < m ∧ m < 2 ^ 52

/-- Canonical normal that still fits in the exponent field (`e < 972`). -/
def IsNormal (m : Nat) (e : Int) : Prop :=
  spec64.minExponent ≤ e ∧ e < overflowExponent ∧ 2 ^ 52 ≤ m ∧ m < 2 ^ 53

/-- Normal-shaped but exponent overflows binary64 (`e ≥ 972`). -/
def IsOverflowNormal (m : Nat) (e : Int) : Prop :=
  overflowExponent ≤ e ∧ 2 ^ 52 ≤ m ∧ m < 2 ^ 53

def IsCanonicalFinite (m : Nat) (e : Int) : Prop :=
  IsSubnormal m e ∨ IsNormal m e

theorem log2_eq_52 {m : Nat} (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) :
    m.log2 = 52 := by
  have hne : m ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos 52) hlo)
  exact (Nat.log2_eq_iff hne).mpr ⟨hlo, hhi⟩

theorem target_eq_te_sub {m : Nat} {e : Int}
    (h : spec64.minExponent < spec64.targetExponent (totalExponent m e)) :
    spec64.targetExponent (totalExponent m e) =
      totalExponent m e - spec64.mantissaBits := by
  unfold Format.targetExponent
  apply Int.max_eq_left
  cases Int.lt_or_le (totalExponent m e - spec64.mantissaBits) spec64.minExponent with
  | inl hlt =>
    have heq : max (totalExponent m e - spec64.mantissaBits) spec64.minExponent =
        spec64.minExponent := Int.max_eq_right (Int.le_of_lt hlt)
    have : spec64.minExponent < spec64.minExponent := heq ▸ h
    exact absurd this (Int.lt_irrefl _)
  | inr hle =>
    exact hle

theorem decreaseExponent_snd (m : Nat) (e t : Int) :
    (decreaseExponent m e t).2 = min e t := by
  simp only [decreaseExponent]
  have h : ((e - t).toNat : Int) = max (e - t) 0 := toNat_eq_max _
  have : e - max (e - t) 0 = min e t := by omega
  omega

theorem decrease_shift_exponent {m : Nat} {e : Int} (hm : m ≠ 0) :
    (shiftToTargetExponent spec64
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
        .exact).2 =
      spec64.targetExponent (totalExponent m e) := by
  rw [shiftToTargetExponent_exact_exponent, add_toNat_sub,
    totalExponent_decreaseExponent hm, decreaseExponent_snd]
  exact Int.max_eq_right (Int.min_le_right _ _)

theorem te_sub_eq {m : Nat} {e : Int} :
    totalExponent m e - spec64.mantissaBits = (m.log2 + 1 : Nat) + e - 53 := by
  unfold totalExponent
  have : (spec64.mantissaBits : Int) = 53 := by simp [mantissaBits_spec64]
  omega


theorem div_pow_log_range {m : Nat} (hm : m ≠ 0) (h : 53 < m.log2 + 1) :
    2 ^ 52 ≤ m >>> (m.log2 + 1 - 53) ∧ m >>> (m.log2 + 1 - 53) < 2 ^ 53 := by
  have hlo : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
  have hhi : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hle : 53 ≤ m.log2 + 1 := Nat.le_of_lt h
  rw [Nat.shiftRight_eq_div_pow]
  constructor
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    rw [← Nat.pow_add]
    have : 52 + (m.log2 + 1 - 53) = m.log2 := by omega
    rw [this]
    exact hlo
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [← Nat.pow_add]
    have : 53 + (m.log2 + 1 - 53) = m.log2 + 1 := by omega
    rw [this]
    exact hhi

theorem mul_pow_log_range {m : Nat} (hm : m ≠ 0) (h : m.log2 + 1 ≤ 53) :
    2 ^ 52 ≤ m <<< (53 - (m.log2 + 1)) ∧
      m <<< (53 - (m.log2 + 1)) < 2 ^ 53 := by
  have hlo : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
  have hhi : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  rw [Nat.shiftLeft_eq]
  constructor
  · refine Nat.le_trans ?_ (Nat.mul_le_mul_right _ hlo)
    rw [← Nat.pow_add]
    have : m.log2 + (53 - (m.log2 + 1)) = 52 := by omega
    rw [this]
    exact Nat.le_refl _
  · have hmul :
        m * 2 ^ (53 - (m.log2 + 1)) <
          2 ^ (m.log2 + 1) * 2 ^ (53 - (m.log2 + 1)) :=
      Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at hmul
    have : m.log2 + 1 + (53 - (m.log2 + 1)) = 53 := by omega
    rwa [this] at hmul

theorem toNat_sub_log_lt {m : Nat} {e : Int}
    (h : e < (m.log2 + 1 : Nat) + e - 53) :
    53 < m.log2 + 1 := by
  have : (53 : Int) < (m.log2 + 1 : Nat) := by omega
  exact Int.ofNat_lt.mp this

theorem toNat_sub_log_le {m : Nat} {e : Int}
    (h : (m.log2 + 1 : Nat) + e - 53 ≤ e) :
    m.log2 + 1 ≤ 53 := by
  have : (m.log2 + 1 : Nat) ≤ (53 : Int) := by omega
  exact Int.ofNat_le.mp this

theorem target_sub_e_toNat {m : Nat} {e : Int}
    (h : spec64.minExponent < spec64.targetExponent (totalExponent m e))
    (hlt : e < spec64.targetExponent (totalExponent m e)) :
    (spec64.targetExponent (totalExponent m e) - e).toNat = m.log2 + 1 - 53 := by
  have ht : spec64.targetExponent (totalExponent m e) =
      (m.log2 + 1 : Nat) + e - 53 := by
    rw [target_eq_te_sub h, te_sub_eq]
  have hbig := toNat_sub_log_lt (ht ▸ hlt)
  have hnn : 0 ≤ spec64.targetExponent (totalExponent m e) - e :=
    Int.sub_nonneg_of_le (Int.le_of_lt hlt)
  have hnat : ((m.log2 + 1 - 53 : Nat) : Int) = (m.log2 + 1 : Nat) - 53 :=
    Int.natCast_sub (Nat.le_of_lt hbig)
  have hte : (spec64.targetExponent (totalExponent m e) - e : Int) =
      (m.log2 + 1 - 53 : Nat) := by
    rw [ht, hnat]
    omega
  rw [hte]
  exact Int.toNat_natCast _

theorem e_sub_target_toNat {m : Nat} {e : Int}
    (h : spec64.minExponent < spec64.targetExponent (totalExponent m e))
    (hle : spec64.targetExponent (totalExponent m e) ≤ e) :
    (e - spec64.targetExponent (totalExponent m e)).toNat = 53 - (m.log2 + 1) := by
  have ht : spec64.targetExponent (totalExponent m e) =
      (m.log2 + 1 : Nat) + e - 53 := by
    rw [target_eq_te_sub h, te_sub_eq]
  have hlog := toNat_sub_log_le (ht ▸ hle)
  have hnn : 0 ≤ e - spec64.targetExponent (totalExponent m e) :=
    Int.sub_nonneg_of_le hle
  have hnat : ((53 - (m.log2 + 1) : Nat) : Int) = 53 - (m.log2 + 1 : Nat) :=
    Int.natCast_sub hlog
  have hte : (e - spec64.targetExponent (totalExponent m e) : Int) =
      (53 - (m.log2 + 1) : Nat) := by
    rw [ht, hnat]
    omega
  rw [hte]
  exact Int.toNat_natCast _

/-- After decrease+shift of a nonzero exact value whose target is strictly
    above `minExponent`, the mantissa is a 53-bit normal. -/
theorem decrease_shift_mantissa_normal {m : Nat} {e : Int} (hm : m ≠ 0)
    (h : spec64.minExponent < spec64.targetExponent (totalExponent m e)) :
    2 ^ 52 ≤
        (shiftToTargetExponent spec64
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
          .exact).1.mantissa ∧
      (shiftToTargetExponent spec64
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
          .exact).1.mantissa < 2 ^ 53 := by
  rw [shiftToTargetExponent_exact_mantissa, totalExponent_decreaseExponent hm,
    decreaseExponent_snd]
  cases Int.lt_or_le e (spec64.targetExponent (totalExponent m e)) with
  | inl hlt =>
    have hmin : min e (spec64.targetExponent (totalExponent m e)) = e :=
      Int.min_eq_left (Int.le_of_lt hlt)
    rw [hmin, target_sub_e_toNat h hlt]
    have hbig := toNat_sub_log_lt (by
      have ht : spec64.targetExponent (totalExponent m e) =
          (m.log2 + 1 : Nat) + e - 53 := by
        rw [target_eq_te_sub h, te_sub_eq]
      exact ht ▸ hlt)
    -- decreaseExponent didn't move the mantissa (e < t)
    have hfst : (decreaseExponent m e
        (spec64.targetExponent (totalExponent m e))).1 = m := by
      simp only [decreaseExponent]
      have : (e - spec64.targetExponent (totalExponent m e)).toNat = 0 :=
        (Int.toNat_sub_eq_zero_iff _ _).mpr (Int.le_of_lt hlt)
      rw [this, Nat.shiftLeft_zero]
    rw [hfst]
    exact div_pow_log_range hm hbig
  | inr hle =>
    have hmin : min e (spec64.targetExponent (totalExponent m e)) =
        spec64.targetExponent (totalExponent m e) := Int.min_eq_right hle
    rw [hmin]
    have hk0 : (spec64.targetExponent (totalExponent m e) -
        spec64.targetExponent (totalExponent m e)).toNat = 0 := by simp
    rw [hk0, Nat.shiftRight_zero]
    have hfst : (decreaseExponent m e
        (spec64.targetExponent (totalExponent m e))).1 =
        m <<< (53 - (m.log2 + 1)) := by
      simp only [decreaseExponent]
      rw [e_sub_target_toNat h hle]
    rw [hfst]
    exact mul_pow_log_range hm (toNat_sub_log_le (by
      have ht : spec64.targetExponent (totalExponent m e) =
          (m.log2 + 1 : Nat) + e - 53 := by
        rw [target_eq_te_sub h, te_sub_eq]
      exact ht ▸ hle))


theorem firstRounded_exponent {s : Sign} {m : Nat} {e : Int} {up : Bool}
    (hm : m ≠ 0) :
    (firstRounded s m e up).2 = spec64.targetExponent (totalExponent m e) :=
  decrease_shift_exponent hm

theorem firstRounded_mantissa_normal {s : Sign} {m : Nat} {e : Int} {up : Bool}
    (hm : m ≠ 0)
    (h : spec64.minExponent < spec64.targetExponent (totalExponent m e)) :
    2 ^ 52 ≤ (firstRounded s m e up).1 ∧ (firstRounded s m e up).1 ≤ 2 ^ 53 := by
  have ⟨hlo, hhi⟩ := decrease_shift_mantissa_normal (e := e) hm h
  -- firstRounded.1 is roundMantissaDirected of that mantissa
  unfold firstRounded
  dsimp
  have hle := rounded_le_pow53 s up
    (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
    (spec64.targetExponent (totalExponent
      (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
      (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2) -
      (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2).toNat
    (by
      have := shiftToTarget_mantissa_lt
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
      rwa [shiftToTargetExponent_exact_mantissa] at this)
  -- lower bound: rounded is m1 or m1+1, m1 ≥ 2^52
  refine ⟨?_, hle⟩
  -- need firstRounded.1 ≥ 2^52
  -- I'll prove rounded ≥ original mantissa after first shift
  have hge : (shiftToTargetExponent spec64
      (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
      (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
      Accuracy.exact).1.mantissa ≤
      roundMantissaDirected
        (shiftToTargetExponent spec64
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
          Accuracy.exact).1.mantissa
        up s
        (shiftToTargetExponent spec64
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
          (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
          Accuracy.exact).1.accuracy := by
    cases hacc : (shiftToTargetExponent spec64
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).1
        (decreaseExponent m e (spec64.targetExponent (totalExponent m e))).2
        Accuracy.exact).1.accuracy with
    | exact => simp
    | inexact o =>
      simp [roundMantissaDirected_inexact]
      split <;> simp
  exact Nat.le_trans hlo hge


theorem roundMantissa_ge (s : Sign) (up : Bool) (m : Nat) (acc : Accuracy) :
    m ≤ roundMantissaDirected m up s acc := by
  cases acc with
  | exact => simp
  | inexact o =>
    simp [roundMantissaDirected_inexact]
    split <;> omega

theorem firstRounded_of_zero (s : Sign) (e : Int) (up : Bool) :
    (firstRounded s 0 e up).1 = 0 := by
  unfold firstRounded
  dsimp
  have hfst : (decreaseExponent 0 e (spec64.targetExponent (totalExponent 0 e))).1 = 0 := by
    simp only [decreaseExponent, Nat.shiftLeft_eq, Nat.zero_mul]
  rw [hfst]
  have hmnt : (shiftToTargetExponent spec64 0
      (decreaseExponent 0 e (spec64.targetExponent (totalExponent 0 e))).2
      Accuracy.exact).1.mantissa = 0 := by
    rw [shiftToTargetExponent_exact_mantissa, Nat.zero_shiftRight]
  have hacc : (shiftToTargetExponent spec64 0
      (decreaseExponent 0 e (spec64.targetExponent (totalExponent 0 e))).2
      Accuracy.exact).1.accuracy = .exact := by
    rw [shiftToTargetExponent_exact_em]
    exact (shiftRight_exact_accuracy 0 _).mpr (Nat.zero_mod _)
  rw [hacc, hmnt, roundMantissaDirected_exact]

theorem roundDirected_zero_or_shaped (s : Sign) (m : Nat) (e : Int) (up : Bool) :
    (∃ z, roundDirected s m e .exact up = .zero z) ∨
      (∃ m' e' h, roundDirected s m e .exact up = .finite s m' e' h ∧
          (IsSubnormal m' e' ∨ IsNormal m' e' ∨ IsOverflowNormal m' e')) := by
  rw [roundDirected_eq_shift_of_rounded]
  have he : spec64.minExponent ≤ (firstRounded s m e up).2 :=
    firstRounded_snd_ge_min s m e up
  have hle : (firstRounded s m e up).1 ≤ 2 ^ 53 :=
    firstRounded_fst_le_pow53 s m e up
  by_cases h0 : (firstRounded s m e up).1 = 0
  · have hshift0 :
        (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).1.mantissa = 0 := by
      rw [h0, shiftToTargetExponent_exact_mantissa, shiftAmount_of_short he (by decide),
        Nat.shiftRight_zero]
    dsimp
    rw [dite_eq_left hshift0]
    refine Or.inl ⟨s, rfl⟩
  · have hne :
        (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).1.mantissa ≠ 0 :=
      shiftToTarget_short_ne_zero he hle h0
    dsimp
    rw [dite_eq_right hne]
    refine Or.inr ?_
    refine ⟨(shiftToTargetExponent spec64 (firstRounded s m e up).1
        (firstRounded s m e up).2 Accuracy.exact).1.mantissa,
      (shiftToTargetExponent spec64 (firstRounded s m e up).1
        (firstRounded s m e up).2 Accuracy.exact).2,
      Nat.pos_of_ne_zero hne, rfl, ?_⟩
    cases Nat.lt_or_eq_of_le hle with
    | inl hlt =>
      have hk0 : (spec64.targetExponent (totalExponent (firstRounded s m e up).1
          (firstRounded s m e up).2) - (firstRounded s m e up).2).toNat = 0 :=
        shiftAmount_of_short he hlt
      have hmnt : (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).1.mantissa =
          (firstRounded s m e up).1 := by
        rw [shiftToTargetExponent_exact_mantissa, hk0, Nat.shiftRight_zero]
      have hexp : (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).2 =
          (firstRounded s m e up).2 := by
        rw [shiftToTargetExponent_exact_exponent, hk0, Int.natCast_zero, Int.add_zero]
      rw [hmnt, hexp]
      by_cases hmin : (firstRounded s m e up).2 = spec64.minExponent
      · by_cases hsub : (firstRounded s m e up).1 < 2 ^ 52
        · exact Or.inl ⟨hmin, Nat.pos_of_ne_zero h0, hsub⟩
        · have hge : 2 ^ 52 ≤ (firstRounded s m e up).1 := Nat.le_of_not_lt hsub
          have hminle : spec64.minExponent ≤ (firstRounded s m e up).2 :=
            Int.le_of_eq hmin.symm
          have hovlt : (firstRounded s m e up).2 < overflowExponent := by
            rw [hmin]
            simp [minExponent_spec64, overflowExponent]
          exact Or.inr (Or.inl ⟨hminle, hovlt, hge, hlt⟩)
      · have hm0 : m ≠ 0 := by
          intro hz
          apply h0
          rw [hz]
          exact firstRounded_of_zero s e up
        have hgt : spec64.minExponent < (firstRounded s m e up).2 :=
          (Int.lt_iff_le_and_ne).mpr ⟨he, Ne.symm hmin⟩
        have htar : (firstRounded s m e up).2 =
            spec64.targetExponent (totalExponent m e) :=
          firstRounded_exponent hm0
        have hnorm := firstRounded_mantissa_normal (s := s) (up := up) hm0 (htar ▸ hgt)
        have hge : 2 ^ 52 ≤ (firstRounded s m e up).1 := hnorm.1
        by_cases hov : overflowExponent ≤ (firstRounded s m e up).2
        · exact Or.inr (Or.inr ⟨hov, hge, hlt⟩)
        · exact Or.inr (Or.inl ⟨he, Int.lt_of_not_ge hov, hge, hlt⟩)
    | inr heq =>
      have hpow := targetExponent_pow53 (e := (firstRounded s m e up).2) he
      have hmnt : (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).1.mantissa = 2 ^ 52 := by
        rw [shiftToTargetExponent_exact_mantissa, heq, hpow]
        have : ((firstRounded s m e up).2 + 1 -
            (firstRounded s m e up).2 : Int).toNat = 1 := by
          have h1 : (firstRounded s m e up).2 + 1 - (firstRounded s m e up).2 =
              (1 : Int) := by omega
          simp [h1]
        rw [this, Nat.shiftRight_eq_div_pow]
      have hexp : (shiftToTargetExponent spec64 (firstRounded s m e up).1
          (firstRounded s m e up).2 Accuracy.exact).2 =
          (firstRounded s m e up).2 + 1 := by
        rw [shiftToTargetExponent_exact_exponent, heq, hpow]
        have : ((firstRounded s m e up).2 + 1 -
            (firstRounded s m e up).2 : Int).toNat = 1 := by
          have h1 : (firstRounded s m e up).2 + 1 - (firstRounded s m e up).2 =
              (1 : Int) := by omega
          simp [h1]
        rw [this]
        rfl
      rw [hmnt, hexp]
      have hge : 2 ^ 52 ≤ 2 ^ 52 := Nat.le_refl _
      have hhi : (2 ^ 52 : Nat) < 2 ^ 53 := by decide
      have he2 : spec64.minExponent ≤ (firstRounded s m e up).2 + 1 :=
        Int.le_trans he (Int.le_add_of_nonneg_right (by decide))
      by_cases hov : overflowExponent ≤ (firstRounded s m e up).2 + 1
      · exact Or.inr (Or.inr ⟨hov, hge, hhi⟩)
      · exact Or.inr (Or.inl ⟨he2, Int.lt_of_not_ge hov, hge, hhi⟩)

end Interval64Proofs.Canonical
