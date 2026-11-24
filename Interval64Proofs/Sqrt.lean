/-
Bits-level directed square-root enclosure, including inexact `sqrtCore`
residuals, and interval membership for `Interval64.sqrt`.
-/
import Interval64Proofs.Div
import Init.Data.Nat.Sqrt.Lemmas

namespace Interval64Proofs.Sqrt

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.RoundInexact
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.ExactAdd
open Interval64Proofs.Mul
open Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem
open Interval64Proofs.Div
open Float.Model
open Float.Model.UnpackedFloat

/-! ### `sqrtCore` residuals: `root² ≤ M < (root+1)²` -/

theorem sqrtCore_te_def (m : Nat) (e : Int) :
    (sqrtCore spec64 m e).2.1 =
      min (e.ediv 2)
        (spec64.targetExponent ((totalExponent m e + 1).ediv 2)) :=
  rfl

theorem sqrtCore_te_le_ediv2 (m : Nat) (e : Int) :
    (sqrtCore spec64 m e).2.1 ≤ e.ediv 2 := by
  rw [sqrtCore_te_def]
  exact Int.min_le_left _ _

theorem two_mul_ediv2_le (e : Int) : 2 * e.ediv 2 ≤ e := by
  have h : 2 * (e / 2) + e % 2 = e := Int.mul_ediv_add_emod e 2
  have hr : 0 ≤ e % 2 := Int.emod_nonneg e (by decide : (2 : Int) ≠ 0)
  have : e.ediv 2 = e / 2 := rfl
  omega

theorem sqrtCore_two_te_le (m : Nat) (e : Int) :
    2 * (sqrtCore spec64 m e).2.1 ≤ e :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_left (sqrtCore_te_le_ediv2 m e) (by decide))
    (two_mul_ediv2_le e)

theorem sqrtCore_k_eq (m : Nat) (e : Int) :
    let te := (sqrtCore spec64 m e).2.1
    (e - 2 * te).toNat = e - 2 * te :=
  Int.toNat_of_nonneg (Int.sub_nonneg_of_le (sqrtCore_two_te_le m e))

theorem mag_sq (m : Nat) (e : Int) : mag m e * mag m e = mag (m * m) (e + e) :=
  (mag_mul m m e e).symm

theorem mag_sq_two (m : Nat) (e : Int) : mag m e * mag m e = mag (m * m) (2 * e) := by
  have : (2 * e : Int) = e + e := by omega
  rw [this, mag_sq]

theorem mag_shiftLeft_two_te (m : Nat) (e : Int) :
    let te := (sqrtCore spec64 m e).2.1
    let k := (e - 2 * te).toNat
    mag (m <<< k) (2 * te) = mag m e := by
  intro te k
  have hk : (k : Int) = e - 2 * te := sqrtCore_k_eq m e
  have : mag (m <<< k) (e - k) = mag m e := mag_shiftLeft m k e
  have he : e - k = 2 * te := by
    have : (e - k : Int) = e - (e - 2 * te) := by rw [hk]
    omega
  rwa [he] at this

theorem sqrtCore_mag_bracket (m : Nat) (e : Int) :
    let root := (sqrtCore spec64 m e).1
    let te := (sqrtCore spec64 m e).2.1
    mag root te * mag root te ≤ mag m e ∧
      (0 < m → mag m e < mag (root + 1) te * mag (root + 1) te) := by
  intro root te
  let k := (e - 2 * te).toNat
  let M := m <<< k
  have hM : mag M (2 * te) = mag m e := mag_shiftLeft_two_te m e
  have hroot : root = Nat.sqrt M := rfl
  have hle : root * root ≤ M := by
    rw [hroot]
    exact Nat.sqrt_le M
  have hlt : M < (root + 1) * (root + 1) := by
    rw [hroot]
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt M
  have hle' : mag (root * root) (2 * te) ≤ mag M (2 * te) := mag_le_mag hle
  constructor
  · rw [← mag_sq_two, hM] at hle'
    exact hle'
  · intro hm
    have hMpos : 0 < M := by
      have : M = m * 2 ^ k := by
        simp [M, Nat.shiftLeft_eq]
      rw [this]
      exact Nat.mul_pos hm (Nat.two_pow_pos k)
    have : mag M (2 * te) < mag ((root + 1) * (root + 1)) (2 * te) :=
      mag_lt_mag hlt
    rw [← mag_sq_two, hM] at this
    exact this


theorem sqrtCore_acc_exact_iff (m : Nat) (e : Int) :
    (sqrtCore spec64 m e).2.2 = .exact ↔
      m <<< (e - 2 * (sqrtCore spec64 m e).2.1).toNat =
        Nat.sqrt (m <<< (e - 2 * (sqrtCore spec64 m e).2.1).toNat) *
          Nat.sqrt (m <<< (e - 2 * (sqrtCore spec64 m e).2.1).toNat) := by
  let te := (sqrtCore spec64 m e).2.1
  let k := (e - 2 * te).toNat
  let rem := (m <<< k) - Nat.sqrt (m <<< k) * Nat.sqrt (m <<< k)
  have hk : k = (e - 2 * (sqrtCore spec64 m e).2.1).toNat := rfl
  have hacc : (sqrtCore spec64 m e).2.2 =
      if rem = 0 then Accuracy.exact
      else Accuracy.inexact (if rem ≤ Nat.sqrt (m <<< k) then .lt else .gt) :=
    rfl
  constructor
  · intro hex
    have hrem : rem = 0 := by
      rw [hacc] at hex
      split at hex
      · next h0 => exact h0
      · next => cases hex
    have : Nat.sqrt (m <<< k) * Nat.sqrt (m <<< k) = m <<< k :=
      Nat.le_antisymm (Nat.sqrt_le (m <<< k)) (Nat.sub_eq_zero_iff_le.mp hrem)
    simpa [hk] using this.symm
  · intro hsq
    have h : m <<< k = Nat.sqrt (m <<< k) * Nat.sqrt (m <<< k) := by
      simpa [hk] using hsq
    have hrem : rem = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_eq h)
    rw [hacc, hrem]
    rfl

theorem sqrt_eq_of_mul_self {n k : Nat} (h : n = k * k) : Nat.sqrt n = k := by
  have hle := Nat.sqrt_le n
  have hlt := Nat.lt_succ_sqrt n
  have h1 : Nat.sqrt n * Nat.sqrt n ≤ k * k := by rwa [← h]
  have h2 : k * k < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
    simpa [h, Nat.succ_eq_add_one] using hlt
  have hsle : Nat.sqrt n ≤ k := Nat.mul_self_le_mul_self_iff.mp h1
  have hge : k ≤ Nat.sqrt n := by
    have : k < Nat.sqrt n + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
    exact Nat.lt_succ_iff.mp this
  exact Nat.le_antisymm hsle hge

/-! ### `sqrtCore` returns enough mantissa bits for packing -/

theorem sqrtCore_unbiased_lt_ediv2 {m : Nat} {e : Int} (h0 : 0 < m) (hs : m < 2 ^ 53) :
    (totalExponent m e + 1).ediv 2 - (53 : Int) < e.ediv 2 := by
  have hlog : (m.log2 : Int) ≤ 52 :=
    Int.ofNat_le.mpr (log2_le_52_of_lt_pow53 h0 hs)
  have hle_tot : totalExponent m e + 1 ≤ (52 : Int) + e + 2 := by
    unfold totalExponent
    omega
  have hmono : (totalExponent m e + 1).ediv 2 ≤ ((52 : Int) + e + 2).ediv 2 :=
    Int.ediv_le_ediv (by decide : (0 : Int) < 2) hle_tot
  have hsml : ((52 : Int) + e + 2).ediv 2 - 53 < e.ediv 2 := by
    have h1 : 2 * (((52 : Int) + e + 2) / 2) + ((52 : Int) + e + 2) % 2 =
        (52 : Int) + e + 2 := Int.mul_ediv_add_emod _ 2
    have h2 : 2 * (e / 2) + e % 2 = e := Int.mul_ediv_add_emod e 2
    have r1 : 0 ≤ ((52 : Int) + e + 2) % 2 :=
      Int.emod_nonneg _ (by decide : (2 : Int) ≠ 0)
    have r2 : 0 ≤ e % 2 := Int.emod_nonneg e (by decide : (2 : Int) ≠ 0)
    have r1' : ((52 : Int) + e + 2) % 2 < 2 :=
      Int.emod_lt_of_pos _ (by decide : (0 : Int) < 2)
    have r2' : e % 2 < 2 := Int.emod_lt_of_pos e (by decide : (0 : Int) < 2)
    have : ((52 : Int) + e + 2).ediv 2 = ((52 : Int) + e + 2) / 2 := rfl
    have : e.ediv 2 = e / 2 := rfl
    omega
  exact Int.lt_of_le_of_lt (Int.sub_le_sub_right hmono 53) hsml

theorem sqrtCore_te_eq_of_gt_min {m : Nat} {e : Int} (h0 : 0 < m) (hs : m < 2 ^ 53)
    (hgt : spec64.minExponent < (sqrtCore spec64 m e).2.1) :
    (sqrtCore spec64 m e).2.1 =
      (totalExponent m e + 1).ediv 2 - (53 : Int) := by
  have hdef := sqrtCore_te_def m e
  have hlt := sqrtCore_unbiased_lt_ediv2 (e := e) h0 hs
  have hunb : spec64.targetExponent ((totalExponent m e + 1).ediv 2) =
      (totalExponent m e + 1).ediv 2 - (53 : Int) := by
    rcases targetExponent_eq_or_min ((totalExponent m e + 1).ediv 2) with h | hmin
    · exact h
    · have : (sqrtCore spec64 m e).2.1 ≤ spec64.minExponent := by
        rw [hdef, hmin]
        exact Int.min_le_right _ _
      exact (Int.not_le.mpr hgt this).elim
  have hte_eq : (sqrtCore spec64 m e).2.1 =
      spec64.targetExponent ((totalExponent m e + 1).ediv 2) := by
    rw [hdef, hunb]
    exact Int.min_eq_right (Int.le_of_lt hlt)
  exact hte_eq.trans hunb

theorem sqrt_monotone {a b : Nat} (h : a ≤ b) : Nat.sqrt a ≤ Nat.sqrt b := by
  have h1 : Nat.sqrt a * Nat.sqrt a ≤ b := Nat.le_trans (Nat.sqrt_le a) h
  have h2 : Nat.sqrt a * Nat.sqrt a < (Nat.sqrt b + 1) * (Nat.sqrt b + 1) :=
    Nat.lt_of_le_of_lt h1 (by simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt b)
  have : Nat.sqrt a < Nat.sqrt b + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
  exact Nat.lt_succ_iff.mp this

theorem sqrt_two_pow_even (n : Nat) : Nat.sqrt (2 ^ (2 * n)) = 2 ^ n := by
  have : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
    rw [Nat.two_mul, Nat.pow_add]
  exact sqrt_eq_of_mul_self this

theorem sqrtCore_root_ge_pow52_of_gt_min {m : Nat} {e : Int}
    (h0 : 0 < m) (hs : m < 2 ^ 53)
    (hgt : spec64.minExponent < (sqrtCore spec64 m e).2.1) :
    2 ^ 52 ≤ (sqrtCore spec64 m e).1 := by
  let te := (sqrtCore spec64 m e).2.1
  let k := (e - 2 * te).toNat
  let M := m <<< k
  have hte : te = (totalExponent m e + 1).ediv 2 - (53 : Int) :=
    sqrtCore_te_eq_of_gt_min h0 hs hgt
  have hk : (k : Int) = e - 2 * te := sqrtCore_k_eq m e
  have hsum_int : ((m.log2 + k : Nat) : Int) = 105 + totalExponent m e -
      2 * ((totalExponent m e + 1).ediv 2) := by
    have hlog : ((m.log2 + k : Nat) : Int) = (m.log2 : Int) + k :=
      Int.natCast_add _ _
    rw [hlog, hk, hte]
    unfold totalExponent
    omega
  have h2q : 2 * ((totalExponent m e + 1).ediv 2) =
      (totalExponent m e + 1) - (totalExponent m e + 1) % 2 := by
    have := Int.mul_ediv_add_emod (totalExponent m e + 1) 2
    have : (totalExponent m e + 1).ediv 2 = (totalExponent m e + 1) / 2 := rfl
    omega
  have hrem : 0 ≤ (totalExponent m e + 1) % 2 :=
    Int.emod_nonneg _ (by decide : (2 : Int) ≠ 0)
  have hrem' : (totalExponent m e + 1) % 2 < 2 :=
    Int.emod_lt_of_pos _ (by decide : (0 : Int) < 2)
  have hge104 : (104 : Int) ≤ (m.log2 + k : Nat) := by
    rw [hsum_int, h2q]
    omega
  have hlogk : 104 ≤ m.log2 + k := Int.ofNat_le.mp (by
    have : ((104 : Nat) : Int) = 104 := rfl
    rwa [this])
  have hne : m ≠ 0 := Nat.ne_of_gt h0
  have hpow : 2 ^ (m.log2 + k) ≤ M := by
    simp [M, Nat.shiftLeft_eq]
    exact pow_mul_ge_of_log hne
  have hpow104 : 2 ^ 104 ≤ 2 ^ (m.log2 + k) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hlogk
  have hM : 2 ^ 104 ≤ M := Nat.le_trans hpow104 hpow
  have hsqrt : 2 ^ 52 ≤ Nat.sqrt M := by
    have hpoweq : 2 ^ (2 * 52) = 2 ^ 104 := by decide
    have : Nat.sqrt (2 ^ (2 * 52)) ≤ Nat.sqrt M := by
      rw [hpoweq]
      exact sqrt_monotone hM
    exact Nat.le_trans (Nat.le_of_eq (sqrt_two_pow_even 52).symm) this
  have hroot : (sqrtCore spec64 m e).1 = Nat.sqrt M := rfl
  rwa [hroot]

theorem sqrtCore_enough_bits {m : Nat} {e : Int} (h0 : 0 < m) (hs : m < 2 ^ 53) :
    (sqrtCore spec64 m e).2.1 ≤ spec64.minExponent ∨
      2 ^ 52 ≤ (sqrtCore spec64 m e).1 := by
  by_cases hte : (sqrtCore spec64 m e).2.1 ≤ spec64.minExponent
  · exact Or.inl hte
  · exact Or.inr (sqrtCore_root_ge_pow52_of_gt_min h0 hs (Int.lt_of_not_ge hte))


/-! ### Nonnegative squares -/

theorem sq_le_sq_of_nonneg {a b : Rat} (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b :=
  mul_le_mul_nonneg ha ha h h

theorem mul_self_lt_mul_self {a b : Rat} (ha : 0 ≤ a) (h : a < b) : a * a < b * b := by
  have hb : 0 < b := rat_lt_of_le_of_lt ha h
  by_cases hz : a = 0
  · rw [hz, Rat.zero_mul]
    exact Rat.mul_pos hb hb
  · have hapos : 0 < a := Rat.lt_of_le_of_ne ha (Ne.symm hz)
    have h1 : a * a < a * b := Rat.mul_lt_mul_of_pos_left h hapos
    have h2 : a * b < b * b := Rat.mul_lt_mul_of_pos_right h hb
    exact rat_lt_trans h1 h2

theorem le_of_sq_le_sq {a b : Rat} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a ≤ b * b) :
    a ≤ b := by
  by_cases hle : a ≤ b
  · exact hle
  · have hlt : b < a := Rat.not_le.mp hle
    have hsq : b * b < a * a := mul_self_lt_mul_self hb hlt
    exact ((Rat.lt_iff_le_and_not_ge.mp hsq).2 h).elim

theorem firstRoundedAcc_pos_lo_le (m : Nat) (e : Int) (acc : Accuracy) :
    signedVal .positive (firstRoundedAcc .positive m e acc false).1
      (firstRoundedAcc .positive m e acc false).2 ≤ mag m e := by
  cases acc with
  | exact =>
    simpa [firstRoundedAcc_exact, signedVal] using
      signedVal_firstRounded_lo .positive m e
  | inexact o =>
    unfold firstRoundedAcc
    dsimp
    rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
    let k := (spec64.targetExponent (totalExponent m e) - e).toNat
    have hm :
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa =
          m >>> k :=
      shiftRight_of_acc_mantissa m k (.inexact o)
    have hr :
        roundMantissaDirected
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
          false .positive
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
          ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa := by
      cases hacc :
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy with
      | exact => simp
      | inexact o' => simp [roundMantissaDirected_inexact, awayFromZero_false_positive]
    have hk : (spec64.targetExponent (totalExponent m e) - e).toNat = k := rfl
    rw [hr, hm, hk]
    simpa [signedVal] using mag_shiftRight_le m k e

theorem shift_succ_mul_pow (m k : Nat) :
    m + 1 ≤ ((m >>> k) + 1) * 2 ^ k := by
  have hsplit : (m >>> k) * 2 ^ k + m % 2 ^ k = m := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact Nat.div_add_mod m (2 ^ k)
  have hmod : m % 2 ^ k + 1 ≤ 2 ^ k :=
    Nat.succ_le_of_lt (Nat.mod_lt m (Nat.two_pow_pos k))
  have hle : m % 2 ^ k ≤ m := Nat.mod_le m (2 ^ k)
  have : ((m >>> k) + 1) * 2 ^ k = m - m % 2 ^ k + 2 ^ k := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

theorem ofMantissa_inexact_residual (m : Nat) (o : Ordering) :
    (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)).roundBit = true ∨
      (ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)).stickyBit = true := by
  cases o <;> simp [ExtendedMantissa.ofMantissaAndAccuracy]

theorem shiftRightOne_keeps_residual (em : ExtendedMantissa)
    (h : em.roundBit = true ∨ em.stickyBit = true) :
    em.shiftRightOne.roundBit = true ∨ em.shiftRightOne.stickyBit = true := by
  refine Or.inr ?_
  cases h with
  | inl hr => simp [ExtendedMantissa.shiftRightOne, hr]
  | inr hs => simp [ExtendedMantissa.shiftRightOne, hs]

theorem shiftRight_keeps_residual (em : ExtendedMantissa) (k : Nat)
    (h : em.roundBit = true ∨ em.stickyBit = true) :
    (em >>> k).roundBit = true ∨ (em >>> k).stickyBit = true := by
  induction k with
  | zero => simpa [HShiftRight.hShiftRight, Nat.repeat] using h
  | succ k ih =>
    have : (em >>> (k + 1)) = (em >>> k).shiftRightOne := by
      simp [HShiftRight.hShiftRight, Nat.repeat]
    rw [this]
    exact shiftRightOne_keeps_residual _ ih

theorem accuracy_inexact_of_residual {em : ExtendedMantissa}
    (h : em.roundBit = true ∨ em.stickyBit = true) :
    ∃ o, em.accuracy = .inexact o := by
  cases em with
  | mk _ rb sb =>
    cases rb <;> cases sb
    · cases h with
      | inl n => cases n
      | inr n => cases n
    · exact ⟨.lt, rfl⟩
    · exact ⟨.eq, rfl⟩
    · exact ⟨.gt, rfl⟩

theorem shiftRight_inexact_stays (m k : Nat) (o : Ordering) :
    ∃ o', ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
      .inexact o' :=
  accuracy_inexact_of_residual
    (shiftRight_keeps_residual _ k (ofMantissa_inexact_residual m o))

theorem firstRoundedAcc_pos_hi_inexact_ge_succ (m : Nat) (e : Int) (o : Ordering) :
    mag (m + 1) e ≤
      signedVal .positive (firstRoundedAcc .positive m e (.inexact o) true).1
        (firstRoundedAcc .positive m e (.inexact o) true).2 := by
  unfold firstRoundedAcc
  dsimp
  rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
  let k := (spec64.targetExponent (totalExponent m e) - e).toNat
  have hk : (spec64.targetExponent (totalExponent m e) - e).toNat = k := rfl
  have hm :
      ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa =
        m >>> k :=
    shiftRight_of_acc_mantissa m k (.inexact o)
  rcases shiftRight_inexact_stays m k o with ⟨o', ho'⟩
  have hr :
      roundMantissaDirected
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa
        true .positive
        ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy =
        m >>> k + 1 := by
    rw [ho', hm, roundMantissaDirected_inexact, awayFromZero_true_positive]
    simp
  rw [hr, hk]
  have hge := shift_succ_mul_pow m k
  have : mag ((m >>> k) + 1) (e + k) = mag (((m >>> k) + 1) * 2 ^ k) e :=
    (mag_mul_two_pow_add ((m >>> k) + 1) k e).symm
  have hle : mag (m + 1) e ≤ mag (((m >>> k) + 1) * 2 ^ k) e :=
    mag_le_mag hge
  simpa [signedVal, this] using hle

theorem loEncloses_of_le {ev : Option EVal} {u v : Rat}
    (h : loEncloses? ev u) (hle : u ≤ v) : loEncloses? ev v := by
  cases ev with
  | none =>
    simp [loEncloses?] at h
  | some ev =>
    cases ev with
    | negInf => simp [loEncloses?, loEncloses]
    | posInf =>
      simp [loEncloses?, loEncloses] at h
    | rat q =>
      simp [loEncloses?, loEncloses] at h ⊢
      exact Rat.le_trans h hle

theorem hiEncloses_of_ge {ev : Option EVal} {u v : Rat}
    (h : hiEncloses? ev u) (hge : v ≤ u) : hiEncloses? ev v := by
  cases ev with
  | none =>
    simp [hiEncloses?] at h
  | some ev =>
    cases ev with
    | posInf => simp [hiEncloses?, hiEncloses]
    | negInf =>
      simp [hiEncloses?, hiEncloses] at h
    | rat q =>
      simp [hiEncloses?, hiEncloses] at h ⊢
      exact Rat.le_trans hge h

theorem sqrtU_finite_eq_round {m : Nat} {e : Int} (h : 0 < m) (up : Bool) :
    sqrtU (.finite .positive m e h) up =
      let (m', e', acc) := sqrtCore spec64 m e
      roundDirected .positive m' e' acc up :=
  rfl

theorem sqrtU_shaped_or_zero {m : Nat} {e : Int} (h : 0 < m) (hs : m < 2 ^ 53)
    (up : Bool) :
    (∃ z, sqrtU (.finite .positive m e h) up = .zero z) ∨
      (∃ m' e' h', sqrtU (.finite .positive m e h) up = .finite .positive m' e' h' ∧
        (IsSubnormal m' e' ∨ IsNormal m' e' ∨ IsOverflowNormal m' e')) := by
  rw [sqrtU_finite_eq_round]
  refine roundDirected_zero_or_shaped_acc .positive
    (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1
    (sqrtCore spec64 m e).2.2 up ?_
  intro h0
  exact firstRoundedAcc_norm_of_enough .positive
    (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1
    (sqrtCore spec64 m e).2.2 up
    (Or.inr (sqrtCore_enough_bits h hs)) h0

theorem mag_roundDirected_pos_lo {m : Nat} {e : Int} {acc : Accuracy}
    {m' : Nat} {e' : Int} {h : 0 < m'}
    (heq : roundDirected .positive m e acc false = .finite .positive m' e' h) :
    mag m' e' ≤ mag m e := by
  have hform := roundDirected_eq_shift_of_rounded_acc .positive m e acc false
  have h0 : (firstRoundedAcc .positive m e acc false).1 ≠ 0 := by
    intro hz
    have hz' := shiftToTarget_short_zero_of_first (s := .positive) (m := m)
      (e := e) (acc := acc) (up := false) hz
    rw [hform] at heq
    simp only at heq
    rw [dite_eq_left hz'] at heq
    cases heq
  have hne := shiftToTarget_short_ne_zero_of_first (s := .positive) (m := m)
    (e := e) (acc := acc) (up := false) h0
  have hpres := signedVal_shiftToTarget_short (s := .positive)
    (firstRoundedAcc_snd_ge_min .positive m e acc false)
    (firstRoundedAcc_fst_le_pow53 .positive m e acc false)
  have hle := firstRoundedAcc_pos_lo_le m e acc
  rw [hform] at heq
  simp only at heq
  rw [dite_eq_right hne] at heq
  injection heq with _ hm' he'
  have hpres' :
      mag
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e acc false).1
          (firstRoundedAcc .positive m e acc false).2 .exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e acc false).1
          (firstRoundedAcc .positive m e acc false).2 .exact).2 =
      mag (firstRoundedAcc .positive m e acc false).1
        (firstRoundedAcc .positive m e acc false).2 := by
    simpa [signedVal] using hpres
  rw [← hm', ← he', hpres']
  exact firstRoundedAcc_pos_lo_le m e acc

theorem mag_roundDirected_pos_hi_exact {m : Nat} {e : Int}
    {m' : Nat} {e' : Int} {h : 0 < m'}
    (heq : roundDirected .positive m e .exact true = .finite .positive m' e' h) :
    mag m e ≤ mag m' e' := by
  have hform := roundDirected_eq_shift_of_rounded_acc .positive m e .exact true
  have h0 : (firstRoundedAcc .positive m e .exact true).1 ≠ 0 := by
    intro hz
    have hz' := shiftToTarget_short_zero_of_first (s := .positive) (m := m)
      (e := e) (acc := Accuracy.exact) (up := true) hz
    rw [hform] at heq
    simp only at heq
    rw [dite_eq_left hz'] at heq
    cases heq
  have hne := shiftToTarget_short_ne_zero_of_first (s := .positive) (m := m)
    (e := e) (acc := Accuracy.exact) (up := true) h0
  have hpres := signedVal_shiftToTarget_short (s := .positive)
    (firstRoundedAcc_snd_ge_min .positive m e .exact true)
    (firstRoundedAcc_fst_le_pow53 .positive m e .exact true)
  have hge : mag m e ≤
      signedVal .positive (firstRoundedAcc .positive m e .exact true).1
        (firstRoundedAcc .positive m e .exact true).2 := by
    simpa [firstRoundedAcc_exact, signedVal] using
      signedVal_firstRounded_hi .positive m e
  rw [hform] at heq
  simp only at heq
  rw [dite_eq_right hne] at heq
  injection heq with _ hm' he'
  have hpres' :
      mag
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e .exact true).1
          (firstRoundedAcc .positive m e .exact true).2 .exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e .exact true).1
          (firstRoundedAcc .positive m e .exact true).2 .exact).2 =
      mag (firstRoundedAcc .positive m e .exact true).1
        (firstRoundedAcc .positive m e .exact true).2 := by
    simpa [signedVal] using hpres
  rw [← hm', ← he', hpres']
  exact hge

theorem mag_roundDirected_pos_hi_inexact {m : Nat} {e : Int} {o : Ordering}
    {m' : Nat} {e' : Int} {h : 0 < m'}
    (heq : roundDirected .positive m e (.inexact o) true =
      .finite .positive m' e' h) :
    mag (m + 1) e ≤ mag m' e' := by
  have hform := roundDirected_eq_shift_of_rounded_acc .positive m e (.inexact o) true
  have h0 : (firstRoundedAcc .positive m e (.inexact o) true).1 ≠ 0 := by
    intro hz
    have hz' := shiftToTarget_short_zero_of_first (s := .positive) (m := m)
      (e := e) (acc := Accuracy.inexact o) (up := true) hz
    rw [hform] at heq
    simp only at heq
    rw [dite_eq_left hz'] at heq
    cases heq
  have hne := shiftToTarget_short_ne_zero_of_first (s := .positive) (m := m)
    (e := e) (acc := Accuracy.inexact o) (up := true) h0
  have hpres := signedVal_shiftToTarget_short (s := .positive)
    (firstRoundedAcc_snd_ge_min .positive m e (.inexact o) true)
    (firstRoundedAcc_fst_le_pow53 .positive m e (.inexact o) true)
  have hge := firstRoundedAcc_pos_hi_inexact_ge_succ m e o
  rw [hform] at heq
  simp only at heq
  rw [dite_eq_right hne] at heq
  injection heq with _ hm' he'
  have hpres' :
      mag
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e (.inexact o) true).1
          (firstRoundedAcc .positive m e (.inexact o) true).2 .exact).1.mantissa
        (shiftToTargetExponent spec64 (firstRoundedAcc .positive m e (.inexact o) true).1
          (firstRoundedAcc .positive m e (.inexact o) true).2 .exact).2 =
      mag (firstRoundedAcc .positive m e (.inexact o) true).1
        (firstRoundedAcc .positive m e (.inexact o) true).2 := by
    simpa [signedVal] using hpres
  rw [← hm', ← he', hpres']
  exact hge

theorem sqrtCore_root_pos {m : Nat} {e : Int} (h : 0 < m) :
    0 < (sqrtCore spec64 m e).1 := by
  let te := (sqrtCore spec64 m e).2.1
  let k := (e - 2 * te).toNat
  let M := m <<< k
  have hM : 0 < M := by
    have : M = m * 2 ^ k := by simp [M, Nat.shiftLeft_eq]
    rw [this]
    exact Nat.mul_pos h (Nat.two_pow_pos k)
  have hroot : (sqrtCore spec64 m e).1 = Nat.sqrt M := rfl
  rw [hroot]
  refine Nat.pos_of_ne_zero ?_
  intro hz
  have : M < 1 := by
    have := Nat.lt_succ_sqrt M
    simpa [hz, Nat.succ_eq_add_one] using this
  exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hM (Nat.le_of_lt_succ this))

theorem sqrtCore_mag_eq_of_exact {m : Nat} {e : Int}
    (hex : (sqrtCore spec64 m e).2.2 = .exact) :
    mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 *
      mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 = mag m e := by
  have hsq := (sqrtCore_acc_exact_iff m e).mp hex
  let te := (sqrtCore spec64 m e).2.1
  let k := (e - 2 * te).toNat
  let root := (sqrtCore spec64 m e).1
  have hM : mag (m <<< k) (2 * te) = mag m e := mag_shiftLeft_two_te m e
  have : m <<< k = root * root := by
    have hroot : root = Nat.sqrt (m <<< k) := rfl
    simpa [te, k, hroot] using hsq
  have : mag (root * root) (2 * te) = mag m e := by rwa [← this]
  rwa [← mag_sq_two] at this

/-- If `r` is a nonnegative square root of the finite value of `a`,
    both directed square roots enclose `r`. Equivalently, finite packed
    results `qlo`, `qhi` satisfy `qlo² ≤ qa ≤ qhi²`. -/
theorem sqrt_mem_rat {a : UInt64} {qa r : Rat}
    (ha : bitsToRat? a = some qa) (hr : 0 ≤ r) (hsq : r * r = qa) :
    loEncloses? (bitsToEVal (sqrtDown a)) r ∧
    hiEncloses? (bitsToEVal (sqrtUp a)) r := by
  have hqa : 0 ≤ qa := by
    simpa [hsq, Rat.zero_mul] using
      sq_le_sq_of_nonneg (by decide : (0 : Rat) ≤ 0) hr
  simp only [sqrtDown, sqrtUp, Interval64.Spec.sqrt]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s, hu, rfl⟩
    have hr0 : r = 0 := by
      have h0 : r * r = 0 := hsq
      by_cases hz : r = 0
      · exact hz
      · have hp : 0 < r := Rat.lt_of_le_of_ne hr (Ne.symm hz)
        exact (ne_of_pos_rat (Rat.mul_pos hp hp) h0).elim
    rw [hu]
    simp only [sqrtU]
    exact ⟨loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, hr0]),
           hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, hr0])⟩
  · rcases hfa with ⟨s, m, e, hm, hu, rfl, hc⟩
    cases s with
    | negative =>
      have : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
      exact ((Rat.lt_iff_le_and_not_ge.mp this).2 hqa).elim
    | positive =>
      rw [hu]
      have hsq' : r * r = mag m e := by simpa [signedVal] using hsq
      have hs : m < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hc
      have hbr := sqrtCore_mag_bracket m e
      let root := (sqrtCore spec64 m e).1
      let te := (sqrtCore spec64 m e).2.1
      let acc := (sqrtCore spec64 m e).2.2
      have hlo_sq : mag root te * mag root te ≤ mag m e := hbr.1
      have hhi_sq : mag m e < mag (root + 1) te * mag (root + 1) te := hbr.2 hm
      have hshape_lo := sqrtU_shaped_or_zero (e := e) hm hs false
      have hshape_hi := sqrtU_shaped_or_zero (e := e) hm hs true
      constructor
      · rcases hshape_lo with ⟨z, heq⟩ | ⟨m', e', h', heq, hsh⟩
        · rw [heq]
          exact loEncloses_packDirected_zero_val _ _ _
            (by simp [loEncloses?, loEncloses]; exact hr)
        · rw [heq]
          have hrd : roundDirected .positive root te acc false =
              .finite .positive m' e' h' := heq ▸ sqrtU_finite_eq_round hm false
          have hle : mag m' e' ≤ mag root te := mag_roundDirected_pos_lo hrd
          have hsqle : mag m' e' * mag m' e' ≤ r * r :=
            Rat.le_trans (sq_le_sq_of_nonneg (mag_nonneg _ _) hle)
              (by simpa [hsq'] using hlo_sq)
          have hle' : mag m' e' ≤ r :=
            le_of_sq_le_sq (mag_nonneg _ _) hr hsqle
          have henc := loEncloses_packDirected_of_shaped .positive h' hsh
            (signedVal .positive m' e') (by simp [loEncloses?, loEncloses, signedVal])
          exact loEncloses_of_le henc (by simpa [signedVal] using hle')
      · rcases hshape_hi with ⟨z, heq⟩ | ⟨m', e', h', heq, hsh⟩
        · -- upward sqrt of a positive finite is never zero
          have hrd : sqrtU (.finite .positive m e hm) true = .zero z := heq
          have hform : sqrtU (.finite .positive m e hm) true =
              roundDirected .positive root te acc true := rfl
          -- firstRounded would have to be 0, contradicting root_pos after upward
          have : False := by
            have h0 : (firstRoundedAcc .positive root te acc true).1 = 0 := by
              have hform' := roundDirected_eq_shift_of_rounded_acc .positive root te acc true
              rw [hform] at hrd
              rw [hform'] at hrd
              by_cases hz : (firstRoundedAcc .positive root te acc true).1 = 0
              · exact hz
              · have hne := shiftToTarget_short_ne_zero_of_first (s := .positive)
                  (m := root) (e := te) (acc := acc) (up := true) hz
                simp only at hrd
                rw [dite_eq_right hne] at hrd
                cases hrd
            -- downward 0 possible? upward of root>0...
            -- if firstRounded is 0, contradiction with pos_hi ≥ 1 when inexact,
            -- or exact firstRounded of root≥1
            have hrpos : 0 < root := sqrtCore_root_pos hm
            cases hacc : acc with
            | exact =>
              have : (firstRoundedAcc .positive root te .exact true).1 =
                  (firstRounded .positive root te true).1 := by
                simp [firstRoundedAcc_exact]
              rw [hacc] at h0
              have hge := signedVal_firstRounded_hi .positive root te
              rw [← this, h0, signedVal_zero] at hge
              exact (Rat.lt_iff_le_and_not_ge.mp (mag_pos hrpos)).2 hge
            | inexact o =>
              have hge := firstRoundedAcc_pos_hi_inexact_ge_succ root te o
              rw [hacc] at h0
              rw [h0, signedVal_zero] at hge
              exact (Rat.lt_iff_le_and_not_ge.mp (mag_pos (Nat.succ_pos root))).2 hge
          exact this.elim
        · rw [heq]
          have hrd : roundDirected .positive root te acc true =
              .finite .positive m' e' h' := heq ▸ sqrtU_finite_eq_round hm true
          have henc := hiEncloses_packDirected_of_shaped .positive h' hsh
            (signedVal .positive m' e') (by simp [hiEncloses?, hiEncloses, signedVal])
          have hge : r ≤ mag m' e' := by
            cases hacc : acc with
            | exact =>
              have heqmag := sqrtCore_mag_eq_of_exact (by
                simpa [acc] using hacc)
              have hge' : mag root te ≤ mag m' e' := by
                have hrd' : roundDirected .positive root te .exact true =
                    .finite .positive m' e' h' := by
                  simpa [acc, hacc] using hrd
                exact mag_roundDirected_pos_hi_exact (m := root) (e := te) (e' := e') hrd'
              have hrr : r * r = mag root te * mag root te :=
                hsq'.trans heqmag.symm
              have h1 := sq_le_sq_of_nonneg (mag_nonneg root te) hge'
              exact le_of_sq_le_sq hr (mag_nonneg _ _) (hrr ▸ h1)
            | inexact o =>
              have hrd' : roundDirected .positive root te (.inexact o) true =
                  .finite .positive m' e' h' := by
                simpa [acc, hacc] using hrd
              have hge' : mag (root + 1) te ≤ mag m' e' :=
                mag_roundDirected_pos_hi_inexact hrd'
              have : r * r < mag (root + 1) te * mag (root + 1) te :=
                hsq' ▸ hhi_sq
              have : r * r ≤ mag m' e' * mag m' e' :=
                Rat.le_of_lt (rat_lt_of_lt_of_le this
                  (sq_le_sq_of_nonneg (mag_nonneg _ _) hge'))
              exact le_of_sq_le_sq hr (mag_nonneg _ _) this
          exact hiEncloses_of_ge henc (by simpa [signedVal] using hge)

theorem not_lt_zero_of_zero_le {f : Float}
    (hle : (0 : Float) ≤ f) : ¬ f < 0 := by
  intro hlt
  have hltU : (unpackBits f.toBits).lt (unpackBits (0 : Float).toBits) = true :=
    (float_lt_iff f 0).mp hlt
  have hleU : (unpackBits (0 : Float).toBits).le (unpackBits f.toBits) = true :=
    (float_le_iff 0 f).mp hle
  rcases unpack_float_zero with ⟨sz, hsz⟩
  rw [hsz] at hltU hleU
  cases huf : unpackBits f.toBits with
  | notANumber => simp [huf, UnpackedFloat.le, UnpackedFloat.compare, Option.any] at hleU
  | infinity s =>
    cases s <;> simp [huf, UnpackedFloat.lt, UnpackedFloat.le, UnpackedFloat.compare,
      Option.any] at hltU hleU
  | zero s =>
    simp [huf, UnpackedFloat.lt, UnpackedFloat.compare] at hltU
  | finite s m e hm =>
    cases s <;> simp [huf, UnpackedFloat.lt, UnpackedFloat.le, UnpackedFloat.compare,
      Option.any] at hltU hleU

/-- If `qa ≤ r²` with `0 ≤ r` and `0 ≤ qa`, downward sqrt encloses `r`. -/
theorem sqrtDown_le_of_sq_ge {a : UInt64} {qa r : Rat}
    (ha : bitsToRat? a = some qa) (hqa : 0 ≤ qa) (hr : 0 ≤ r)
    (hle : qa ≤ r * r) :
    loEncloses? (bitsToEVal (sqrtDown a)) r := by
  simp only [sqrtDown, Interval64.Spec.sqrt]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s, hu, rfl⟩
    rw [hu]
    simp only [sqrtU]
    exact loEncloses_packDirected_zero_val _ _ _
      (by simp [loEncloses?, loEncloses]; exact hr)
  · rcases hfa with ⟨s, m, e, hm, hu, rfl, hc⟩
    cases s with
    | negative =>
      have : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
      exact ((Rat.lt_iff_le_and_not_ge.mp this).2 hqa).elim
    | positive =>
      rw [hu]
      have hqa' : mag m e ≤ r * r := by simpa [signedVal] using hle
      have hs : m < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hc
      have hbr := sqrtCore_mag_bracket m e
      let root := (sqrtCore spec64 m e).1
      let te := (sqrtCore spec64 m e).2.1
      let acc := (sqrtCore spec64 m e).2.2
      have hlo_sq : mag root te * mag root te ≤ mag m e := hbr.1
      have hshape_lo := sqrtU_shaped_or_zero (e := e) hm hs false
      rcases hshape_lo with ⟨z, heq⟩ | ⟨m', e', h', heq, hsh⟩
      · rw [heq]
        exact loEncloses_packDirected_zero_val _ _ _
          (by simp [loEncloses?, loEncloses]; exact hr)
      · rw [heq]
        have hrd : roundDirected .positive root te acc false =
            .finite .positive m' e' h' := heq ▸ sqrtU_finite_eq_round hm false
        have hler : mag m' e' ≤ mag root te := mag_roundDirected_pos_lo hrd
        have hsqle : mag m' e' * mag m' e' ≤ r * r :=
          Rat.le_trans (sq_le_sq_of_nonneg (mag_nonneg _ _) hler)
            (Rat.le_trans hlo_sq hqa')
        have hle' : mag m' e' ≤ r :=
          le_of_sq_le_sq (mag_nonneg _ _) hr hsqle
        have henc := loEncloses_packDirected_of_shaped .positive h' hsh
          (signedVal .positive m' e') (by simp [loEncloses?, loEncloses, signedVal])
        exact loEncloses_of_le henc (by simpa [signedVal] using hle')

/-- If `r² ≤ qa` with `0 ≤ r` and `0 ≤ qa`, upward sqrt encloses `r`. -/
theorem sqrtUp_ge_of_sq_le {a : UInt64} {qa r : Rat}
    (ha : bitsToRat? a = some qa) (hqa : 0 ≤ qa) (hr : 0 ≤ r)
    (hge : r * r ≤ qa) :
    hiEncloses? (bitsToEVal (sqrtUp a)) r := by
  simp only [sqrtUp, Interval64.Spec.sqrt]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s, hu, rfl⟩
    have hr0 : r = 0 := by
      have h0 : r * r = 0 := by
        have : r * r ≤ 0 := by simpa using hge
        have : 0 ≤ r * r := by
          simpa [Rat.zero_mul] using
            sq_le_sq_of_nonneg (by decide : (0 : Rat) ≤ 0) hr
        exact Rat.le_antisymm ‹r * r ≤ 0› this
      by_cases hz : r = 0
      · exact hz
      · have hp : 0 < r := Rat.lt_of_le_of_ne hr (Ne.symm hz)
        exact (ne_of_pos_rat (Rat.mul_pos hp hp) h0).elim
    rw [hu]
    simp only [sqrtU]
    exact hiEncloses_packDirected_zero_val _ _ _
      (by simp [hiEncloses?, hiEncloses, hr0])
  · rcases hfa with ⟨s, m, e, hm, hu, rfl, hc⟩
    cases s with
    | negative =>
      have : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
      exact ((Rat.lt_iff_le_and_not_ge.mp this).2 hqa).elim
    | positive =>
      rw [hu]
      have hge'qa : r * r ≤ mag m e := by simpa [signedVal] using hge
      have hs : m < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hc
      have hbr := sqrtCore_mag_bracket m e
      let root := (sqrtCore spec64 m e).1
      let te := (sqrtCore spec64 m e).2.1
      let acc := (sqrtCore spec64 m e).2.2
      have hhi_sq : mag m e < mag (root + 1) te * mag (root + 1) te := hbr.2 hm
      have hshape_hi := sqrtU_shaped_or_zero (e := e) hm hs true
      rcases hshape_hi with ⟨z, heq⟩ | ⟨m', e', h', heq, hsh⟩
      · have hrd : sqrtU (.finite .positive m e hm) true = .zero z := heq
        have hform : sqrtU (.finite .positive m e hm) true =
            roundDirected .positive root te acc true := rfl
        have : False := by
          have h0 : (firstRoundedAcc .positive root te acc true).1 = 0 := by
            have hform' := roundDirected_eq_shift_of_rounded_acc .positive root te acc true
            rw [hform] at hrd
            rw [hform'] at hrd
            by_cases hz : (firstRoundedAcc .positive root te acc true).1 = 0
            · exact hz
            · have hne := shiftToTarget_short_ne_zero_of_first (s := .positive)
                (m := root) (e := te) (acc := acc) (up := true) hz
              simp only at hrd
              rw [dite_eq_right hne] at hrd
              cases hrd
          have hrpos : 0 < root := sqrtCore_root_pos hm
          cases hacc : acc with
          | exact =>
            have : (firstRoundedAcc .positive root te .exact true).1 =
                (firstRounded .positive root te true).1 := by
              simp [firstRoundedAcc_exact]
            rw [hacc] at h0
            have hge0 := signedVal_firstRounded_hi .positive root te
            rw [← this, h0, signedVal_zero] at hge0
            exact (Rat.lt_iff_le_and_not_ge.mp (mag_pos hrpos)).2 hge0
          | inexact o =>
            have hge0 := firstRoundedAcc_pos_hi_inexact_ge_succ root te o
            rw [hacc] at h0
            rw [h0, signedVal_zero] at hge0
            exact (Rat.lt_iff_le_and_not_ge.mp (mag_pos (Nat.succ_pos root))).2 hge0
        exact this.elim
      · rw [heq]
        have hrd : roundDirected .positive root te acc true =
            .finite .positive m' e' h' := heq ▸ sqrtU_finite_eq_round hm true
        have henc := hiEncloses_packDirected_of_shaped .positive h' hsh
          (signedVal .positive m' e') (by simp [hiEncloses?, hiEncloses, signedVal])
        have hge : r ≤ mag m' e' := by
          cases hacc : acc with
          | exact =>
            have heqmag := sqrtCore_mag_eq_of_exact (by
              simpa [acc] using hacc)
            have hroot_le : mag root te ≤ mag m' e' := by
              have hrd' : roundDirected .positive root te .exact true =
                  .finite .positive m' e' h' := by
                simpa [acc, hacc] using hrd
              exact mag_roundDirected_pos_hi_exact (m := root) (e := te) (e' := e') hrd'
            have hrr : r * r ≤ mag root te * mag root te := by
              have : r * r ≤ mag m e := hge'qa
              rwa [← heqmag] at this
            have h1 := sq_le_sq_of_nonneg (mag_nonneg root te) hroot_le
            exact le_of_sq_le_sq hr (mag_nonneg _ _) (Rat.le_trans hrr h1)
          | inexact o =>
            have hrd' : roundDirected .positive root te (.inexact o) true =
                .finite .positive m' e' h' := by
              simpa [acc, hacc] using hrd
            have hroot_le : mag (root + 1) te ≤ mag m' e' :=
              mag_roundDirected_pos_hi_inexact hrd'
            have : r * r < mag (root + 1) te * mag (root + 1) te :=
              rat_lt_of_le_of_lt hge'qa hhi_sq
            have : r * r ≤ mag m' e' * mag m' e' :=
              Rat.le_of_lt (rat_lt_of_lt_of_le this
                (sq_le_sq_of_nonneg (mag_nonneg _ _) hroot_le))
            exact le_of_sq_le_sq hr (mag_nonneg _ _) this
        exact hiEncloses_of_ge henc (by simpa [signedVal] using hge)

theorem loEncloses_sqrtDown {a : Float} {qa r : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hqa : 0 ≤ qa) (hr : 0 ≤ r)
    (hle : qa ≤ r * r) :
    loEncloses? (bitsToEVal (Interval64.Directed.sqrtDown a).toBits) r := by
  have h := sqrtDown_le_of_sq_ge ha hqa hr hle
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  rw [sqrtDown_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

theorem hiEncloses_sqrtUp {a : Float} {qa r : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hqa : 0 ≤ qa) (hr : 0 ≤ r)
    (hge : r * r ≤ qa) :
    hiEncloses? (bitsToEVal (Interval64.Directed.sqrtUp a).toBits) r := by
  have h := sqrtUp_ge_of_sq_le ha hqa hr hge
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  rw [sqrtUp_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

/-- Interval square-root membership. If `0 ≤ r`, `r * r = x`, and `x ∈ X`
    with finite endpoints, then `r ∈ sqrt(X)`. Matches `Interval64.sqrt`:
    NaN or `hi < 0` would yield `invalid` (which has no rational members),
    but those cases cannot arise under these hypotheses; a negative `lo`
    is clipped to `0.0` so the lower bound is `sqrt(0) = 0`. -/
theorem sqrt_mem_iv {x r : Rat} {X : Interval64}
    (hx : MemIv x X) (hx0 : 0 ≤ x) (hr : 0 ≤ r) (hsq : r * r = x)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q) :
    MemIv r (Interval64.sqrt X) := by
  rcases hXlo with ⟨alo, hAlo⟩
  rcases hXhi with ⟨ahi, hAhi⟩
  have hxl : alo ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hAlo] at this
    exact this
  have hxh : x ≤ ahi := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hAhi] at this
    exact this
  have hnan : (X.lo.isNaN || X.hi.isNaN) = false := by
    simp only [Bool.or_eq_false_iff]
    exact ⟨not_isNaN_of_MemIv_lo hx, not_isNaN_of_MemIv_hi hx⟩
  have hahi0 : 0 ≤ ahi := Rat.le_trans hx0 hxh
  have hhi0 : ¬ X.hi < 0 :=
    not_lt_zero_of_zero_le ((zero_le_iff_rat hAhi).mpr hahi0)
  have hhiDec : decide (X.hi < 0) = false := decide_eq_false hhi0
  have heq : Interval64.sqrt X =
      ⟨Interval64.Directed.sqrtDown (if decide (X.lo < 0) then (0.0 : Float) else X.lo),
        Interval64.Directed.sqrtUp X.hi⟩ := by
    unfold Interval64.sqrt
    rw [hnan, hhiDec]
    rw [ite_eq_right (by decide : ¬ (false = true))]
    rw [ite_eq_right (by decide : ¬ (false = true))]
  cases hloz : decide (X.lo < 0) with
  | true =>
    rw [heq]
    simp only [hloz]
    have hlo : loEncloses? (bitsToEVal (Interval64.Directed.sqrtDown (0.0 : Float)).toBits) r :=
      loEncloses_sqrtDown bitsToRat?_float_zero (Rat.le_refl) hr (by
        simpa [Rat.zero_mul, hsq] using hx0)
    have hhi : hiEncloses? (bitsToEVal (Interval64.Directed.sqrtUp X.hi).toBits) r :=
      hiEncloses_sqrtUp hAhi hahi0 hr (by simpa [hsq] using hxh)
    exact ⟨hlo, hhi⟩
  | false =>
    have hnlo : ¬ X.lo < 0 := of_decide_eq_false hloz
    have h0lo : (0 : Float) ≤ X.lo :=
      le_of_not_lt_of_rats hAlo bitsToRat?_float_zero hnlo
    have halo0 : 0 ≤ alo := (zero_le_iff_rat hAlo).mp h0lo
    rw [heq]
    simp only [hloz]
    have hlo : loEncloses? (bitsToEVal (Interval64.Directed.sqrtDown X.lo).toBits) r :=
      loEncloses_sqrtDown hAlo halo0 hr (by simpa [hsq] using hxl)
    have hhi : hiEncloses? (bitsToEVal (Interval64.Directed.sqrtUp X.hi).toBits) r :=
      hiEncloses_sqrtUp hAhi hahi0 hr (by simpa [hsq] using hxh)
    exact ⟨hlo, hhi⟩

/-- The representable root cannot be subnormal if `sqrtCore` used a
    normal-range target exponent. -/
theorem sqrt_rep_not_subnormal {m : Nat} {e : Int} {m' : Nat} {e' : Int}
    (h0 : 0 < m) (hs : m < 2 ^ 53) (_h' : 0 < m')
    (hgt : spec64.minExponent < (sqrtCore spec64 m e).2.1)
    (hv : mag m e = mag m' e' * mag m' e')
    (hsub : IsSubnormal m' e') : False := by
  have hq := sqrtCore_root_ge_pow52_of_gt_min h0 hs hgt
  let root := (sqrtCore spec64 m e).1
  let te := (sqrtCore spec64 m e).2.1
  have hlo_sq : mag root te * mag root te ≤ mag m e :=
    (sqrtCore_mag_bracket m e).1
  have hroot_le : mag root te ≤ mag m' e' :=
    le_of_sq_le_sq (mag_nonneg _ _) (mag_nonneg _ _) (by
      rw [← hv]; exact hlo_sq)
  have hge : mag (2 ^ 52) te ≤ mag m' e' :=
    Rat.le_trans (mag_le_mag hq) hroot_le
  have hlt : mag m' e' < mag (2 ^ 52) te := by
    have h1 : mag m' e' < mag (2 ^ 52) e' := mag_lt_mag hsub.2.2
    have h2 : mag (2 ^ 52) e' ≤ mag (2 ^ 52) te := by
      rw [hsub.1]
      exact mag_le_of_exp_le (Int.le_of_lt hgt)
    exact rat_lt_of_lt_of_le h1 h2
  exact (Rat.lt_iff_le_and_not_ge.mp hlt).2 hge

theorem sqrt_rep_te_le_exp {m : Nat} {e : Int} {m' : Nat} {e' : Int}
    (h0 : 0 < m) (hs : m < 2 ^ 53) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m e = mag m' e' * mag m' e') :
    (sqrtCore spec64 m e).2.1 ≤ e' := by
  by_cases hte : (sqrtCore spec64 m e).2.1 ≤ spec64.minExponent
  · have hmin : spec64.minExponent ≤ e' := by
      cases hc with
      | inl hsub => exact Int.le_of_eq hsub.1.symm
      | inr hn => exact hn.1
    exact Int.le_trans hte hmin
  · have hgt : spec64.minExponent < (sqrtCore spec64 m e).2.1 :=
      Int.lt_of_not_ge hte
    have hnorm : IsNormal m' e' := by
      cases hc with
      | inl hsub => exact (sqrt_rep_not_subnormal h0 hs h' hgt hv hsub).elim
      | inr hn => exact hn
    have hq := sqrtCore_root_ge_pow52_of_gt_min h0 hs hgt
    let root := (sqrtCore spec64 m e).1
    let te := (sqrtCore spec64 m e).2.1
    have hlo_sq : mag root te * mag root te ≤ mag m e :=
      (sqrtCore_mag_bracket m e).1
    have hroot_le : mag root te ≤ mag m' e' :=
      le_of_sq_le_sq (mag_nonneg _ _) (mag_nonneg _ _) (by
        rw [← hv]; exact hlo_sq)
    have hge : mag (2 ^ 52) te ≤ mag m' e' :=
      Rat.le_trans (mag_le_mag hq) hroot_le
    have hhi : mag m' e' < mag (2 ^ 52) (e' + 1) := by
      have : mag m' e' < mag (2 ^ 53) e' := mag_lt_mag hnorm.2.2.2
      rwa [mag_pow53_eq] at this
    have hlt : mag (2 ^ 52) te < mag (2 ^ 52) (e' + 1) :=
      rat_lt_of_le_of_lt hge hhi
    have hnot : ¬ e' + 1 ≤ te := fun hle =>
      (Rat.lt_iff_le_and_not_ge.mp hlt).2 (mag_le_of_exp_le hle)
    exact Int.lt_add_one_iff.mp (Int.lt_of_not_ge hnot)

theorem two_mul_toNat_eq {a b : Int} (h : a ≤ b) :
    ((2 * (b - a).toNat : Nat) : Int) = 2 * (b - a) := by
  have hnn : 0 ≤ b - a := Int.sub_nonneg_of_le h
  have : ((2 * (b - a).toNat : Nat) : Int) =
      (2 : Int) * ((b - a).toNat : Int) := by
    simp [Int.natCast_mul]
  rw [this, Int.toNat_of_nonneg hnn]

theorem sqrtCore_M_eq_of_rep {m : Nat} {e : Int} {m' : Nat} {e' : Int}
    (h0 : 0 < m) (hs : m < 2 ^ 53) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m e = mag m' e' * mag m' e') :
    let te := (sqrtCore spec64 m e).2.1
    let k := (e - 2 * te).toNat
    m <<< k = m' * m' * 2 ^ (2 * (e' - te).toNat) := by
  intro te k
  have hte_le : te ≤ e' := sqrt_rep_te_le_exp h0 hs h' hc hv
  have hM : mag (m <<< k) (2 * te) = mag m e := by
    simpa [te, k] using mag_shiftLeft_two_te m e
  have hsq : mag m' e' * mag m' e' = mag (m' * m') (2 * e') := mag_sq_two m' e'
  have heq : mag (m <<< k) (2 * te) = mag (m' * m') (2 * e') :=
    hM.trans (hv.trans hsq)
  have hpow : pow2 (2 * e') = pow2 (2 * te) * pow2 (2 * (e' - te)) := by
    have : 2 * te + 2 * (e' - te) = 2 * e' := by omega
    rw [← pow2_add, this]
  have hmul : ((m <<< k : Nat) : Rat) * pow2 (2 * te) =
      ((m' * m' : Nat) : Rat) * pow2 (2 * e') := by
    simpa [mag] using heq
  have hP : pow2 (2 * te) ≠ 0 := pow2_ne_zero _
  have hmul' : ((m <<< k : Nat) : Rat) * pow2 (2 * te) =
      (((m' * m' : Nat) : Rat) * pow2 (2 * (e' - te))) * pow2 (2 * te) := by
    rw [hmul, hpow, Rat.mul_comm (pow2 (2 * te)), ← Rat.mul_assoc]
  have hA : ((m <<< k : Nat) : Rat) =
      ((m' * m' : Nat) : Rat) * pow2 (2 * (e' - te)) := by
    have h1 : ((m <<< k : Nat) : Rat) * pow2 (2 * te) * (pow2 (2 * te))⁻¹ =
        (((m' * m' : Nat) : Rat) * pow2 (2 * (e' - te))) * pow2 (2 * te) *
          (pow2 (2 * te))⁻¹ := by
      rw [hmul']
    simpa [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 (2 * te)) hP, Rat.mul_one] using h1
  have hpow' : pow2 (2 * (e' - te)) =
      ((2 ^ (2 * (e' - te).toNat) : Nat) : Rat) := by
    have hcast : ((2 * (e' - te).toNat : Nat) : Int) = 2 * (e' - te) :=
      two_mul_toNat_eq hte_le
    have : pow2 (2 * (e' - te)) = pow2 ((2 * (e' - te).toNat : Nat) : Int) := by
      rw [hcast]
    rw [this]
    exact pow2_toNat_of_nonneg (Int.natCast_nonneg _)
  have : ((m <<< k : Nat) : Rat) =
      ((m' * m' * 2 ^ (2 * (e' - te).toNat) : Nat) : Rat) := by
    rw [hA, hpow', ← Rat.natCast_mul]
  exact Rat.natCast_inj.mp this

theorem mul_sq_pow {m' n : Nat} :
    m' * m' * (2 ^ n * 2 ^ n) = (m' * 2 ^ n) * (m' * 2 ^ n) := by
  calc
    m' * m' * (2 ^ n * 2 ^ n)
        = m' * (m' * (2 ^ n * 2 ^ n)) := by rw [Nat.mul_assoc]
    _ = m' * (m' * 2 ^ n * 2 ^ n) := by rw [← Nat.mul_assoc m' (2 ^ n)]
    _ = m' * (2 ^ n * m' * 2 ^ n) := by rw [Nat.mul_comm m' (2 ^ n)]
    _ = m' * (2 ^ n * (m' * 2 ^ n)) := by rw [Nat.mul_assoc (2 ^ n)]
    _ = (m' * 2 ^ n) * (m' * 2 ^ n) := by rw [← Nat.mul_assoc]

theorem sqrtCore_exact_of_rep {m : Nat} {e : Int} {m' : Nat} {e' : Int}
    (h0 : 0 < m) (hs : m < 2 ^ 53) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m e = mag m' e' * mag m' e') :
    (sqrtCore spec64 m e).2.2 = .exact ∧
      mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 = mag m' e' := by
  have hM := sqrtCore_M_eq_of_rep h0 hs h' hc hv
  let te := (sqrtCore spec64 m e).2.1
  let k := (e - 2 * te).toNat
  let n := (e' - te).toNat
  have hsqN : m <<< k = (m' * 2 ^ n) * (m' * 2 ^ n) := by
    have hpow : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
      rw [Nat.two_mul, Nat.pow_add]
    have : m' * m' * 2 ^ (2 * n) = (m' * 2 ^ n) * (m' * 2 ^ n) := by
      rw [hpow, mul_sq_pow]
    simpa [te, k, n] using hM.trans this
  have hroot : (sqrtCore spec64 m e).1 = Nat.sqrt (m <<< k) := rfl
  have hsqrt : Nat.sqrt (m <<< k) = m' * 2 ^ n :=
    sqrt_eq_of_mul_self hsqN
  have hex : (sqrtCore spec64 m e).2.2 = .exact :=
    (sqrtCore_acc_exact_iff m e).mpr (by
      have : m <<< k = Nat.sqrt (m <<< k) * Nat.sqrt (m <<< k) := by
        rw [hsqrt, ← hsqN]
      simpa [te, k] using this)
  have hmageq : mag (sqrtCore spec64 m e).1 te = mag m' e' := by
    rw [hroot, hsqrt]
    have hte_le : te ≤ e' := sqrt_rep_te_le_exp h0 hs h' hc hv
    have hn : (n : Int) = e' - te := Int.toNat_of_nonneg (Int.sub_nonneg_of_le hte_le)
    have heq : e' - (n : Int) = te := by omega
    have := mag_mul_pow2 m' e' n
    rwa [heq] at this
  exact ⟨hex, by simpa [te] using hmageq⟩

/-- If a nonnegative square root of a finite `qa` is itself a finite binary64
    value, both directed square roots evaluate to that exact value. -/
theorem sqrt_exact {a : UInt64} {qa r : Rat}
    (ha : bitsToRat? a = some qa) (hr : 0 ≤ r) (hsq : r * r = qa)
    (hrep : ∃ c, bitsToRat? c = some r) :
    bitsToRat? (sqrtDown a) = some r ∧ bitsToRat? (sqrtUp a) = some r := by
  rcases representable_cases hrep with hq0 | hqf
  · have hqa0 : qa = 0 := by simpa [hq0, Rat.zero_mul] using hsq.symm
    have hboth : bitsToRat? (sqrtDown a) = some 0 ∧
        bitsToRat? (sqrtUp a) = some 0 := by
      simp only [sqrtDown, sqrtUp, Interval64.Spec.sqrt]
      rcases bitsToRat?_cases ha with hza | hfa
      · rcases hza with ⟨s, hu, rfl⟩
        rw [hu]
        simp only [sqrtU]
        constructor <;> exact bitsToRat?_packDirected_zero _ _
      · rcases hfa with ⟨s, m, e, hm, hu, rfl, _⟩
        have : signedVal s m e = 0 := hqa0
        exact (signedVal_ne_zero_of_pos hm this).elim
    rw [hq0]
    exact hboth
  · rcases hqf with ⟨sCan, m', e', h', hc, hvq⟩
    have hspos : sCan = .positive := by
      cases sCan with
      | positive => rfl
      | negative =>
        have : signedVal .negative m' e' < 0 := signedVal_neg_lt_zero h'
        exact ((Rat.lt_iff_le_and_not_ge.mp this).2 (hvq ▸ hr)).elim
    simp only [sqrtDown, sqrtUp, Interval64.Spec.sqrt]
    rcases bitsToRat?_cases ha with hza | hfa
    · rcases hza with ⟨_, _, rfl⟩
      have : r * r = 0 := hsq
      have hr0 : r = 0 := by
        by_cases hz : r = 0
        · exact hz
        · have hp : 0 < r := Rat.lt_of_le_of_ne hr (Ne.symm hz)
          exact (ne_of_pos_rat (Rat.mul_pos hp hp) this).elim
      exact (signedVal_ne_zero_of_pos h' (hvq.symm.trans hr0)).elim
    · rcases hfa with ⟨s, m, e, hm, hu, rfl, hcan⟩
      cases s with
      | negative =>
        have : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
        have hqa : 0 ≤ signedVal .negative m e := by
          simpa [hsq, Rat.zero_mul] using
            sq_le_sq_of_nonneg (by decide : (0 : Rat) ≤ 0) hr
        exact ((Rat.lt_iff_le_and_not_ge.mp this).2 hqa).elim
      | positive =>
        rw [hu]
        have hs : m < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hcan
        have hv : mag m e = mag m' e' * mag m' e' := by
          have h1 : mag m e = r * r := by
            simpa [signedVal] using hsq.symm
          have h2 : r = mag m' e' := by
            simpa [signedVal, hspos] using hvq
          rw [h1, h2]
        have ⟨hex, hmageq⟩ := sqrtCore_exact_of_rep hm hs h' hc hv
        let root := (sqrtCore spec64 m e).1
        let te := (sqrtCore spec64 m e).2.1
        have hvprod : signedVal .positive root te = signedVal sCan m' e' := by
          simp [signedVal, hspos, show mag root te = mag m' e' from hmageq]
        have hvprod' : signedVal .positive root te = signedVal .positive m' e' := by
          simpa [hspos] using hvprod
        constructor
        · have heq :=
            roundDirected_eq_of_canonical .positive root te false h' hc hvprod'
          have hsqrt :
              sqrtU (.finite .positive m e hm) false =
                roundDirected .positive root te (sqrtCore spec64 m e).2.2 false :=
            rfl
          rw [hsqrt, hex, heq]
          simpa [hvq, hspos] using
            bitsToRat?_packDirected_canonical false .positive h' hc
        · have heq :=
            roundDirected_eq_of_canonical .positive root te true h' hc hvprod'
          have hsqrt :
              sqrtU (.finite .positive m e hm) true =
                roundDirected .positive root te (sqrtCore spec64 m e).2.2 true :=
            rfl
          rw [hsqrt, hex, heq]
          simpa [hvq, hspos] using
            bitsToRat?_packDirected_canonical true .positive h' hc

theorem rat_three_sq : (3 : Rat) * 3 = 9 := by
  have h3 : (3 : Rat) = ((3 : Int) : Rat) := rfl
  have h9 : (9 : Rat) = ((9 : Int) : Rat) := rfl
  rw [h3, h9, ← Rat.intCast_mul]; rfl

theorem mag_nat (n : Nat) : mag n 0 = (n : Rat) := by
  simp [mag, pow2_zero]

theorem val_three : signedVal .positive (3 * 2 ^ 51) (-51) = 3 := by
  have he : (0 : Int) - (51 : Nat) = (-51 : Int) := by decide
  have h' : mag (3 * 2 ^ 51) ((0 : Int) - (51 : Nat)) = mag 3 0 :=
    mag_mul_pow2 3 0 51
  have h'' : mag (3 * 2 ^ 51) (-51) = mag 3 0 := he ▸ h'
  simp only [signedVal]
  rw [h'', mag_nat]
  rfl

theorem val_nine : signedVal .positive (9 * 2 ^ 49) (-49) = 9 := by
  have he : (0 : Int) - (49 : Nat) = (-49 : Int) := by decide
  have h' : mag (9 * 2 ^ 49) ((0 : Int) - (49 : Nat)) = mag 9 0 :=
    mag_mul_pow2 9 0 49
  have h'' : mag (9 * 2 ^ 49) (-49) = mag 9 0 := he ▸ h'
  simp only [signedVal]
  rw [h'', mag_nat]
  rfl

theorem isNormal_three : IsNormal (3 * 2 ^ 51) (-51) := by
  unfold IsNormal
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · rw [minExponent_spec64]; decide
  · unfold overflowExponent; decide
  · decide
  · decide

theorem isNormal_nine : IsNormal (9 * 2 ^ 49) (-49) := by
  unfold IsNormal
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · rw [minExponent_spec64]; decide
  · unfold overflowExponent; decide
  · decide
  · decide

def bitsThree : UInt64 :=
  packBits (.finite .positive (3 * 2 ^ 51) (-51)
    (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51)))

def bitsNine : UInt64 :=
  packBits (.finite .positive (9 * 2 ^ 49) (-49)
    (Nat.mul_pos (by decide : 0 < 9) (Nat.two_pow_pos 49)))

theorem bitsToRat?_three : bitsToRat? bitsThree = some 3 := by
  rw [bitsThree, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51))
      (Or.inr isNormal_three), val_three]

theorem bitsToRat?_nine : bitsToRat? bitsNine = some 9 := by
  rw [bitsNine, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 9) (Nat.two_pow_pos 49))
      (Or.inr isNormal_nine), val_nine]

theorem nine_toBits : (9.0 : Float).toBits = bitsNine := by decide
theorem three_toBits : (3.0 : Float).toBits = bitsThree := by decide

/-- Concrete corollary: both directed square roots of `9` are exactly `3`. -/
theorem sqrt_nine_exact :
    bitsToRat? (sqrtDown (9.0 : Float).toBits) = some 3 ∧
    bitsToRat? (sqrtUp (9.0 : Float).toBits) = some 3 := by
  rw [nine_toBits]
  exact sqrt_exact bitsToRat?_nine (by decide) rat_three_sq ⟨bitsThree, bitsToRat?_three⟩

end Interval64Proofs.Sqrt
