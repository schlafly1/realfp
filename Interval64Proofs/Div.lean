/-
Bits-level directed division enclosure, including inexact `divCore`
residuals, and interval membership for `Interval64.div`.
-/
import Interval64Proofs.RoundInexact
import Interval64Proofs.Mul
import Interval64Proofs.IntervalMem
import Interval64Proofs.Sub

namespace Interval64Proofs.Div

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
open Interval64Proofs.Sub
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Membership in `whole` -/

theorem packBits_posInf : packBits (.infinity .positive) = posInf := by decide
theorem packBits_negInf : packBits (.infinity .negative) = negInf := by decide

theorem bitsToEVal_posInf : bitsToEVal posInf = some .posInf := by
  have := bitsToEVal_pack_inf .positive
  rw [packBits_posInf] at this
  exact this

theorem bitsToEVal_negInf : bitsToEVal negInf = some .negInf := by
  have := bitsToEVal_pack_inf .negative
  rw [packBits_negInf] at this
  exact this

theorem inf_toBits : (Float.inf).toBits = posInf := by decide
theorem negInf_toBits : (-Float.inf).toBits = negInf := by decide

/-- Every rational is a member of `whole = [-∞, +∞]`. -/
theorem memIv_whole (x : Rat) : MemIv x Interval64.whole := by
  simp [MemIv, Mem, Interval64.whole, negInf_toBits, inf_toBits,
    bitsToEVal_negInf, bitsToEVal_posInf, loEncloses?, hiEncloses?,
    loEncloses, hiEncloses]

/-! ### Local rational helpers -/

theorem rat_nat_ne_zero {n : Nat} (h : 0 < n) : (n : Rat) ≠ 0 := by
  intro hz
  exact Nat.ne_of_gt h (by
    have : ((n : Nat) : Rat) = ((0 : Nat) : Rat) := by simpa using hz
    exact Rat.natCast_inj.mp this)

theorem rat_nat_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) :=
  (Rat.natCast_lt_natCast).mpr h

theorem inv_neg (a : Rat) : (-a)⁻¹ = -(a⁻¹) := by
  by_cases h : a = 0
  · simp [h, Rat.neg_zero, Rat.inv_zero]
  · apply Rat.inv_eq_of_mul_eq_one
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_inv_cancel a h]

theorem neg_div (a b : Rat) : (-a) / b = -(a / b) := by
  rw [Rat.div_def, Rat.div_def, Rat.neg_mul]

theorem div_neg (a b : Rat) : a / (-b) = -(a / b) := by
  rw [Rat.div_def, Rat.div_def, inv_neg, Rat.mul_neg]

theorem mul_left_comm_rat (a b c : Rat) : a * (b * c) = b * (a * c) := by
  rw [← Rat.mul_assoc, Rat.mul_comm a, Rat.mul_assoc]

theorem add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

theorem lt_add_of_pos_right (a b : Rat) (h : 0 < b) : a < a + b := by
  have := (Rat.add_lt_add_left (a := 0) (b := b) (c := a)).mpr h
  simpa [Rat.add_zero] using this

/-! ### Sign of a quotient and algebra of magnitudes -/

theorem sign_div_eq_mul (s₁ s₂ : Sign) : s₁ / s₂ = s₁ * s₂ := by
  cases s₁ <;> cases s₂ <;> rfl

def signedOf (s : Sign) (r : Rat) : Rat :=
  match s with
  | .positive => r
  | .negative => -r

theorem signedVal_signedOf (s : Sign) (m : Nat) (e : Int) :
    signedVal s m e = signedOf s (mag m e) :=
  rfl

theorem signedOf_div (s₁ s₂ : Sign) (a b : Rat) :
    signedOf s₁ a / signedOf s₂ b = signedOf (s₁ / s₂) (a / b) := by
  cases s₁ <;> cases s₂
  · have h : (Sign.negative / Sign.negative : Sign) = .positive := rfl
    simp [signedOf, h, neg_div, div_neg, Rat.neg_neg]
  · have h : (Sign.negative / Sign.positive : Sign) = .negative := rfl
    simp [signedOf, h, neg_div, div_neg, Rat.neg_neg]
  · have h : (Sign.positive / Sign.negative : Sign) = .negative := rfl
    simp [signedOf, h, neg_div, div_neg, Rat.neg_neg]
  · have h : (Sign.positive / Sign.positive : Sign) = .positive := rfl
    simp [signedOf, h, neg_div, div_neg, Rat.neg_neg]

theorem mag_ne_zero {m : Nat} {e : Int} (h : 0 < m) : mag m e ≠ 0 := by
  intro hz
  have hp := mag_pos (m := m) (e := e) h
  rw [hz] at hp
  exact Rat.lt_irrefl hp

theorem mag_div (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    mag m₁ e₁ / mag m₂ e₂ = (m₁ : Rat) / (m₂ : Rat) * pow2 (e₁ - e₂) := by
  unfold mag
  have : (m₁ : Rat) * pow2 e₁ / ((m₂ : Rat) * pow2 e₂) =
      ((m₁ : Rat) / (m₂ : Rat)) * (pow2 e₁ / pow2 e₂) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
    -- m₁ * p1 * (p2⁻¹ * m₂⁻¹) = m₁ * m₂⁻¹ * (p1 * p2⁻¹)
    calc
      (m₁ : Rat) * pow2 e₁ * ((pow2 e₂)⁻¹ * (m₂ : Rat)⁻¹)
          = (m₁ : Rat) * (pow2 e₁ * (pow2 e₂)⁻¹) * (m₂ : Rat)⁻¹ := by
            simp [Rat.mul_assoc]
      _ = (m₁ : Rat) * (m₂ : Rat)⁻¹ * (pow2 e₁ * (pow2 e₂)⁻¹) := by
            rw [Rat.mul_assoc, Rat.mul_comm (pow2 e₁ * (pow2 e₂)⁻¹),
              Rat.mul_assoc]
  rw [this, pow2_sub]

theorem signedVal_div (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) (h₂ : 0 < m₂) :
    signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂ =
      signedOf (s₁ / s₂) (mag m₁ e₁ / mag m₂ e₂) := by
  rw [signedVal_signedOf, signedVal_signedOf]
  exact signedOf_div s₁ s₂ _ _

/-! ### `divCore` residual: the exact quotient is in `[q * 2^te, (q+1) * 2^te]` -/

theorem divCore_te_le (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ e₁ - e₂ := by
  simp only [divCore]
  exact Int.min_le_left _ _

theorem accuracyOfFraction_exact_iff (num den : Nat) :
    accuracyOfFraction num den = .exact ↔ num = 0 := by
  unfold accuracyOfFraction
  by_cases h : num = 0 <;> simp [h]

theorem divCore_acc_exact_iff (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    (divCore spec64 m₁ e₁ m₂ e₂).2.2 = .exact ↔
      let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
      let k := (e₁ - e₂ - te).toNat
      (m₁ <<< k) % m₂ = 0 := by
  simp only [divCore]
  exact accuracyOfFraction_exact_iff _ _

theorem natCast_div_add_mod (n d : Nat) (hd : 0 < d) :
    (n : Rat) / (d : Rat) = (n / d : Nat) + ((n % d : Nat) : Rat) / (d : Rat) := by
  have hde : (d : Rat) ≠ 0 := rat_nat_ne_zero hd
  have hsplit : n = (n / d) * d + n % d := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n d).symm
  conv => lhs; rw [hsplit]
  rw [Rat.natCast_add, Rat.natCast_mul, add_div]
  have : ((n / d : Nat) : Rat) * (d : Rat) / (d : Rat) = ((n / d : Nat) : Rat) :=
    Rat.mul_div_cancel (a := ((n / d : Nat) : Rat)) (b := (d : Rat)) hde
  rw [this]

theorem mag_div_core (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    let q := (divCore spec64 m₁ e₁ m₂ e₂).1
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    let k := (e₁ - e₂ - te).toNat
    let rem := (m₁ <<< k) % m₂
    mag m₁ e₁ / mag m₂ e₂ =
      mag q te + ((rem : Rat) / (m₂ : Rat)) * pow2 te := by
  intro q te k rem
  have hte_le : te ≤ e₁ - e₂ := divCore_te_le m₁ e₁ m₂ e₂
  have hk' : (k : Int) = e₁ - e₂ - te := by
    exact Int.toNat_of_nonneg (Int.sub_nonneg_of_le hte_le)
  have hq : q = (m₁ <<< k) / m₂ := rfl
  have hdiv := mag_div m₁ e₁ m₂ e₂ h₂
  have hshift : (m₁ : Rat) * pow2 (k : Int) = ((m₁ <<< k : Nat) : Rat) := by
    rw [Nat.shiftLeft_eq, Rat.natCast_mul, Rat.natCast_pow]
    have h2 : ((2 : Nat) : Rat) = (2 : Rat) := rfl
    rw [h2, ← pow2_nat]
  have : (m₁ : Rat) / (m₂ : Rat) * pow2 (e₁ - e₂) =
      ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te := by
    have h2k : pow2 (e₁ - e₂) = pow2 te * pow2 (k : Int) := by
      have : te + (k : Int) = e₁ - e₂ := by omega
      rw [← pow2_add, this]
    have hswap : (m₁ : Rat) / (m₂ : Rat) * pow2 (k : Int) =
        ((m₁ : Rat) * pow2 (k : Int)) / (m₂ : Rat) := by
      rw [Rat.div_def, Rat.div_def]
      rw [Rat.mul_assoc, Rat.mul_comm (m₂ : Rat)⁻¹, Rat.mul_assoc]
    calc
      (m₁ : Rat) / (m₂ : Rat) * pow2 (e₁ - e₂)
          = (m₁ : Rat) / (m₂ : Rat) * (pow2 te * pow2 (k : Int)) := by rw [h2k]
      _ = (m₁ : Rat) / (m₂ : Rat) * pow2 (k : Int) * pow2 te := by
            rw [Rat.mul_assoc, Rat.mul_comm (pow2 te), ← Rat.mul_assoc]
      _ = ((m₁ : Rat) * pow2 (k : Int)) / (m₂ : Rat) * pow2 te := by rw [hswap]
      _ = ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te := by rw [hshift]
  rw [hdiv, this, natCast_div_add_mod _ _ h₂, hq]
  rw [Rat.add_mul, mag]

theorem rem_div_pos {rem m₂ : Nat} (hne : rem ≠ 0) (h₂ : 0 < m₂) :
    (0 : Rat) < (rem : Rat) / (m₂ : Rat) := by
  rw [Rat.div_def]
  exact Rat.mul_pos (rat_nat_pos (Nat.pos_of_ne_zero hne)) (Rat.inv_pos.mpr (rat_nat_pos h₂))

theorem rem_div_lt_one {rem m₂ : Nat} (hrem : rem < m₂) (h₂ : 0 < m₂) :
    (rem : Rat) / (m₂ : Rat) < 1 := by
  rw [Rat.div_lt_iff (rat_nat_pos h₂)]
  simpa [Rat.one_mul] using (Rat.natCast_lt_natCast.mpr hrem)

theorem mag_div_bracket (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    let q := (divCore spec64 m₁ e₁ m₂ e₂).1
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    let acc := (divCore spec64 m₁ e₁ m₂ e₂).2.2
    (acc = .exact → mag m₁ e₁ / mag m₂ e₂ = mag q te) ∧
      (∀ o, acc = .inexact o → inexactMag q te (mag m₁ e₁ / mag m₂ e₂)) := by
  intro q te acc
  let k := (e₁ - e₂ - te).toNat
  let rem := (m₁ <<< k) % m₂
  have hcore : mag m₁ e₁ / mag m₂ e₂ =
      mag q te + ((rem : Rat) / (m₂ : Rat)) * pow2 te := by
    simpa [q, te, k, rem] using mag_div_core m₁ e₁ m₂ e₂ h₂
  have hacc_iff : acc = .exact ↔ rem = 0 := by
    simpa [acc, rem, k, te] using divCore_acc_exact_iff m₁ e₁ m₂ e₂
  constructor
  · intro hex
    have hz : rem = 0 := hacc_iff.mp hex
    have hz' : ((rem : Rat) / (m₂ : Rat)) * pow2 te = 0 := by
      simp [hz, Rat.div_def, Rat.zero_mul]
    rw [hcore, hz', Rat.add_zero]
  · intro o ho
    have hne : rem ≠ 0 := by
      intro hz
      have : acc = .exact := hacc_iff.mpr hz
      rw [this] at ho
      cases ho
    have hrem_lt : rem < m₂ := Nat.mod_lt _ h₂
    have hpos := rem_div_pos hne h₂
    have hlt1 := rem_div_lt_one hrem_lt h₂
    have hterm_pos : (0 : Rat) < ((rem : Rat) / (m₂ : Rat)) * pow2 te :=
      Rat.mul_pos hpos (pow2_pos te)
    have hlo : mag q te < mag m₁ e₁ / mag m₂ e₂ := by
      rw [hcore]
      exact lt_add_of_pos_right _ _ hterm_pos
    have hhi : mag m₁ e₁ / mag m₂ e₂ < mag (q + 1) te := by
      rw [hcore, mag_add, mag_one]
      have : ((rem : Rat) / (m₂ : Rat)) * pow2 te < pow2 te := by
        have h := Rat.mul_lt_mul_of_pos_right hlt1 (pow2_pos te)
        simpa [Rat.one_mul] using h
      exact (Rat.add_lt_add_left (c := mag q te)).mpr this
    exact ⟨hlo, hhi⟩

theorem log2_ge_of_pow_le {m p : Nat} (h : 2 ^ p ≤ m) : p ≤ m.log2 :=
  (Nat.le_log2 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos p) h))).mpr h

theorem shiftRight_ge_pow {m k : Nat} (hne : m ≠ 0) (hk : k ≤ m.log2) :
    2 ^ (m.log2 - k) ≤ m >>> k := by
  have hpow : 2 ^ m.log2 ≤ m := Nat.log2_self_le hne
  have hdiv : 2 ^ m.log2 / 2 ^ k ≤ m / 2 ^ k := Nat.div_le_div_right hpow
  have heq : 2 ^ m.log2 / 2 ^ k = 2 ^ (m.log2 - k) := Nat.pow_div hk (by decide : 0 < 2)
  rw [Nat.shiftRight_eq_div_pow, ← heq]
  exact hdiv

theorem nat_eq_of_int_sub {k n a : Nat}
    (h : (k : Int) = (n : Int) - (a : Int)) (hle : a ≤ n) : k = n - a := by
  have hc : ((n - a : Nat) : Int) = (n : Int) - (a : Int) := Int.ofNat_sub hle
  exact Int.ofNat_inj.mp (h.trans hc.symm)

theorem canonical_mantissa_lt {m : Nat} {e : Int} (h : IsCanonicalFinite m e) :
    m < 2 ^ 53 := by
  cases h with
  | inl hs => exact Nat.lt_trans hs.2.2 (by decide)
  | inr hn => exact hn.2.2.2

/-- After the first shift+round of an inexact residual whose input is
    already at-or-below `minExponent` or already has at least 53 significand
    bits, the result is either a subnormal exponent or a normal-sized mantissa. -/
theorem firstRoundedAcc_norm_inexact (s : Sign) (m : Nat) (e : Int)
    (o : Ordering) (up : Bool)
    (h : e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m)
    (h0 : (firstRoundedAcc s m e (.inexact o) up).1 ≠ 0) :
    (firstRoundedAcc s m e (.inexact o) up).2 = spec64.minExponent ∨
      2 ^ 52 ≤ (firstRoundedAcc s m e (.inexact o) up).1 := by
  unfold firstRoundedAcc at h0 ⊢
  dsimp at h0 ⊢
  let k := (spec64.targetExponent (totalExponent m e) - e).toNat
  have hmnt :
      (shiftToTargetExponent spec64 m e (.inexact o)).1.mantissa = m >>> k := by
    rw [shiftToTargetExponent_em, shiftRight_of_acc_mantissa]
  have hexp :
      (shiftToTargetExponent spec64 m e (.inexact o)).2 =
        e + (spec64.targetExponent (totalExponent m e) - e).toNat :=
    shiftToTargetExponent_exp _ _ _ _
  have hround_ge : m >>> k ≤
      roundMantissaDirected
        (shiftToTargetExponent spec64 m e (.inexact o)).1.mantissa
        up s
        (shiftToTargetExponent spec64 m e (.inexact o)).1.accuracy := by
    rw [hmnt]
    exact roundMantissa_ge s up (m >>> k) _
  have htar := spec64.targetExponent (totalExponent m e)
  cases h with
  | inl hle =>
    have htar_ge : e ≤ spec64.targetExponent (totalExponent m e) :=
      Int.le_trans hle (targetExponent_ge_min _)
    have hexp' : (shiftToTargetExponent spec64 m e (.inexact o)).2 =
        spec64.targetExponent (totalExponent m e) := by
      rw [hexp, Int.toNat_of_nonneg (Int.sub_nonneg_of_le htar_ge)]
      omega
    by_cases hmin : spec64.targetExponent (totalExponent m e) = spec64.minExponent
    · exact Or.inl (by rw [hexp', hmin])
    · have hgt : spec64.minExponent < spec64.targetExponent (totalExponent m e) :=
        (Int.lt_iff_le_and_ne).mpr ⟨targetExponent_ge_min _, Ne.symm hmin⟩
      have htar_eq :
          spec64.targetExponent (totalExponent m e) =
            totalExponent m e - spec64.mantissaBits :=
        target_eq_te_sub hgt
      have hk_int : (k : Int) = (m.log2 + 1 : Nat) - (53 : Nat) := by
        have hk : (k : Int) = spec64.targetExponent (totalExponent m e) - e :=
          Int.toNat_of_nonneg (Int.sub_nonneg_of_le htar_ge)
        rw [hk, htar_eq]
        unfold totalExponent
        simp [mantissaBits_spec64]
        omega
      have hlog : 53 ≤ m.log2 + 1 := by
        have : 0 ≤ ((m.log2 + 1 : Nat) : Int) - 53 := by
          have : (k : Int) ≥ 0 := Int.natCast_nonneg _
          omega
        exact Int.ofNat_le.mp (by omega)
      have hlog' : 52 ≤ m.log2 := Nat.le_of_succ_le_succ (by
        have : 53 ≤ m.log2 + 1 := hlog
        omega)
      have hne : m ≠ 0 := by
        intro hz
        have : m.log2 = 0 := by rw [hz]; rfl
        rw [this] at hlog'
        exact Nat.not_le_of_gt (by decide : (0 : Nat) < 52) hlog'
      have hk_eq : k = m.log2 + 1 - 53 :=
        nat_eq_of_int_sub hk_int (by omega)
      have hk_le : k ≤ m.log2 := by rw [hk_eq]; omega
      have hge : 2 ^ 52 ≤ m >>> k := by
        have := shiftRight_ge_pow hne hk_le
        have hpow : 2 ^ (m.log2 - k) = 2 ^ 52 := by
          rw [hk_eq]
          have : m.log2 - (m.log2 + 1 - 53) = 52 := by omega
          rw [this]
        rwa [hpow] at this
      exact Or.inr (Nat.le_trans hge hround_ge)
  | inr hmge =>
    have hne : m ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2 ^ 52) hmge)
    by_cases hshift : spec64.targetExponent (totalExponent m e) ≤ e
    · have hk0 : k = 0 := (Int.toNat_sub_eq_zero_iff _ _).mpr hshift
      have hm0 : m >>> k = m := by rw [hk0, Nat.shiftRight_zero]
      exact Or.inr (Nat.le_trans hmge (by
        have := hround_ge
        rwa [hm0] at this))
    · have htar_gt : e < spec64.targetExponent (totalExponent m e) :=
        Int.lt_of_not_ge hshift
      have hexp' : (shiftToTargetExponent spec64 m e (.inexact o)).2 =
          spec64.targetExponent (totalExponent m e) := by
        rw [hexp, Int.toNat_of_nonneg (Int.sub_nonneg_of_le (Int.le_of_lt htar_gt))]
        omega
      by_cases hmin : spec64.targetExponent (totalExponent m e) = spec64.minExponent
      · exact Or.inl (by rw [hexp', hmin])
      · have hgt : spec64.minExponent < spec64.targetExponent (totalExponent m e) :=
          (Int.lt_iff_le_and_ne).mpr ⟨targetExponent_ge_min _, Ne.symm hmin⟩
        have htar_eq :
            spec64.targetExponent (totalExponent m e) =
              totalExponent m e - spec64.mantissaBits :=
          target_eq_te_sub hgt
        have htar_ge : e ≤ spec64.targetExponent (totalExponent m e) := Int.le_of_lt htar_gt
        have hk_int : (k : Int) = (m.log2 + 1 : Nat) - (53 : Nat) := by
          have hk : (k : Int) = spec64.targetExponent (totalExponent m e) - e :=
            Int.toNat_of_nonneg (Int.sub_nonneg_of_le htar_ge)
          rw [hk, htar_eq]
          unfold totalExponent
          simp [mantissaBits_spec64]
          omega
        have hlog : 52 ≤ m.log2 := log2_ge_of_pow_le hmge
        have hk_eq : k = m.log2 + 1 - 53 :=
          nat_eq_of_int_sub hk_int (by
            have : 53 ≤ m.log2 + 1 := Nat.succ_le_succ hlog
            exact this)
        have hk_le : k ≤ m.log2 := by rw [hk_eq]; omega
        have hge : 2 ^ 52 ≤ m >>> k := by
          have := shiftRight_ge_pow hne hk_le
          have hpow : 2 ^ (m.log2 - k) = 2 ^ 52 := by
            rw [hk_eq]
            have : m.log2 - (m.log2 + 1 - 53) = 52 := by
              have : 53 ≤ m.log2 + 1 := Nat.succ_le_succ hlog
              omega
            rw [this]
          rwa [hpow] at this
        exact Or.inr (Nat.le_trans hge hround_ge)

theorem firstRoundedAcc_norm_of_enough (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (up : Bool)
    (h : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m)
    (h0 : (firstRoundedAcc s m e acc up).1 ≠ 0) :
    (firstRoundedAcc s m e acc up).2 = spec64.minExponent ∨
      2 ^ 52 ≤ (firstRoundedAcc s m e acc up).1 := by
  cases hacc : acc with
  | exact =>
    rw [hacc] at h0
    have heq : firstRoundedAcc s m e .exact up = firstRounded s m e up :=
      firstRoundedAcc_exact s m e up
    rw [heq] at h0 ⊢
    have he : spec64.minExponent ≤ (firstRounded s m e up).2 :=
      firstRounded_snd_ge_min s m e up
    have hle : (firstRounded s m e up).1 ≤ 2 ^ 53 :=
      firstRounded_fst_le_pow53 s m e up
    cases Nat.lt_or_eq_of_le hle with
    | inl _hlt =>
      by_cases hmin : (firstRounded s m e up).2 = spec64.minExponent
      · exact Or.inl hmin
      · have hgt : spec64.minExponent < (firstRounded s m e up).2 :=
          (Int.lt_iff_le_and_ne).mpr ⟨he, Ne.symm hmin⟩
        have hm0 : m ≠ 0 := by
          intro hz
          apply h0
          rw [hz]
          exact firstRounded_of_zero s e up
        have htar : (firstRounded s m e up).2 =
            spec64.targetExponent (totalExponent m e) :=
          firstRounded_exponent hm0
        have hnorm := firstRounded_mantissa_normal (s := s) (up := up) hm0 (htar ▸ hgt)
        exact Or.inr hnorm.1
    | inr heq53 =>
      exact Or.inr (heq53 ▸ by decide)
  | inexact o =>
    rw [hacc] at h0
    have hin : e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m := by
      cases h with
      | inl hex =>
        rw [hacc] at hex
        cases hex
      | inr h' => exact h'
    exact firstRoundedAcc_norm_inexact s m e o up hin h0



end Interval64Proofs.Div
