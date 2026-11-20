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




/-! ### `divCore` returns enough mantissa bits for packing -/

theorem log2_le_52_of_lt_pow53 {m : Nat} (h0 : 0 < m) (h : m < 2 ^ 53) :
    m.log2 ≤ 52 :=
  Nat.le_of_lt_succ ((Nat.log2_lt (Nat.ne_of_gt h0)).mpr h)

theorem totalExponent_sub_formula (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    totalExponent m₁ e₁ - totalExponent m₂ e₂ =
      (m₁.log2 : Int) - (m₂.log2 : Int) + e₁ - e₂ := by
  unfold totalExponent
  omega

theorem divCore_unbiased_le {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) :
    totalExponent m₁ e₁ - totalExponent m₂ e₂ - (53 : Int) ≤ e₁ - e₂ - 1 := by
  have hlog : (m₁.log2 : Int) ≤ 52 := Int.ofNat_le.mpr (log2_le_52_of_lt_pow53 h₁ hs)
  have hlog2 : 0 ≤ (m₂.log2 : Int) := Int.natCast_nonneg _
  rw [totalExponent_sub_formula]
  omega

theorem targetExponent_eq_or_min (te : Int) :
    spec64.targetExponent te = te - 53 ∨
      spec64.targetExponent te = spec64.minExponent := by
  unfold Format.targetExponent
  rw [mantissaBits_spec64]
  by_cases h : te - (53 : Int) ≤ spec64.minExponent
  · exact Or.inr (Int.max_eq_right h)
  · exact Or.inl (Int.max_eq_left (Int.le_of_not_le h))

theorem divCore_target_le {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) :
    spec64.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂) ≤
        e₁ - e₂ - 1 ∨
      spec64.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂) =
        spec64.minExponent := by
  have hunb := divCore_unbiased_le (m₁ := m₁) (m₂ := m₂) (e₁ := e₁) (e₂ := e₂) h₁ hs
  rcases targetExponent_eq_or_min (totalExponent m₁ e₁ - totalExponent m₂ e₂) with h | h
  · exact Or.inl (h ▸ hunb)
  · exact Or.inr h

theorem divCore_te_def (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    (divCore spec64 m₁ e₁ m₂ e₂).2.1 =
      min (e₁ - e₂)
        (spec64.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂)) :=
  rfl

/-- If the `divCore` target exponent is above `minExponent`, it equals
    the unbiased quotient exponent minus 53. -/
theorem divCore_te_eq_of_gt_min {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53)
    (hgt : spec64.minExponent < (divCore spec64 m₁ e₁ m₂ e₂).2.1) :
    (divCore spec64 m₁ e₁ m₂ e₂).2.1 =
      totalExponent m₁ e₁ - totalExponent m₂ e₂ - (53 : Int) := by
  have hdef := divCore_te_def m₁ e₁ m₂ e₂
  have hte : (divCore spec64 m₁ e₁ m₂ e₂).2.1 =
      spec64.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂) := by
    rcases divCore_target_le (m₁ := m₁) (m₂ := m₂) (e₁ := e₁) (e₂ := e₂) h₁ hs with hle | hmin
    · rw [hdef, Int.min_eq_right (Int.le_trans hle (by omega))]
    · have : (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ spec64.minExponent := by
        rw [hdef, hmin]
        exact Int.min_le_right _ _
      exact (Int.not_le.mpr hgt this).elim
  rw [hte]
  rcases targetExponent_eq_or_min (totalExponent m₁ e₁ - totalExponent m₂ e₂) with h | hmin
  · exact h
  · have : (divCore spec64 m₁ e₁ m₂ e₂).2.1 = spec64.minExponent := hte.trans hmin
    exact (Int.not_le.mpr hgt (Int.le_of_eq this)).elim

theorem divCore_k_eq_of_gt_min {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53)
    (hgt : spec64.minExponent < (divCore spec64 m₁ e₁ m₂ e₂).2.1) :
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    let k := (e₁ - e₂ - te).toNat
    k = 53 - m₁.log2 + m₂.log2 := by
  intro te k
  have hte := divCore_te_eq_of_gt_min h₁ hs hgt
  have hk : (k : Int) = e₁ - e₂ - te :=
    Int.toNat_of_nonneg (Int.sub_nonneg_of_le (divCore_te_le m₁ e₁ m₂ e₂))
  have hk_int : (k : Int) = (53 : Int) - (m₁.log2 : Int) + (m₂.log2 : Int) := by
    have hte' : te = totalExponent m₁ e₁ - totalExponent m₂ e₂ - (53 : Int) := hte
    rw [hk, hte', totalExponent_sub_formula]
    omega
  have hlog : m₁.log2 ≤ 53 :=
    Nat.le_trans (log2_le_52_of_lt_pow53 h₁ hs) (by decide)
  have hcast : ((53 - m₁.log2 + m₂.log2 : Nat) : Int) =
      (53 : Int) - (m₁.log2 : Int) + (m₂.log2 : Int) := by
    have hsub : ((53 - m₁.log2 : Nat) : Int) = (53 : Int) - (m₁.log2 : Int) :=
      Int.ofNat_sub hlog
    rw [Int.natCast_add, hsub]
  exact Int.ofNat_inj.mp (hk_int.trans hcast.symm)

theorem pow_mul_ge_of_log {m k : Nat} (hne : m ≠ 0) :
    2 ^ (m.log2 + k) ≤ m * 2 ^ k := by
  have := Nat.log2_self_le hne
  simpa [Nat.pow_add] using Nat.mul_le_mul_right (2 ^ k) this

theorem two_pow_succ_log (n : Nat) : n < 2 ^ (n.log2 + 1) :=
  Nat.lt_log2_self

theorem mul_pow52_le_of_log (m : Nat) :
    m * 2 ^ 52 ≤ 2 ^ (53 + m.log2) := by
  have hlt : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hle : m * 2 ^ 52 ≤ (2 ^ (m.log2 + 1) - 1) * 2 ^ 52 :=
    Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hlt)
  have h2 : (2 ^ (m.log2 + 1) - 1) * 2 ^ 52 + 2 ^ 52 =
      2 ^ (m.log2 + 1) * 2 ^ 52 := by
    have ha : 1 ≤ 2 ^ (m.log2 + 1) := Nat.succ_le_of_lt (Nat.two_pow_pos _)
    have : 2 ^ (m.log2 + 1) - 1 + 1 = 2 ^ (m.log2 + 1) := Nat.sub_add_cancel ha
    calc
      (2 ^ (m.log2 + 1) - 1) * 2 ^ 52 + 2 ^ 52
          = (2 ^ (m.log2 + 1) - 1 + 1) * 2 ^ 52 := by
            rw [Nat.add_mul, Nat.one_mul]
      _ = 2 ^ (m.log2 + 1) * 2 ^ 52 := by rw [this]
  have hpow : 2 ^ (m.log2 + 1) * 2 ^ 52 = 2 ^ (m.log2 + 1 + 52) :=
    (Nat.pow_add 2 _ _).symm
  have hsum : m.log2 + 1 + 52 = 53 + m.log2 := by omega
  have hplus : (2 ^ (m.log2 + 1) - 1) * 2 ^ 52 + 2 ^ 52 = 2 ^ (53 + m.log2) := by
    rw [h2, hpow, hsum]
  have : (2 ^ (m.log2 + 1) - 1) * 2 ^ 52 ≤ 2 ^ (53 + m.log2) := by
    have := Nat.le_add_right ((2 ^ (m.log2 + 1) - 1) * 2 ^ 52) (2 ^ 52)
    rwa [hplus] at this
  exact Nat.le_trans hle this

theorem divCore_q_ge_pow52_of_gt_min {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂)
    (hgt : spec64.minExponent < (divCore spec64 m₁ e₁ m₂ e₂).2.1) :
    2 ^ 52 ≤ (divCore spec64 m₁ e₁ m₂ e₂).1 := by
  let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
  let k := (e₁ - e₂ - te).toNat
  let q := (divCore spec64 m₁ e₁ m₂ e₂).1
  have hk_eq : k = 53 - m₁.log2 + m₂.log2 :=
    divCore_k_eq_of_gt_min h₁ hs hgt
  have hq : q = (m₁ <<< k) / m₂ := rfl
  have hne1 : m₁ ≠ 0 := Nat.ne_of_gt h₁
  have hlog : m₁.log2 ≤ 53 :=
    Nat.le_trans (log2_le_52_of_lt_pow53 h₁ hs) (by decide)
  have hnum : 2 ^ (53 + m₂.log2) ≤ m₁ <<< k := by
    rw [Nat.shiftLeft_eq]
    have : 2 ^ (m₁.log2 + k) ≤ m₁ * 2 ^ k := pow_mul_ge_of_log hne1
    have hsum : m₁.log2 + k = 53 + m₂.log2 := by
      rw [hk_eq, ← Nat.add_assoc, Nat.add_sub_of_le hlog]
    rwa [hsum] at this
  have hle52 : 2 ^ 52 ≤ 2 ^ (53 + m₂.log2) / m₂ :=
    (Nat.le_div_iff_mul_le h₂).mpr (by
      rw [Nat.mul_comm]
      exact mul_pow52_le_of_log m₂)
  have : 2 ^ 52 ≤ (m₁ <<< k) / m₂ :=
    Nat.le_trans hle52 (Nat.div_le_div_right hnum)
  simpa [q, hq] using this

/-- For a binary64-sized numerator, `divCore` either underflows to
    `minExponent` (or below) or returns a mantissa of at least 53 bits. -/
theorem divCore_enough_bits {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂) :
    (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ spec64.minExponent ∨
      2 ^ 52 ≤ (divCore spec64 m₁ e₁ m₂ e₂).1 := by
  by_cases hte : (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ spec64.minExponent
  · exact Or.inl hte
  · exact Or.inr (divCore_q_ge_pow52_of_gt_min h₁ hs h₂ (Int.lt_of_not_ge hte))


/-! ### Unpacked finite division encloses the exact quotient -/

theorem mag_div_nonneg (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    (0 : Rat) ≤ mag m₁ e₁ / mag m₂ e₂ := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg (mag_nonneg m₁ e₁)
    (Rat.le_of_lt (Rat.inv_pos.mpr (mag_pos h₂)))

theorem signedMag_signedOf (s : Sign) {r : Rat} (h : 0 ≤ r) :
    signedMag s (signedOf s r) = r := by
  cases s <;> simp [signedMag, signedOf, Rat.neg_neg]

theorem divU_finite_lo {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    loEncloses? (toEVal (divU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) false))
      (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) := by
  simp only [divU]
  have hbr := mag_div_bracket m₁ e₁ m₂ e₂ h₂
  have hv : signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂ =
      signedOf (s₁ / s₂) (mag m₁ e₁ / mag m₂ e₂) :=
    signedVal_div s₁ s₂ m₁ m₂ e₁ e₂ h₂
  refine roundDirected_lo_acc (s₁ / s₂)
    (divCore spec64 m₁ e₁ m₂ e₂).1
    (divCore spec64 m₁ e₁ m₂ e₂).2.1
    (divCore spec64 m₁ e₁ m₂ e₂).2.2
    (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) ?hex ?hin
  · intro hex
    have : mag m₁ e₁ / mag m₂ e₂ =
        mag (divCore spec64 m₁ e₁ m₂ e₂).1 (divCore spec64 m₁ e₁ m₂ e₂).2.1 :=
      hbr.1 hex
    rw [hv, this, signedVal_signedOf]
  · intro o ho
    have hinex := hbr.2 o ho
    have hsm :
        signedMag (s₁ / s₂)
          (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) =
          mag m₁ e₁ / mag m₂ e₂ := by
      rw [hv, signedMag_signedOf (s := s₁ / s₂) (mag_div_nonneg m₁ e₁ m₂ e₂ h₂)]
    simpa [hsm] using hinex

theorem divU_finite_hi {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    hiEncloses? (toEVal (divU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) true))
      (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) := by
  simp only [divU]
  have hbr := mag_div_bracket m₁ e₁ m₂ e₂ h₂
  have hv : signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂ =
      signedOf (s₁ / s₂) (mag m₁ e₁ / mag m₂ e₂) :=
    signedVal_div s₁ s₂ m₁ m₂ e₁ e₂ h₂
  refine roundDirected_hi_acc (s₁ / s₂)
    (divCore spec64 m₁ e₁ m₂ e₂).1
    (divCore spec64 m₁ e₁ m₂ e₂).2.1
    (divCore spec64 m₁ e₁ m₂ e₂).2.2
    (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) ?hex ?hin
  · intro hex
    have : mag m₁ e₁ / mag m₂ e₂ =
        mag (divCore spec64 m₁ e₁ m₂ e₂).1 (divCore spec64 m₁ e₁ m₂ e₂).2.1 :=
      hbr.1 hex
    rw [hv, this, signedVal_signedOf]
  · intro o ho
    have hinex := hbr.2 o ho
    have hsm :
        signedMag (s₁ / s₂)
          (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂) =
          mag m₁ e₁ / mag m₂ e₂ := by
      rw [hv, signedMag_signedOf (s := s₁ / s₂) (mag_div_nonneg m₁ e₁ m₂ e₂ h₂)]
    simpa [hsm] using hinex

theorem divU_finite_eq_round (s₁ s₂ : Sign) {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (up : Bool) :
    divU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) up =
      let (m, e, acc) := divCore spec64 m₁ e₁ m₂ e₂
      roundDirected (s₁ / s₂) m e acc up :=
  rfl

theorem divU_shaped_or_zero {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (hs₁ : m₁ < 2 ^ 53) (up : Bool) :
    (∃ z, divU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) up = .zero z) ∨
      (∃ m' e' h, divU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) up =
          .finite (s₁ / s₂) m' e' h ∧
          (IsSubnormal m' e' ∨ IsNormal m' e' ∨ IsOverflowNormal m' e')) := by
  rw [divU_finite_eq_round]
  refine roundDirected_zero_or_shaped_acc (s₁ / s₂)
    (divCore spec64 m₁ e₁ m₂ e₂).1
    (divCore spec64 m₁ e₁ m₂ e₂).2.1
    (divCore spec64 m₁ e₁ m₂ e₂).2.2 up ?_
  intro h0
  exact firstRoundedAcc_norm_of_enough (s₁ / s₂)
    (divCore spec64 m₁ e₁ m₂ e₂).1
    (divCore spec64 m₁ e₁ m₂ e₂).2.1
    (divCore spec64 m₁ e₁ m₂ e₂).2.2 up
    (Or.inr (divCore_enough_bits h₁ hs₁ h₂)) h0

/-! ### Bits-level enclosure of directed div -/

theorem div_encloses_lo {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hqb : qb ≠ 0) :
    loEncloses? (bitsToEVal (divDown a b)) (qa / qb) := by
  simp only [divDown, Interval64.Spec.div]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      exact (hqb rfl).elim
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      simp only [divU]
      exact loEncloses_packDirected_zero_val _ _ _
        (by
        have : (0 : Rat) / signedVal s2 m2 e2 = 0 := by
          rw [Rat.div_def, Rat.zero_mul]
        simp [loEncloses?, loEncloses, this])
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      exact (hqb rfl).elim
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2]
      have hlo := divU_finite_lo (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape :=
        divU_shaped_or_zero (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
          (canonical_mantissa_lt hc1) false
      rcases hshape with ⟨z, heq⟩ | ⟨m, e, h, heq, hsh⟩
      · rw [heq]
        exact loEncloses_packDirected_zero_val _ _ _ (heq ▸ hlo)
      · rw [heq]
        exact loEncloses_packDirected_of_shaped (s1 / s2) h hsh _ (heq ▸ hlo)

theorem div_encloses_hi {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hqb : qb ≠ 0) :
    hiEncloses? (bitsToEVal (divUp a b)) (qa / qb) := by
  simp only [divUp, Interval64.Spec.div]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      exact (hqb rfl).elim
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      simp only [divU]
      exact hiEncloses_packDirected_zero_val _ _ _
        (by
        have : (0 : Rat) / signedVal s2 m2 e2 = 0 := by
          rw [Rat.div_def, Rat.zero_mul]
        simp [hiEncloses?, hiEncloses, this])
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      exact (hqb rfl).elim
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2]
      have hhi := divU_finite_hi (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape :=
        divU_shaped_or_zero (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
          (canonical_mantissa_lt hc1) true
      rcases hshape with ⟨z, heq⟩ | ⟨m, e, h, heq, hsh⟩
      · rw [heq]
        exact hiEncloses_packDirected_zero_val _ _ _ (heq ▸ hhi)
      · rw [heq]
        exact hiEncloses_packDirected_of_shaped (s1 / s2) h hsh _ (heq ▸ hhi)

theorem div_encloses {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hqb : qb ≠ 0) :
    loEncloses? (bitsToEVal (divDown a b)) (qa / qb) ∧
    hiEncloses? (bitsToEVal (divUp a b)) (qa / qb) :=
  ⟨div_encloses_lo ha hb hqb, div_encloses_hi ha hb hqb⟩


/-! ### Exactness when the quotient is a representable binary64 value -/

theorem one_le_two_pow (n : Nat) : (1 : Rat) ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih =>
    rw [Rat.pow_succ]
    have h0 : (0 : Rat) ≤ (2 : Rat) ^ n :=
      Rat.le_trans (by decide : (0 : Rat) ≤ 1) ih
    have hmul : (2 : Rat) ^ n * 1 ≤ (2 : Rat) ^ n * 2 :=
      Rat.mul_le_mul_of_nonneg_left (by decide : (1 : Rat) ≤ 2) h0
    have : (2 : Rat) ^ n ≤ (2 : Rat) ^ n * 2 := by simpa [Rat.mul_one] using hmul
    exact Rat.le_trans ih this

theorem one_le_pow2_of_nonneg {e : Int} (h : 0 ≤ e) : (1 : Rat) ≤ pow2 e := by
  have he : (e.toNat : Int) = e := Int.toNat_of_nonneg h
  rw [pow2_eq_zpow, ← he, Rat.zpow_natCast]
  exact one_le_two_pow _

theorem pow2_le_pow2 {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  have hab : a + (b - a) = b := by omega
  have hmul : pow2 b = pow2 a * pow2 (b - a) := by
    rw [← pow2_add, hab]
  have h1 : (1 : Rat) ≤ pow2 (b - a) :=
    one_le_pow2_of_nonneg (Int.sub_nonneg_of_le h)
  have : pow2 a * 1 ≤ pow2 a * pow2 (b - a) :=
    Rat.mul_le_mul_of_nonneg_left h1 (pow2_nonneg a)
  simpa [Rat.mul_one, hmul] using this

theorem mag_le_of_exp_le {m : Nat} {e₁ e₂ : Int} (h : e₁ ≤ e₂) :
    mag m e₁ ≤ mag m e₂ :=
  Rat.mul_le_mul_of_nonneg_left (pow2_le_pow2 h)
    (Rat.natCast_le_natCast.mpr (Nat.zero_le m))

theorem rat_lt_of_le_of_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  have hle : a ≤ c := Rat.le_trans h₁ (Rat.le_of_lt h₂)
  have hne : a ≠ c := by
    intro he
    exact (Rat.lt_iff_le_and_not_ge.mp h₂).2 (he ▸ h₁)
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_trans {a b c : Rat} (h₁ : a < b) (h₂ : b < c) : a < c :=
  rat_lt_of_le_of_lt (Rat.le_of_lt h₁) h₂

theorem mag_lt_of_exp_lt {m : Nat} {e₁ e₂ : Int} (hm : 0 < m) (h : e₁ < e₂) :
    mag m e₁ < mag m e₂ := by
  have hle : mag m e₁ ≤ mag m (e₂ - 1) := mag_le_of_exp_le (Int.le_sub_one_of_lt h)
  have hsucc : mag m ((e₂ - 1) + 1) = mag m (e₂ - 1) * 2 := by
    unfold mag
    rw [pow2_succ, Rat.mul_assoc]
  have heq : e₂ = (e₂ - 1) + 1 := by omega
  have hlt : mag m (e₂ - 1) < mag m e₂ := by
    rw [heq, hsucc]
    have : mag m (e₂ - 1) * 1 < mag m (e₂ - 1) * 2 :=
      Rat.mul_lt_mul_of_pos_left (by decide : (1 : Rat) < 2) (mag_pos hm)
    simpa [Rat.mul_one] using this
  exact rat_lt_of_le_of_lt hle hlt

theorem rat_div_eq_zero {a b : Rat} (hb : b ≠ 0) : a / b = 0 ↔ a = 0 := by
  rw [Rat.div_def, Rat.mul_eq_zero]
  constructor
  · intro h
    cases h with
    | inl ha => exact ha
    | inr hi =>
      have : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hb
      rw [hi, Rat.mul_zero] at this
      exact ((by decide : (1 : Rat) ≠ 0) this.symm).elim
  · intro ha
    exact Or.inl ha

theorem rem_term_nonneg (rem m₂ : Nat) (te : Int) (h₂ : 0 < m₂) :
    (0 : Rat) ≤ ((rem : Rat) / (m₂ : Rat)) * pow2 te :=
  Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.natCast_le_natCast.mpr (Nat.zero_le rem))
      (Rat.le_of_lt (Rat.inv_pos.mpr (rat_nat_pos h₂))))
    (pow2_nonneg te)

theorem mag_div_ge_q {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₂ : 0 < m₂) :
    let q := (divCore spec64 m₁ e₁ m₂ e₂).1
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    mag q te ≤ mag m₁ e₁ / mag m₂ e₂ := by
  intro q te
  have hcore := mag_div_core m₁ e₁ m₂ e₂ h₂
  let k := (e₁ - e₂ - te).toNat
  let rem := (m₁ <<< k) % m₂
  have : mag m₁ e₁ / mag m₂ e₂ =
      mag q te + ((rem : Rat) / (m₂ : Rat)) * pow2 te := by
    simpa [q, te, k, rem] using hcore
  rw [this]
  exact le_add_of_nonneg_right (rem_term_nonneg rem m₂ te h₂)

theorem mag_pow53_eq (e : Int) :
    mag (2 ^ 53) e = mag (2 ^ 52) (e + 1) := by
  have h : (2 ^ 53 : Nat) = 2 ^ 52 * 2 ^ 1 := by decide
  rw [h, mag_mul_two_pow_add]
  rfl

/-- A representable nonzero quotient cannot be subnormal if `divCore`
    produced a normal-sized mantissa above `minExponent`. -/
theorem div_rep_not_subnormal {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {m' : Nat} {e' : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂)
    (hgt : spec64.minExponent < (divCore spec64 m₁ e₁ m₂ e₂).2.1)
    (hv : mag m₁ e₁ / mag m₂ e₂ = mag m' e')
    (hsub : IsSubnormal m' e') : False := by
  have hq := divCore_q_ge_pow52_of_gt_min h₁ hs h₂ hgt
  let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
  have hge : mag (2 ^ 52) te ≤ mag m₁ e₁ / mag m₂ e₂ :=
    Rat.le_trans (mag_le_mag hq) (mag_div_ge_q h₂)
  have heq : e' = spec64.minExponent := hsub.1
  have hm' : m' < 2 ^ 52 := hsub.2.2
  have hlt : mag m' e' < mag (2 ^ 52) te :=
    rat_lt_trans (mag_lt_mag hm')
      (mag_lt_of_exp_lt (by decide : 0 < 2 ^ 52) (heq ▸ hgt))
  have hge' : mag (2 ^ 52) te ≤ mag m' e' := by rwa [hv] at hge
  exact (Rat.lt_iff_le_and_not_ge.mp hlt).2 hge'

theorem div_rep_te_le_exp {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {m' : Nat} {e' : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m₁ e₁ / mag m₂ e₂ = mag m' e') :
    (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ e' := by
  by_cases hte : (divCore spec64 m₁ e₁ m₂ e₂).2.1 ≤ spec64.minExponent
  · have hmin : spec64.minExponent ≤ e' := by
      cases hc with
      | inl hs => exact Int.le_of_eq hs.1.symm
      | inr hn => exact hn.1
    exact Int.le_trans hte hmin
  · have hgt : spec64.minExponent < (divCore spec64 m₁ e₁ m₂ e₂).2.1 :=
      Int.lt_of_not_ge hte
    have hnorm : IsNormal m' e' := by
      cases hc with
      | inl hsub => exact (div_rep_not_subnormal h₁ hs h₂ hgt hv hsub).elim
      | inr hn => exact hn
    have hq := divCore_q_ge_pow52_of_gt_min h₁ hs h₂ hgt
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    have hge : mag (2 ^ 52) te ≤ mag m' e' := by
      have := Rat.le_trans (mag_le_mag hq) (mag_div_ge_q h₂)
      rwa [hv] at this
    have hhi : mag m' e' < mag (2 ^ 52) (e' + 1) := by
      have : mag m' e' < mag (2 ^ 53) e' := mag_lt_mag hnorm.2.2.2
      rwa [mag_pow53_eq] at this
    have hlt : mag (2 ^ 52) te < mag (2 ^ 52) (e' + 1) :=
      rat_lt_of_le_of_lt hge hhi
    have hnot : ¬ e' + 1 ≤ te := fun hle =>
      (Rat.lt_iff_le_and_not_ge.mp hlt).2 (mag_le_of_exp_le hle)
    exact Int.lt_add_one_iff.mp (Int.lt_of_not_ge hnot)

theorem pow2_toNat_of_nonneg {e : Int} (h : 0 ≤ e) :
    pow2 e = ((2 ^ e.toNat : Nat) : Rat) := by
  have he : pow2 e = pow2 (e.toNat : Int) := by
    rw [Int.toNat_of_nonneg h]
  have h2 : ((2 : Nat) : Rat) = (2 : Rat) := rfl
  rw [he, pow2_nat, Rat.natCast_pow, h2]

theorem divCore_rem_eq_zero_of_rep {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {m' : Nat} {e' : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m₁ e₁ / mag m₂ e₂ = mag m' e') :
    let te := (divCore spec64 m₁ e₁ m₂ e₂).2.1
    let k := (e₁ - e₂ - te).toNat
    (m₁ <<< k) % m₂ = 0 := by
  intro te k
  have hte_le : te ≤ e' := div_rep_te_le_exp h₁ hs h₂ h' hc hv
  have hcore := mag_div_core m₁ e₁ m₂ e₂ h₂
  have hquot : mag m₁ e₁ / mag m₂ e₂ =
      ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te := by
    have hd := natCast_div_add_mod (m₁ <<< k) m₂ h₂
    have hsplit :
        mag ((m₁ <<< k) / m₂) te +
          ((((m₁ <<< k) % m₂ : Nat) : Rat) / (m₂ : Rat)) * pow2 te =
          ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te := by
      rw [hd, Rat.add_mul, mag]
    have hcore' : mag m₁ e₁ / mag m₂ e₂ =
        mag ((m₁ <<< k) / m₂) te +
          ((((m₁ <<< k) % m₂ : Nat) : Rat) / (m₂ : Rat)) * pow2 te := by
      simpa [te, k, show (divCore spec64 m₁ e₁ m₂ e₂).1 = (m₁ <<< k) / m₂ from rfl]
        using hcore
    rw [hcore', hsplit]
  have hde : (m₂ : Rat) ≠ 0 := rat_nat_ne_zero h₂
  have hP : pow2 te ≠ 0 := pow2_ne_zero te
  -- (A / B) * P = C * Q
  have heq : ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te =
      (m' : Rat) * pow2 e' := by
    simpa [mag] using hquot.symm.trans hv
  have hre : ((m₁ <<< k : Nat) : Rat) * pow2 te / (m₂ : Rat) =
      (m' : Rat) * pow2 e' := by
    have : ((m₁ <<< k : Nat) : Rat) / (m₂ : Rat) * pow2 te =
        ((m₁ <<< k : Nat) : Rat) * pow2 te / (m₂ : Rat) := by
      rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm (m₂ : Rat)⁻¹,
        Rat.mul_assoc]
    rwa [← this]
  have hmul : ((m₁ <<< k : Nat) : Rat) * pow2 te =
      (m' : Rat) * pow2 e' * (m₂ : Rat) := by
    have := congrArg (fun z : Rat => z * (m₂ : Rat)) hre
    simpa [Rat.div_mul_cancel (a := ((m₁ <<< k : Nat) : Rat) * pow2 te) hde] using this
  have hpow : pow2 e' = pow2 te * pow2 (e' - te) := by
    rw [← pow2_add, show te + (e' - te) = e' by omega]
  have hmul' : ((m₁ <<< k : Nat) : Rat) * pow2 te =
      ((m' : Rat) * (m₂ : Rat) * pow2 (e' - te)) * pow2 te := by
    rw [hmul, hpow]
    simp [Rat.mul_assoc, Rat.mul_comm, mul_left_comm_rat]
  have hA : ((m₁ <<< k : Nat) : Rat) =
      (m' : Rat) * (m₂ : Rat) * pow2 (e' - te) := by
    have h1 : ((m₁ <<< k : Nat) : Rat) * pow2 te * (pow2 te)⁻¹ =
        ((m' : Rat) * (m₂ : Rat) * pow2 (e' - te)) * pow2 te * (pow2 te)⁻¹ := by
      rw [hmul']
    simpa [Rat.mul_assoc, Rat.mul_inv_cancel (pow2 te) hP, Rat.mul_one] using h1
  have hpow' : pow2 (e' - te) = ((2 ^ (e' - te).toNat : Nat) : Rat) :=
    pow2_toNat_of_nonneg (Int.sub_nonneg_of_le hte_le)
  have heqN : (m₁ <<< k : Nat) = m' * m₂ * 2 ^ (e' - te).toNat := by
    have : ((m₁ <<< k : Nat) : Rat) =
        ((m' * m₂ * 2 ^ (e' - te).toNat : Nat) : Rat) := by
      rw [hA, hpow', Rat.natCast_mul, Rat.natCast_mul]
    exact Rat.natCast_inj.mp this
  have : m₂ ∣ m₁ <<< k :=
    ⟨m' * 2 ^ (e' - te).toNat, by
      rw [heqN, Nat.mul_comm m' m₂, Nat.mul_assoc]⟩
  exact Nat.mod_eq_zero_of_dvd this

theorem mag_eq_of_signedOf {s s' : Sign} {r : Rat} {m : Nat} {e : Int}
    (hr : 0 ≤ r) (hm : 0 < m)
    (h : signedOf s r = signedVal s' m e) : r = mag m e := by
  cases s with
  | positive =>
    cases s' with
    | positive =>
      simp [signedOf, signedVal] at h
      exact h
    | negative =>
      simp [signedOf, signedVal] at h
      have hneg : -r = mag m e := by
        have := congrArg Neg.neg h
        simpa [Rat.neg_neg] using this
      have hpos : (0 : Rat) < -r := hneg.symm ▸ mag_pos hm
      have hlt : r < 0 := by
        have := Rat.neg_lt_neg hpos
        simpa [Rat.neg_neg, Rat.neg_zero] using this
      exact ((Rat.lt_iff_le_and_not_ge.mp hlt).2 hr).elim
  | negative =>
    cases s' with
    | negative =>
      simp [signedOf, signedVal] at h
      have := congrArg Neg.neg h
      simpa [Rat.neg_neg] using this
    | positive =>
      simp [signedOf, signedVal] at h
      have hpos : (0 : Rat) < -r := h.symm ▸ mag_pos hm
      have hlt : r < 0 := by
        have := Rat.neg_lt_neg hpos
        simpa [Rat.neg_neg, Rat.neg_zero] using this
      exact ((Rat.lt_iff_le_and_not_ge.mp hlt).2 hr).elim

theorem divCore_exact_of_rep {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {m' : Nat} {e' : Int}
    (h₁ : 0 < m₁) (hs : m₁ < 2 ^ 53) (h₂ : 0 < m₂) (h' : 0 < m')
    (hc : IsCanonicalFinite m' e')
    (hv : mag m₁ e₁ / mag m₂ e₂ = mag m' e') :
    (divCore spec64 m₁ e₁ m₂ e₂).2.2 = .exact ∧
      mag (divCore spec64 m₁ e₁ m₂ e₂).1 (divCore spec64 m₁ e₁ m₂ e₂).2.1 =
        mag m' e' := by
  have hrem := divCore_rem_eq_zero_of_rep h₁ hs h₂ h' hc hv
  have hex : (divCore spec64 m₁ e₁ m₂ e₂).2.2 = .exact :=
    (divCore_acc_exact_iff m₁ e₁ m₂ e₂).mpr hrem
  have hbr := mag_div_bracket m₁ e₁ m₂ e₂ h₂
  have hmag : mag m₁ e₁ / mag m₂ e₂ =
      mag (divCore spec64 m₁ e₁ m₂ e₂).1 (divCore spec64 m₁ e₁ m₂ e₂).2.1 :=
    hbr.1 hex
  exact ⟨hex, hmag.symm.trans hv⟩

/-- If `qa / qb` is itself a finite binary64 value, both directed divisions
    evaluate to that exact value. -/
theorem div_exact {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hqb : qb ≠ 0)
    (hrep : ∃ c, bitsToRat? c = some (qa / qb)) :
    bitsToRat? (divDown a b) = some (qa / qb) ∧
    bitsToRat? (divUp a b) = some (qa / qb) := by
  rcases representable_cases hrep with hq0 | hqf
  · have hqa : qa = 0 := (rat_div_eq_zero hqb).mp hq0
    have hboth : bitsToRat? (divDown a b) = some 0 ∧
        bitsToRat? (divUp a b) = some 0 := by
      simp only [divDown, divUp, Interval64.Spec.div]
      rcases bitsToRat?_cases ha with hza | hfa
      · rcases hza with ⟨s1, hu1, rfl⟩
        rcases bitsToRat?_cases hb with hzb | hfb
        · rcases hzb with ⟨_, _, rfl⟩
          exact (hqb rfl).elim
        · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
          rw [hu1, hu2]
          simp only [divU]
          constructor <;> exact bitsToRat?_packDirected_zero _ _
      · rcases hfa with ⟨_, _, _, h1, _, rfl, _⟩
        exact (signedVal_ne_zero_of_pos h1 hqa).elim
    rw [hq0]
    exact hboth
  · rcases hqf with ⟨sCan, m', e', h', hc, hvq⟩
    simp only [divDown, divUp, Interval64.Spec.div]
    rcases bitsToRat?_cases ha with hza | hfa
    · rcases hza with ⟨_, _, rfl⟩
      have : (0 : Rat) / qb = signedVal sCan m' e' := hvq
      rw [Rat.div_def, Rat.zero_mul] at this
      exact (signedVal_ne_zero_of_pos h' this.symm).elim
    · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hcan1⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨_, _, rfl⟩
        exact (hqb rfl).elim
      · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
        rw [hu1, hu2]
        have hs1 : m1 < 2 ^ 53 := canonical_mantissa_lt hcan1
        have hdivv : signedVal s1 m1 e1 / signedVal s2 m2 e2 =
            signedOf (s1 / s2) (mag m1 e1 / mag m2 e2) :=
          signedVal_div s1 s2 m1 m2 e1 e2 h2
        have hv : mag m1 e1 / mag m2 e2 = mag m' e' :=
          mag_eq_of_signedOf (mag_div_nonneg m1 e1 m2 e2 h2) h'
            (hdivv.symm.trans hvq)
        have ⟨hex, hmageq⟩ := divCore_exact_of_rep h1 hs1 h2 h' hc hv
        let q := (divCore spec64 m1 e1 m2 e2).1
        let te := (divCore spec64 m1 e1 m2 e2).2.1
        have hqpos : 0 < q := by
          refine Nat.pos_of_ne_zero ?_
          intro hq0
          have : mag q te = 0 := by
            rw [hq0]
            simp [mag, Rat.zero_mul]
          have : mag m' e' = 0 := (show mag q te = mag m' e' from hmageq).symm.trans this
          exact mag_ne_zero h' this
        have hvprod : signedVal (s1 / s2) q te = signedVal sCan m' e' := by
          have h1' : signedVal (s1 / s2) q te =
              signedOf (s1 / s2) (mag q te) := signedVal_signedOf _ _ _
          have h2' : signedOf (s1 / s2) (mag q te) =
              signedOf (s1 / s2) (mag m1 e1 / mag m2 e2) := by
            rw [show mag q te = mag m' e' from hmageq, hv]
          exact h1'.trans (h2'.trans (hdivv.symm.trans hvq))
        have hs : s1 / s2 = sCan :=
          signedVal_eq_implies_sign hqpos h' hvprod
        have hvprod' : signedVal sCan q te = signedVal sCan m' e' := by
          rwa [hs] at hvprod
        constructor
        · have heq :=
            roundDirected_eq_of_canonical sCan q te false h' hc hvprod'
          have hdiv :
              divU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
                roundDirected (s1 / s2) q te (divCore spec64 m1 e1 m2 e2).2.2 false :=
            rfl
          rw [hdiv, hex, hs, heq]
          simpa [hvq] using bitsToRat?_packDirected_canonical false sCan h' hc
        · have heq :=
            roundDirected_eq_of_canonical sCan q te true h' hc hvprod'
          have hdiv :
              divU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
                roundDirected (s1 / s2) q te (divCore spec64 m1 e1 m2 e2).2.2 true :=
            rfl
          rw [hdiv, hex, hs, heq]
          simpa [hvq] using bitsToRat?_packDirected_canonical true sCan h' hc


/-! ### Interval membership for `Interval64.div` -/

theorem bitsToRat?_float_zero : bitsToRat? (0 : Float).toBits = some 0 := by decide

theorem unpack_float_zero : ∃ s, unpackBits (0 : Float).toBits = .zero s := by
  have h := bitsToRat?_float_zero
  rcases bitsToRat?_cases h with hz | hf
  · rcases hz with ⟨s, hu, _⟩
    exact ⟨s, hu⟩
  · rcases hf with ⟨s, m, e, hm, _, hq, _⟩
    exact (signedVal_ne_zero_of_pos hm hq.symm).elim

theorem le_zero_iff_rat {f : Float} {q : Rat}
    (h : bitsToRat? f.toBits = some q) : f ≤ 0 ↔ q ≤ 0 := by
  constructor
  · intro hle
    exact float_le_rat h bitsToRat?_float_zero hle
  · intro hle
    have hleU : (unpackBits f.toBits).le (unpackBits (0 : Float).toBits) = true := by
      rcases unpack_float_zero with ⟨sz, hsz⟩
      rw [hsz]
      rcases bitsToRat?_cases h with hz | hf
      · rcases hz with ⟨s, hu, rfl⟩
        simp [hu, UnpackedFloat.le, UnpackedFloat.compare, Option.any]
      · rcases hf with ⟨s, m, e, hm, hu, rfl, _⟩
        cases s with
        | positive =>
          have hpos : ¬ signedVal .positive m e ≤ 0 := by
            intro hle'
            exact (Rat.lt_iff_le_and_not_ge.mp (mag_pos hm)).2 (by
              simpa [signedVal] using hle')
          exact (hpos hle).elim
        | negative =>
          simp [hu, UnpackedFloat.le, UnpackedFloat.compare, Option.any]
    exact (float_le_iff f 0).mpr hleU

theorem zero_le_iff_rat {f : Float} {q : Rat}
    (h : bitsToRat? f.toBits = some q) : 0 ≤ f ↔ 0 ≤ q := by
  constructor
  · intro hle
    exact float_le_rat bitsToRat?_float_zero h hle
  · intro hle
    have hleU : (unpackBits (0 : Float).toBits).le (unpackBits f.toBits) = true := by
      rcases unpack_float_zero with ⟨sz, hsz⟩
      rw [hsz]
      rcases bitsToRat?_cases h with hz | hf
      · rcases hz with ⟨s, hu, rfl⟩
        simp [hu, UnpackedFloat.le, UnpackedFloat.compare, Option.any]
      · rcases hf with ⟨s, m, e, hm, hu, rfl, _⟩
        cases s with
        | negative =>
          have hneg : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
          exact ((Rat.lt_iff_le_and_not_ge.mp hneg).2 hle).elim
        | positive =>
          simp [hu, UnpackedFloat.le, UnpackedFloat.compare, Option.any]
    exact (float_le_iff 0 f).mpr hleU

theorem isInvalid_eq_false_of_rats {I : Interval64.Interval64} {lo hi : Rat}
    (hlo : bitsToRat? I.lo.toBits = some lo)
    (hhi : bitsToRat? I.hi.toBits = some hi) :
    Interval64.isInvalid I = false := by
  have hnlo := not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hlo)
  have hnhi := not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hhi)
  simp only [Interval64.isInvalid, hnlo, hnhi, Bool.or_false]

theorem containsZero_iff {Y : Interval64.Interval64} {blo bhi : Rat}
    (hlo : bitsToRat? Y.lo.toBits = some blo)
    (hhi : bitsToRat? Y.hi.toBits = some bhi) :
    Interval64.containsZero Y = true ↔ blo ≤ 0 ∧ 0 ≤ bhi := by
  have hinv : Interval64.isInvalid Y = false := isInvalid_eq_false_of_rats hlo hhi
  simp only [Interval64.containsZero, hinv, Bool.not_false, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨hle, hge⟩
    exact ⟨(le_zero_iff_rat hlo).mp hle, (zero_le_iff_rat hhi).mp hge⟩
  · intro ⟨hle, hge⟩
    exact ⟨(le_zero_iff_rat hlo).mpr hle, (zero_le_iff_rat hhi).mpr hge⟩

theorem rat_lt_of_lt_of_le {a b c : Rat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h₁) h₂
  have hne : a ≠ c := fun he =>
    (Rat.lt_iff_le_and_not_ge.mp h₁).2 (he ▸ h₂)
  exact Rat.lt_of_le_of_ne hle hne

theorem not_containsZero_same_sign {Y : Interval64.Interval64} {blo bhi : Rat}
    (hlo : bitsToRat? Y.lo.toBits = some blo)
    (hhi : bitsToRat? Y.hi.toBits = some bhi)
    (hz : Interval64.containsZero Y = false) :
    0 < blo ∨ bhi < 0 := by
  have hnot : ¬ (blo ≤ 0 ∧ 0 ≤ bhi) := by
    intro h
    have : Interval64.containsZero Y = true := (containsZero_iff hlo hhi).mpr h
    simp [this] at hz
  by_cases h1 : blo ≤ 0
  · by_cases h2 : 0 ≤ bhi
    · exact (hnot ⟨h1, h2⟩).elim
    · exact Or.inr (Rat.not_le.mp h2)
  · exact Or.inl (Rat.not_le.mp h1)

theorem ne_of_pos_rat {a : Rat} (h : 0 < a) : a ≠ 0 :=
  fun hz => Rat.lt_irrefl (hz ▸ h)

theorem ne_of_neg_rat {a : Rat} (h : a < 0) : a ≠ 0 :=
  fun hz => Rat.lt_irrefl (hz ▸ h)

theorem ne_zero_of_same_sign {blo bhi : Rat} (hle : blo ≤ bhi)
    (hs : 0 < blo ∨ bhi < 0) : blo ≠ 0 ∧ bhi ≠ 0 := by
  cases hs with
  | inl h =>
    exact ⟨ne_of_pos_rat h, ne_of_pos_rat (rat_lt_of_lt_of_le h hle)⟩
  | inr h =>
    exact ⟨ne_of_neg_rat (rat_lt_of_le_of_lt hle h), ne_of_neg_rat h⟩

theorem inv_le_inv_of_pos {a b : Rat} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := rat_lt_of_lt_of_le ha h
  have hbne : b ≠ 0 := ne_of_pos_rat hb
  have hane : a ≠ 0 := ne_of_pos_rat ha
  have h1 : a * b⁻¹ ≤ 1 := by
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hb))
    rwa [Rat.mul_inv_cancel b hbne] at this
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (Rat.inv_pos.mpr ha))
  have h2 : a⁻¹ * (a * b⁻¹) = b⁻¹ := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel a hane, Rat.one_mul]
  have h3 : a⁻¹ * 1 = a⁻¹ := Rat.mul_one _
  rwa [h2, h3] at this

theorem inv_le_inv_of_neg {a b : Rat} (hb : b < 0) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have ha : a < 0 := rat_lt_of_le_of_lt h hb
  have hneg : -b ≤ -a := Rat.neg_le_neg h
  have hbp : 0 < -b := by
    have := Rat.neg_lt_neg hb
    simpa [Rat.neg_zero] using this
  have := inv_le_inv_of_pos hbp hneg
  rw [inv_neg, inv_neg] at this
  have := Rat.neg_le_neg this
  simpa [Rat.neg_neg] using this

theorem inv_bounds {y blo bhi : Rat}
    (hyl : blo ≤ y) (hyh : y ≤ bhi) (hy0 : y ≠ 0)
    (hs : 0 < blo ∨ bhi < 0) :
    bhi⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ blo⁻¹ := by
  cases hs with
  | inl hpos =>
    have hypos : 0 < y := rat_lt_of_lt_of_le hpos hyl
    exact ⟨inv_le_inv_of_pos hypos hyh, inv_le_inv_of_pos hpos hyl⟩
  | inr hneg =>
    have hyneg : y < 0 := rat_lt_of_le_of_lt hyh hneg
    exact ⟨inv_le_inv_of_neg hneg hyh, inv_le_inv_of_neg hyneg hyl⟩

theorem rmin_4_assoc (a b c d : Rat) :
    rmin (rmin a b) (rmin c d) = rmin a (rmin b (rmin c d)) := by
  apply Rat.le_antisymm
  · exact le_rmin
      (Rat.le_trans (rmin_le_left _ _) (rmin_le_left _ _))
      (le_rmin
        (Rat.le_trans (rmin_le_left _ _) (rmin_le_right _ _))
        (le_rmin
          (Rat.le_trans (rmin_le_right _ _) (rmin_le_left _ _))
          (Rat.le_trans (rmin_le_right _ _) (rmin_le_right _ _))))
  · exact le_rmin
      (le_rmin (rmin_le_left a _)
        (Rat.le_trans (rmin_le_right a _) (rmin_le_left b _)))
      (le_rmin
        (Rat.le_trans (rmin_le_right a _)
          (Rat.le_trans (rmin_le_right b _) (rmin_le_left c d)))
        (Rat.le_trans (rmin_le_right a _)
          (Rat.le_trans (rmin_le_right b _) (rmin_le_right c d))))


theorem rmin_comm (a b : Rat) : rmin a b = rmin b a :=
  Rat.le_antisymm
    (le_rmin (rmin_le_right a b) (rmin_le_left a b))
    (le_rmin (rmin_le_right b a) (rmin_le_left b a))

theorem rmax_comm (a b : Rat) : rmax a b = rmax b a :=
  Rat.le_antisymm
    (rmax_le (le_rmax_right b a) (le_rmax_left b a))
    (rmax_le (le_rmax_right a b) (le_rmax_left a b))

theorem rmax_4_assoc (a b c d : Rat) :
    rmax (rmax a b) (rmax c d) = rmax a (rmax b (rmax c d)) := by
  apply Rat.le_antisymm
  · exact rmax_le
      (rmax_le (le_rmax_left a _)
        (Rat.le_trans (le_rmax_left b (rmax c d)) (le_rmax_right a _)))
      (rmax_le
        (Rat.le_trans (le_rmax_left c d)
          (Rat.le_trans (le_rmax_right b _) (le_rmax_right a _)))
        (Rat.le_trans (le_rmax_right c d)
          (Rat.le_trans (le_rmax_right b _) (le_rmax_right a _))))
  · exact rmax_le
      (Rat.le_trans (le_rmax_left a b) (le_rmax_left (rmax a b) _))
      (rmax_le
        (Rat.le_trans (le_rmax_right a b) (le_rmax_left (rmax a b) _))
        (le_rmax_right (rmax a b) _))

theorem min_div_le_of_interval {x y alo ahi blo bhi : Rat}
    (hxl : alo ≤ x) (hxh : x ≤ ahi) (hyl : blo ≤ y) (hyh : y ≤ bhi)
    (hy0 : y ≠ 0) (hs : 0 < blo ∨ bhi < 0) :
    rmin (rmin (alo / blo) (alo / bhi)) (rmin (ahi / blo) (ahi / bhi)) ≤ x / y := by
  have ⟨hinvL, hinvR⟩ := inv_bounds hyl hyh hy0 hs
  have h := min_mul_le_of_interval (blo := bhi⁻¹) (bhi := blo⁻¹) hxl hxh hinvL hinvR
  simp only [← Rat.div_def] at h
  rw [rmin_comm (alo / bhi) (alo / blo), rmin_comm (ahi / bhi) (ahi / blo)] at h
  simpa [Rat.div_def] using h

theorem max_div_ge_of_interval {x y alo ahi blo bhi : Rat}
    (hxl : alo ≤ x) (hxh : x ≤ ahi) (hyl : blo ≤ y) (hyh : y ≤ bhi)
    (hy0 : y ≠ 0) (hs : 0 < blo ∨ bhi < 0) :
    x / y ≤ rmax (rmax (alo / blo) (alo / bhi)) (rmax (ahi / blo) (ahi / bhi)) := by
  have ⟨hinvL, hinvR⟩ := inv_bounds hyl hyh hy0 hs
  have h := max_mul_ge_of_interval (blo := bhi⁻¹) (bhi := blo⁻¹) hxl hxh hinvL hinvR
  simp only [← Rat.div_def] at h
  rw [rmax_comm (alo / bhi) (alo / blo), rmax_comm (ahi / bhi) (ahi / blo)] at h
  simpa [Rat.div_def] using h

theorem loEncloses_divDown {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (hqb : qb ≠ 0) :
    loEncloses? (bitsToEVal (Interval64.Directed.divDown a b).toBits) (qa / qb) := by
  have h := div_encloses_lo ha hb hqb
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  rw [divDown_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

theorem hiEncloses_divUp {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (hqb : qb ≠ 0) :
    hiEncloses? (bitsToEVal (Interval64.Directed.divUp a b).toBits) (qa / qb) := by
  have h := div_encloses_hi ha hb hqb
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  rw [divUp_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

theorem loEncloses_fmin {a b : Float} {xa xb z : Rat}
    (ha : loEncloses? (bitsToEVal a.toBits) xa)
    (hb : loEncloses? (bitsToEVal b.toBits) xb)
    (hx : rmin xa xb ≤ z) :
    loEncloses? (bitsToEVal (Interval64.fmin a b).toBits) z := by
  cases hqa : bitsToRat? a.toBits with
  | none =>
    have hI := eq_negInf_of_loEncloses_not_rat ha hqa
    have := fmin_negInf (Or.inl hI) (ne_none_of_loEncloses ha) (ne_none_of_loEncloses hb)
    simp [this, loEncloses?, loEncloses]
  | some qa =>
    cases hqb : bitsToRat? b.toBits with
    | none =>
      have hI := eq_negInf_of_loEncloses_not_rat hb hqb
      have := fmin_negInf (Or.inr hI) (ne_none_of_loEncloses ha) (ne_none_of_loEncloses hb)
      simp [this, loEncloses?, loEncloses]
    | some qb =>
      rcases bitsToRat?_fmin hqa hqb with ⟨ql, hql, hql_a, hql_b⟩
      have hqa' : qa ≤ xa := by
        have := ha
        simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hqa] at this
        exact this
      have hqb' : qb ≤ xb := by
        have := hb
        simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hqb] at this
        exact this
      have : ql ≤ z :=
        Rat.le_trans (le_rmin (Rat.le_trans hql_a hqa') (Rat.le_trans hql_b hqb')) hx
      rw [bitsToEVal_rat_of_bitsToRat? hql]
      simp [loEncloses?, loEncloses]
      exact this

theorem hiEncloses_fmax {a b : Float} {xa xb z : Rat}
    (ha : hiEncloses? (bitsToEVal a.toBits) xa)
    (hb : hiEncloses? (bitsToEVal b.toBits) xb)
    (hx : z ≤ rmax xa xb) :
    hiEncloses? (bitsToEVal (Interval64.fmax a b).toBits) z := by
  cases hqa : bitsToRat? a.toBits with
  | none =>
    have hI := eq_posInf_of_hiEncloses_not_rat ha hqa
    have := fmax_posInf (Or.inl hI) (ne_none_of_hiEncloses ha) (ne_none_of_hiEncloses hb)
    simp [this, hiEncloses?, hiEncloses]
  | some qa =>
    cases hqb : bitsToRat? b.toBits with
    | none =>
      have hI := eq_posInf_of_hiEncloses_not_rat hb hqb
      have := fmax_posInf (Or.inr hI) (ne_none_of_hiEncloses ha) (ne_none_of_hiEncloses hb)
      simp [this, hiEncloses?, hiEncloses]
    | some qb =>
      rcases bitsToRat?_fmax hqa hqb with ⟨qh, hqh, haq, hbq⟩
      have hqa' : xa ≤ qa := by
        have := ha
        simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hqa] at this
        exact this
      have hqb' : xb ≤ qb := by
        have := hb
        simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hqb] at this
        exact this
      have : z ≤ qh :=
        Rat.le_trans hx (rmax_le (Rat.le_trans hqa' haq) (Rat.le_trans hqb' hbq))
      rw [bitsToEVal_rat_of_bitsToRat? hqh]
      simp [hiEncloses?, hiEncloses]
      exact this

theorem fmin_not_nan {a b : Float}
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (Interval64.fmin a b).isNaN = false := by
  simp only [Interval64.fmin]
  cases h : decide (a < b) with
  | true => simpa [h] using ha
  | false => simpa [h] using hb

theorem fmax_not_nan {a b : Float}
    (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (Interval64.fmax a b).isNaN = false := by
  simp only [Interval64.fmax]
  cases h : decide (a > b) with
  | true => simpa [h] using ha
  | false => simpa [h] using hb

theorem not_nan_of_loEncloses {f : Float} {z : Rat}
    (h : loEncloses? (bitsToEVal f.toBits) z) : f.isNaN = false := by
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem not_nan_of_hiEncloses {f : Float} {z : Rat}
    (h : hiEncloses? (bitsToEVal f.toBits) z) : f.isNaN = false := by
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

/-- The four-corner rule implemented by `Interval64.div`, for finite
    endpoints, when the denominator interval does not contain zero.
    If the denominator contains zero, the result is `whole` (see
    `memIv_whole`). `y ≠ 0` is required because `x / 0` is not a
    meaningful quotient (Lean would send it to `0`). An invalid
    interval has no rational members (`not_memIv_invalid`). -/
theorem div_mem_iv {x y : Rat} {X Y : Interval64.Interval64}
    (hx : MemIv x X) (hy : MemIv y Y) (hy0 : y ≠ 0)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q)
    (hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    MemIv (x / y) (X / Y) := by
  rcases hXlo with ⟨alo, hAlo⟩
  rcases hXhi with ⟨ahi, hAhi⟩
  rcases hYlo with ⟨blo, hBlo⟩
  rcases hYhi with ⟨bhi, hBhi⟩
  have hnan : Interval64.anyNan X Y = false := anyNan_eq_false hx hy
  cases hcz : Interval64.containsZero Y with
  | true =>
    have heq : X / Y = Interval64.whole := by
      change Interval64.div X Y = Interval64.whole
      unfold Interval64.div
      simp [hnan, hcz]
    rw [heq]
    exact memIv_whole _
  | false =>
    have hs : 0 < blo ∨ bhi < 0 := not_containsZero_same_sign hBlo hBhi hcz
    have hxl : alo ≤ x := by
      have := hx.1
      simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hAlo] at this
      exact this
    have hxh : x ≤ ahi := by
      have := hx.2
      simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hAhi] at this
      exact this
    have hyl : blo ≤ y := by
      have := hy.1
      simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hBlo] at this
      exact this
    have hyh : y ≤ bhi := by
      have := hy.2
      simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hBhi] at this
      exact this
    have ⟨hblo0, hbhi0⟩ := ne_zero_of_same_sign (Rat.le_trans hyl hyh) hs
    let d0 := Interval64.Directed.divDown X.lo Y.lo
    let d1 := Interval64.Directed.divDown X.lo Y.hi
    let d2 := Interval64.Directed.divDown X.hi Y.lo
    let d3 := Interval64.Directed.divDown X.hi Y.hi
    let u0 := Interval64.Directed.divUp X.lo Y.lo
    let u1 := Interval64.Directed.divUp X.lo Y.hi
    let u2 := Interval64.Directed.divUp X.hi Y.lo
    let u3 := Interval64.Directed.divUp X.hi Y.hi
    have hlo0 := loEncloses_divDown hAlo hBlo hblo0
    have hlo1 := loEncloses_divDown hAlo hBhi hbhi0
    have hlo2 := loEncloses_divDown hAhi hBlo hblo0
    have hlo3 := loEncloses_divDown hAhi hBhi hbhi0
    have hhi0 := hiEncloses_divUp hAlo hBlo hblo0
    have hhi1 := hiEncloses_divUp hAlo hBhi hbhi0
    have hhi2 := hiEncloses_divUp hAhi hBlo hblo0
    have hhi3 := hiEncloses_divUp hAhi hBhi hbhi0
    have hmin := min_div_le_of_interval hxl hxh hyl hyh hy0 hs
    have hmax := max_div_ge_of_interval hxl hxh hyl hyh hy0 hs
    have hlo23 := loEncloses_fmin hlo2 hlo3 (Rat.le_refl)
    have hlo123 := loEncloses_fmin hlo1 hlo23 (Rat.le_refl)
    have hloall : loEncloses? (bitsToEVal (Interval64.fmin d0
        (Interval64.fmin d1 (Interval64.fmin d2 d3))).toBits) (x / y) :=
      loEncloses_fmin hlo0 hlo123 (by
        rwa [rmin_4_assoc] at hmin)
    have hhi23 := hiEncloses_fmax hhi2 hhi3 (Rat.le_refl)
    have hhi123 := hiEncloses_fmax hhi1 hhi23 (Rat.le_refl)
    have hhiall : hiEncloses? (bitsToEVal (Interval64.fmax u0
        (Interval64.fmax u1 (Interval64.fmax u2 u3))).toBits) (x / y) :=
      hiEncloses_fmax hhi0 hhi123 (by
        rwa [rmax_4_assoc] at hmax)
    have hlonan : (Interval64.fmin d0 (Interval64.fmin d1 (Interval64.fmin d2 d3))).isNaN =
        false :=
      fmin_not_nan (not_nan_of_loEncloses hlo0)
        (fmin_not_nan (not_nan_of_loEncloses hlo1)
          (fmin_not_nan (not_nan_of_loEncloses hlo2) (not_nan_of_loEncloses hlo3)))
    have hhinan : (Interval64.fmax u0 (Interval64.fmax u1 (Interval64.fmax u2 u3))).isNaN =
        false :=
      fmax_not_nan (not_nan_of_hiEncloses hhi0)
        (fmax_not_nan (not_nan_of_hiEncloses hhi1)
          (fmax_not_nan (not_nan_of_hiEncloses hhi2) (not_nan_of_hiEncloses hhi3)))
    have heq : X / Y =
        ⟨Interval64.fmin d0 (Interval64.fmin d1 (Interval64.fmin d2 d3)),
         Interval64.fmax u0 (Interval64.fmax u1 (Interval64.fmax u2 u3))⟩ := by
      change Interval64.div X Y = _
      unfold Interval64.div
      simp [hnan, hcz, d0, d1, d2, d3, u0, u1, u2, u3, hlonan, hhinan]
    rw [heq]
    exact ⟨hloall, hhiall⟩

end Interval64Proofs.Div
