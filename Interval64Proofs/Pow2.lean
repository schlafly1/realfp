/-
Algebra of `Interval64.Spec.pow2` (`2^e` as a rational).
-/
import Interval64.Spec
import Init.Data.Rat.Lemmas

namespace Interval64Proofs.Pow2

open Interval64.Spec
open Float.Model
open Float.Model.UnpackedFloat

theorem two_ne_zero : (2 : Rat) ≠ 0 := by
  decide

theorem two_pos : (0 : Rat) < 2 := by
  decide

theorem two_nonneg : (0 : Rat) ≤ 2 :=
  Rat.le_of_lt two_pos

/-- `pow2 e` agrees with integer power `(2 : Rat) ^ e`. -/
theorem pow2_eq_zpow (e : Int) : pow2 e = (2 : Rat) ^ e := by
  unfold pow2
  split
  · rename_i h
    have he : (e.toNat : Int) = e := Int.toNat_of_nonneg h
    calc
      (2 : Rat) ^ e.toNat = (2 : Rat) ^ (e.toNat : Int) := (Rat.zpow_natCast 2 e.toNat).symm
      _ = (2 : Rat) ^ e := by rw [he]
  · rename_i h
    have hle : e ≤ 0 := Int.le_of_not_le h
    have habs : (e.natAbs : Int) = -e := Int.ofNat_natAbs_of_nonpos hle
    have hz : (2 : Rat) ^ e = ((2 : Rat) ^ (-e))⁻¹ := by
      rw [← Rat.zpow_neg, Int.neg_neg]
    rw [hz, ← habs, Rat.zpow_natCast, Rat.div_def, Rat.one_mul]

theorem pow2_zero : pow2 0 = 1 := by
  simp [pow2_eq_zpow]

theorem pow2_one : pow2 1 = 2 := by
  simp [pow2_eq_zpow]

theorem pow2_pos (e : Int) : (0 : Rat) < pow2 e := by
  rw [pow2_eq_zpow]
  exact Rat.zpow_pos two_pos

theorem pow2_ne_zero (e : Int) : pow2 e ≠ 0 :=
  Rat.ne_of_gt (pow2_pos e)

theorem pow2_nonneg (e : Int) : (0 : Rat) ≤ pow2 e :=
  Rat.le_of_lt (pow2_pos e)

theorem pow2_add (a b : Int) : pow2 (a + b) = pow2 a * pow2 b := by
  simp [pow2_eq_zpow, Rat.zpow_add two_ne_zero]

theorem pow2_neg (e : Int) : pow2 (-e) = (pow2 e)⁻¹ := by
  simp [pow2_eq_zpow, Rat.zpow_neg]

theorem pow2_sub (a b : Int) : pow2 (a - b) = pow2 a / pow2 b := by
  rw [Int.sub_eq_add_neg, pow2_add, pow2_neg, Rat.div_def]

theorem pow2_succ (e : Int) : pow2 (e + 1) = pow2 e * 2 := by
  rw [pow2_add, pow2_one]

theorem pow2_nat (n : Nat) : pow2 (n : Int) = (2 : Rat) ^ n := by
  rw [pow2_eq_zpow, Rat.zpow_natCast]

/-- Magnitude `m * 2^e`. -/
def mag (m : Nat) (e : Int) : Rat := (m : Rat) * pow2 e

theorem mag_zero (e : Int) : mag 0 e = 0 := by
  simp [mag]

theorem mag_nonneg (m : Nat) (e : Int) : (0 : Rat) ≤ mag m e :=
  Rat.mul_nonneg (Rat.natCast_nonneg) (pow2_nonneg e)

theorem mag_add (m n : Nat) (e : Int) : mag (m + n) e = mag m e + mag n e := by
  simp [mag, Rat.natCast_add, Rat.add_mul]

theorem mag_mul_pow2 (m : Nat) (e : Int) (k : Nat) :
    mag (m * 2 ^ k) (e - k) = mag m e := by
  unfold mag
  rw [Rat.natCast_mul, Rat.natCast_pow]
  have h2 : ((2 : Nat) : Rat) = (2 : Rat) := rfl
  have hk : ((2 : Nat) : Rat) ^ k = pow2 (k : Int) := by
    rw [h2, pow2_nat]
  rw [hk, Rat.mul_assoc, ← pow2_add]
  rw [Int.add_comm (k : Int) (e - (k : Int)), Int.sub_add_cancel]


theorem mag_shiftLeft (m k : Nat) (e : Int) :
    mag (m <<< k) (e - k) = mag m e := by
  rw [Nat.shiftLeft_eq]
  exact mag_mul_pow2 m e k

theorem decreaseExponent_mag (m : Nat) (e t : Int) :
    mag ((decreaseExponent m e t).1) ((decreaseExponent m e t).2) = mag m e := by
  simp only [decreaseExponent]
  exact mag_shiftLeft m (e - t).toNat e

/-- Signed magnitude `± m * 2^e`. -/
def signedVal (s : Sign) (m : Nat) (e : Int) : Rat :=
  match s with
  | .positive => mag m e
  | .negative => -mag m e

theorem signedVal_nonneg_iff (m : Nat) (e : Int) :
    (0 : Rat) ≤ signedVal .positive m e :=
  mag_nonneg m e

theorem signedVal_neg (m : Nat) (e : Int) :
    signedVal .negative m e = -signedVal .positive m e :=
  rfl

theorem signedVal_apply (s : Sign) (m : Nat) (e : Int) :
    (s.apply (m : Int) : Rat) * pow2 e = signedVal s m e := by
  cases s with
  | negative =>
    simp [Sign.apply, signedVal, mag, Rat.intCast_neg, Rat.neg_mul, Rat.intCast_natCast]
  | positive =>
    simp [Sign.apply, signedVal, mag, Rat.intCast_natCast]

theorem signedVal_add_aligned (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e : Int) :
    ((s₁.apply (m₁ : Int) + s₂.apply (m₂ : Int) : Int) : Rat) * pow2 e =
      signedVal s₁ m₁ e + signedVal s₂ m₂ e := by
  rw [Rat.intCast_add, Rat.add_mul, signedVal_apply, signedVal_apply]


theorem mag_one (e : Int) : mag 1 e = pow2 e := by
  simp [mag]

theorem mag_le_mag {m n : Nat} {e : Int} (h : m ≤ n) : mag m e ≤ mag n e :=
  Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr h) (pow2_nonneg e)

theorem mag_lt_mag {m n : Nat} {e : Int} (h : m < n) : mag m e < mag n e :=
  Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr h) (pow2_pos e)

theorem mag_mul_two_pow_add (q k : Nat) (e : Int) :
    mag (q * 2 ^ k) e = mag q (e + k) := by
  unfold mag
  rw [Rat.natCast_mul, Rat.natCast_pow]
  have h2 : ((2 : Nat) : Rat) = (2 : Rat) := rfl
  rw [h2, ← pow2_nat, Rat.mul_assoc, ← pow2_add, Int.add_comm (k : Int)]

theorem mag_split (m k : Nat) (e : Int) :
    mag m e = mag (m >>> k) (e + k) + mag (m % 2 ^ k) e := by
  have hm : m = (m >>> k) * 2 ^ k + m % 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact (Nat.div_add_mod m (2 ^ k)).symm
  conv => lhs; rw [hm]
  rw [mag_add, mag_mul_two_pow_add]

theorem le_add_of_nonneg_right {a b : Rat} (h : 0 ≤ b) : a ≤ a + b := by
  have := (Rat.add_le_add_left (a := 0) (b := b) (c := a)).mpr h
  simpa [Rat.add_zero] using this

theorem mag_shiftRight_le (m k : Nat) (e : Int) :
    mag (m >>> k) (e + k) ≤ mag m e := by
  conv => rhs; rw [mag_split m k e]
  exact le_add_of_nonneg_right (mag_nonneg _ _)

theorem mag_two_pow (k : Nat) (e : Int) : mag (2 ^ k) e = pow2 (e + k) := by
  unfold mag
  rw [Rat.natCast_pow]
  have h2 : ((2 : Nat) : Rat) = (2 : Rat) := rfl
  rw [h2, ← pow2_nat, Rat.mul_comm, ← pow2_add]

theorem mag_lt_shiftRight_succ (m k : Nat) (e : Int) (_hr : m % 2 ^ k ≠ 0) :
    mag m e < mag ((m >>> k) + 1) (e + k) := by
  have hrmlt : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (Nat.two_pow_pos k)
  conv => lhs; rw [mag_split m k e]
  rw [mag_add, mag_one]
  have hlt : mag (m % 2 ^ k) e < pow2 (e + k) := by
    have : mag (m % 2 ^ k) e < mag (2 ^ k) e := mag_lt_mag hrmlt
    rwa [mag_two_pow] at this
  exact (Rat.add_lt_add_left (a := mag (m % 2 ^ k) e) (b := pow2 (e + k))
    (c := mag (m >>> k) (e + k))).mpr hlt

end Interval64Proofs.Pow2
