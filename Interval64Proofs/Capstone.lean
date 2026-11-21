/-
Capstone: `∀ x ∈ [1/2, 3/2], x*x + x ≤ 15/4`, obtained from the reusable
`MemIv` / `hi_le_of_native` bridge. Membership of `x` in `demoIv` is lifted
through the Lean `Interval64` `mul` and `add` by `mul_mem_iv` and
`add_mem_iv`; the only numeric fact in `sq_add_le` is `demoHi_le'`, now kernel-checked via the
Nat mirror (`Interval64.KF.demoHi_le_kernel`); `demoHi_le` (`native_decide`) remains as a demo. The earlier exactness-based proof is kept
as `sq_add_le_of_exact`.
-/
import Interval64Proofs.Mul
import Interval64Proofs.IntervalMem
import Interval64.NativeDecide
import Interval64Proofs.KernelDemo

namespace Interval64Proofs.Capstone

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Canonical
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.ExactAdd
open Interval64Proofs.Mul
open Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem
open Interval64.NativeDecide
open Float.Model
open Float.Model.UnpackedFloat

theorem rat_two_mul_two : (2 : Rat) * 2 = 4 := by
  have h2 : (2 : Rat) = ((2 : Int) : Rat) := rfl
  have h4 : (4 : Rat) = ((4 : Int) : Rat) := rfl
  rw [h2, h4, ← Rat.intCast_mul]; rfl

theorem rat_three_mul_three : (3 : Rat) * 3 = 9 := by
  have h3 : (3 : Rat) = ((3 : Int) : Rat) := rfl
  have h9 : (9 : Rat) = ((9 : Int) : Rat) := rfl
  rw [h3, h9, ← Rat.intCast_mul]; rfl

theorem rat_three_mul_two : (3 : Rat) * 2 = 6 := by
  have h3 : (3 : Rat) = ((3 : Int) : Rat) := rfl
  have h2 : (2 : Rat) = ((2 : Int) : Rat) := rfl
  have h6 : (6 : Rat) = ((6 : Int) : Rat) := rfl
  rw [h3, h2, h6, ← Rat.intCast_mul]; rfl

theorem rat_nine_add_six : (9 : Rat) + 6 = 15 := by
  have h9 : (9 : Rat) = ((9 : Int) : Rat) := rfl
  have h6 : (6 : Rat) = ((6 : Int) : Rat) := rfl
  have h15 : (15 : Rat) = ((15 : Int) : Rat) := rfl
  rw [h9, h6, h15, ← Rat.intCast_add]; rfl

theorem pow2_two : pow2 2 = 4 := by
  have : (2 : Int) = (2 : Nat) := rfl
  rw [this, pow2_nat, Rat.pow_succ, Rat.pow_one, rat_two_mul_two]

theorem pow2_neg_one : pow2 (-1) = (1 : Rat) / 2 := by
  rw [pow2_neg]
  have : (1 : Int) = (1 : Nat) := rfl
  rw [this, pow2_nat, Rat.pow_one, Rat.div_def, Rat.one_mul]

theorem pow2_neg_two : pow2 (-2) = (1 : Rat) / 4 := by
  rw [pow2_neg]
  have : (2 : Int) = (2 : Nat) := rfl
  rw [this, pow2_nat, Rat.pow_succ, Rat.pow_one, rat_two_mul_two, Rat.div_def, Rat.one_mul]

theorem half_mul_half :
    ((1 : Rat) / 2) * ((1 : Rat) / 2) = (1 : Rat) / 4 := by
  rw [← pow2_neg_one, ← pow2_neg_two, ← pow2_add]; rfl

theorem three_halves_eq : (3 : Rat) / 2 = 3 * pow2 (-1) := by
  rw [pow2_neg_one, Rat.div_def, Rat.div_def, Rat.one_mul]

theorem nine_quarters_eq : (9 : Rat) / 4 = 9 * pow2 (-2) := by
  rw [pow2_neg_two, Rat.div_def, Rat.div_def, Rat.one_mul]

theorem mul_mul_rearrange (a b : Rat) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  rw [Rat.mul_assoc, Rat.mul_assoc]
  -- a * (b * (a * b)) = (a * a) * (b * b)
  -- a * (b * (a * b)) = a * ((b * a) * b)
  rw [← Rat.mul_assoc b a b]
  -- a * ((b * a) * b) 
  rw [Rat.mul_comm b a]
  -- a * ((a * b) * b) = a * (a * (b * b))
  rw [Rat.mul_assoc a b b, ← Rat.mul_assoc]

theorem three_halves_mul :
    ((3 : Rat) / 2) * ((3 : Rat) / 2) = (9 : Rat) / 4 := by
  rw [three_halves_eq, nine_quarters_eq, mul_mul_rearrange, rat_three_mul_three, ← pow2_add]
  rfl

theorem three_halves_mul_add :
    ((3 : Rat) / 2) * ((3 : Rat) / 2) + (3 : Rat) / 2 = (15 : Rat) / 4 := by
  rw [three_halves_mul, nine_quarters_eq, three_halves_eq]
  have hshift : pow2 (-1) = pow2 (-2) * 2 := by
    have : pow2 (-1) = pow2 ((-2 : Int) + 1) := rfl
    rw [this, pow2_add, pow2_one]
  rw [hshift, Rat.mul_comm (pow2 (-2)) 2, ← Rat.mul_assoc,
    rat_three_mul_two, ← Rat.add_mul, rat_nine_add_six]
  have : (15 : Rat) / 4 = 15 * pow2 (-2) := by
    rw [pow2_neg_two, Rat.div_def, Rat.div_def, Rat.one_mul]
  exact this.symm

theorem val_half : signedVal .positive (2 ^ 52) (-53) = (1 : Rat) / 2 := by
  have h := mag_mul_pow2 1 (-1) 52
  have he : ((-1 : Int) - (52 : Nat)) = (-53 : Int) := by decide
  have h' : mag (2 ^ 52) ((-1 : Int) - (52 : Nat)) = mag 1 (-1) := by
    simpa [Nat.one_mul] using h
  have h'' : mag (2 ^ 52) (-53) = mag 1 (-1) := he ▸ h'
  simp only [signedVal]
  rw [h'']
  unfold mag
  have hone : ((1 : Nat) : Rat) = 1 := rfl
  rw [hone, pow2_neg_one, Rat.one_mul]

theorem val_shift (m k : Nat) (e : Int) {e' : Int}
    (he : e - (k : Int) = e') :
    mag (m * 2 ^ k) e' = mag m e := by
  have h := mag_mul_pow2 m e k
  exact he ▸ h

theorem val_half' : signedVal .positive (2 ^ 52) (-53) = (1 : Rat) / 2 :=
  val_half

theorem val_quarter : signedVal .positive (2 ^ 52) (-54) = (1 : Rat) / 4 := by
  have he : ((-2 : Int) - (52 : Nat)) = (-54 : Int) := by decide
  have h' : mag (2 ^ 52) ((-2 : Int) - (52 : Nat)) = mag 1 (-2) := by
    simpa [Nat.one_mul] using mag_mul_pow2 1 (-2) 52
  have h'' : mag (2 ^ 52) (-54) = mag 1 (-2) := he ▸ h'
  simp only [signedVal]
  rw [h'']
  unfold mag
  have hone : ((1 : Nat) : Rat) = 1 := rfl
  rw [hone, pow2_neg_two, Rat.one_mul]

theorem val_scaled {n : Nat} {k : Nat} {e e' : Int} {q : Rat}
    (he : e - (k : Int) = e')
    (hv : mag n e = q) :
    signedVal .positive (n * 2 ^ k) e' = q := by
  have h := mag_mul_pow2 n e k
  simp only [signedVal]
  exact (he ▸ h).trans hv

theorem mag_n_neg1 (n : Nat) : mag n (-1) = (n : Rat) / 2 := by
  unfold mag
  rw [pow2_neg_one, Rat.div_def, Rat.div_def, Rat.one_mul]

theorem mag_n_neg2 (n : Nat) : mag n (-2) = (n : Rat) / 4 := by
  unfold mag
  rw [pow2_neg_two, Rat.div_def, Rat.div_def, Rat.one_mul]

theorem val_three_halves : signedVal .positive (3 * 2 ^ 51) (-52) = (3 : Rat) / 2 :=
  val_scaled (e := -1) (by decide) (mag_n_neg1 3)

theorem val_three_quarters : signedVal .positive (3 * 2 ^ 51) (-53) = (3 : Rat) / 4 :=
  val_scaled (e := -2) (by decide) (mag_n_neg2 3)

theorem val_nine_quarters : signedVal .positive (9 * 2 ^ 49) (-51) = (9 : Rat) / 4 :=
  val_scaled (e := -2) (by decide) (mag_n_neg2 9)

theorem val_fifteen_quarters : signedVal .positive (15 * 2 ^ 49) (-51) = (15 : Rat) / 4 :=
  val_scaled (e := -2) (by decide) (mag_n_neg2 15)

theorem minExp_le_neg54 : spec64.minExponent ≤ (-54 : Int) := by
  simp [minExponent_spec64]

theorem exp_lt_overflow {e : Int} (h : e ≤ (-51 : Int)) : e < overflowExponent := by
  simp [overflowExponent]
  omega

theorem isNormal_half : IsNormal (2 ^ 52) (-53) :=
  ⟨Int.le_trans minExp_le_neg54 (by decide), exp_lt_overflow (by decide),
    Nat.le_refl _, two_pow_52_lt_53⟩

theorem isNormal_quarter : IsNormal (2 ^ 52) (-54) :=
  ⟨minExp_le_neg54, exp_lt_overflow (by decide), Nat.le_refl _, two_pow_52_lt_53⟩

theorem isNormal_three_halves : IsNormal (3 * 2 ^ 51) (-52) :=
  ⟨Int.le_trans minExp_le_neg54 (by decide), exp_lt_overflow (by decide),
    by decide, by decide⟩

theorem isNormal_three_quarters : IsNormal (3 * 2 ^ 51) (-53) :=
  ⟨Int.le_trans minExp_le_neg54 (by decide), exp_lt_overflow (by decide),
    by decide, by decide⟩

theorem isNormal_nine_quarters : IsNormal (9 * 2 ^ 49) (-51) :=
  ⟨Int.le_trans minExp_le_neg54 (by decide), exp_lt_overflow (by decide),
    by decide, by decide⟩

theorem isNormal_fifteen_quarters : IsNormal (15 * 2 ^ 49) (-51) :=
  ⟨Int.le_trans minExp_le_neg54 (by decide), exp_lt_overflow (by decide),
    by decide, by decide⟩

def bitsHalf : UInt64 :=
  packBits (.finite .positive (2 ^ 52) (-53) (Nat.two_pow_pos 52))

def bitsThreeHalves : UInt64 :=
  packBits (.finite .positive (3 * 2 ^ 51) (-52)
    (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51)))

def bitsQuarter : UInt64 :=
  packBits (.finite .positive (2 ^ 52) (-54) (Nat.two_pow_pos 52))

def bitsThreeQuarters : UInt64 :=
  packBits (.finite .positive (3 * 2 ^ 51) (-53)
    (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51)))

def bitsNineQuarters : UInt64 :=
  packBits (.finite .positive (9 * 2 ^ 49) (-51)
    (Nat.mul_pos (by decide : 0 < 9) (Nat.two_pow_pos 49)))

def bitsFifteenQuarters : UInt64 :=
  packBits (.finite .positive (15 * 2 ^ 49) (-51)
    (Nat.mul_pos (by decide : 0 < 15) (Nat.two_pow_pos 49)))

theorem bitsToRat?_half : bitsToRat? bitsHalf = some ((1 : Rat) / 2) := by
  rw [bitsHalf, bitsToRat?_pack_canonical .positive (Nat.two_pow_pos 52)
    (Or.inr isNormal_half), val_half]

theorem bitsToRat?_threeHalves : bitsToRat? bitsThreeHalves = some ((3 : Rat) / 2) := by
  rw [bitsThreeHalves, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51))
      (Or.inr isNormal_three_halves), val_three_halves]

theorem bitsToRat?_quarter : bitsToRat? bitsQuarter = some ((1 : Rat) / 4) := by
  rw [bitsQuarter, bitsToRat?_pack_canonical .positive (Nat.two_pow_pos 52)
    (Or.inr isNormal_quarter), val_quarter]

theorem bitsToRat?_threeQuarters : bitsToRat? bitsThreeQuarters = some ((3 : Rat) / 4) := by
  rw [bitsThreeQuarters, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 3) (Nat.two_pow_pos 51))
      (Or.inr isNormal_three_quarters), val_three_quarters]

theorem bitsToRat?_nineQuarters : bitsToRat? bitsNineQuarters = some ((9 : Rat) / 4) := by
  rw [bitsNineQuarters, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 9) (Nat.two_pow_pos 49))
      (Or.inr isNormal_nine_quarters), val_nine_quarters]

theorem bitsToRat?_fifteenQuarters : bitsToRat? bitsFifteenQuarters = some ((15 : Rat) / 4) := by
  rw [bitsFifteenQuarters, bitsToRat?_pack_canonical .positive
      (Nat.mul_pos (by decide : 0 < 15) (Nat.two_pow_pos 49))
      (Or.inr isNormal_fifteen_quarters), val_fifteen_quarters]

theorem mem_of_bounds {x : Rat} {lo hi : UInt64} {q r : Rat}
    (hlo : bitsToRat? lo = some q) (hhi : bitsToRat? hi = some r)
    (hle : q ≤ x) (hge : x ≤ r) : Mem x lo hi := by
  have hq := bitsToEVal_rat_of_bitsToRat? hlo
  have hr := bitsToEVal_rat_of_bitsToRat? hhi
  refine ⟨?_, ?_⟩
  · simp [loEncloses?, loEncloses, hq]
    exact hle
  · simp [hiEncloses?, hiEncloses, hr]
    exact hge

theorem half_toBits : (0.5 : Float).toBits = bitsHalf := by decide
theorem threeHalves_toBits : (1.5 : Float).toBits = bitsThreeHalves := by decide
theorem fifteenQuarters_toBits : (3.75 : Float).toBits = bitsFifteenQuarters := by decide

theorem bitsToRat?_float_half :
    bitsToRat? (0.5 : Float).toBits = some ((1 : Rat) / 2) := by
  rw [half_toBits, bitsToRat?_half]

theorem bitsToRat?_float_threeHalves :
    bitsToRat? (1.5 : Float).toBits = some ((3 : Rat) / 2) := by
  rw [threeHalves_toBits, bitsToRat?_threeHalves]

theorem bitsToRat?_float_fifteenQuarters :
    bitsToRat? (3.75 : Float).toBits = some ((15 : Rat) / 4) := by
  rw [fifteenQuarters_toBits, bitsToRat?_fifteenQuarters]

theorem mem_demoIv {x : Rat}
    (hlo : (1 : Rat) / 2 ≤ x) (hhi : x ≤ (3 : Rat) / 2) :
    MemIv x demoIv :=
  mem_of_bounds bitsToRat?_float_half bitsToRat?_float_threeHalves hlo hhi

/-- `demoHi ≤ 3.75`, kernel-checked through the Nat mirror (`KernelDemo`); the
    `native_decide` version `demoHi_le` stays in `Interval64.NativeDecide` as a demo. -/
theorem demoHi_le' : demoHi ≤ 3.75 :=
  Interval64.KF.demoHi_le_kernel

/-- `∀ x ∈ [1/2, 3/2], x*x + x ≤ 15/4`, from `demoHi_le'` plus the
    reusable `MemIv` bridge. The only numeric fact is kernel-checked (`decide +kernel`). -/
theorem sq_add_le {x : Rat}
    (hlo : (1 : Rat) / 2 ≤ x) (hhi : x ≤ (3 : Rat) / 2) :
    x * x + x ≤ (15 : Rat) / 4 := by
  have hx : MemIv x demoIv := mem_demoIv hlo hhi
  have hsq : MemIv (x * x) (demoIv * demoIv) :=
    mul_mem_iv hx hx
      ⟨_, bitsToRat?_float_half⟩ ⟨_, bitsToRat?_float_threeHalves⟩
      ⟨_, bitsToRat?_float_half⟩ ⟨_, bitsToRat?_float_threeHalves⟩
  have hadd : MemIv (x * x + x) (demoIv * demoIv + demoIv) :=
    add_mem_iv hsq hx
  exact hi_le_of_native hadd demoHi_le' bitsToRat?_float_fifteenQuarters

/-- Previous capstone, derived by exactness of the representable corners
    rather than from `demoHi_le`. -/
theorem sq_add_le_of_exact {x : Rat}
    (hlo : (1 : Rat) / 2 ≤ x) (hhi : x ≤ (3 : Rat) / 2) :
    x * x + x ≤ (15 : Rat) / 4 := by
  have hx : Mem x bitsHalf bitsThreeHalves :=
    mem_of_bounds bitsToRat?_half bitsToRat?_threeHalves hlo hhi
  have h0 : (0 : Rat) ≤ (1 : Rat) / 2 := by
    rw [← pow2_neg_one]
    exact pow2_nonneg (-1)
  have hsq : Mem (x * x) (mulDown bitsHalf bitsHalf) (mulUp bitsThreeHalves bitsThreeHalves) :=
    mul_mem_nonneg hx hx bitsToRat?_half bitsToRat?_half
      bitsToRat?_threeHalves bitsToRat?_threeHalves h0 h0
  have hrep_lo : ∃ c, bitsToRat? c = some (((1 : Rat) / 2) * ((1 : Rat) / 2)) :=
    ⟨bitsQuarter, half_mul_half.symm ▸ bitsToRat?_quarter⟩
  have hrep_hi : ∃ c, bitsToRat? c = some (((3 : Rat) / 2) * ((3 : Rat) / 2)) :=
    ⟨bitsNineQuarters, three_halves_mul.symm ▸ bitsToRat?_nineQuarters⟩
  have hmul_lo := (mul_exact bitsToRat?_half bitsToRat?_half hrep_lo).1
  have hmul_hi := (mul_exact bitsToRat?_threeHalves bitsToRat?_threeHalves hrep_hi).2
  have hsum_hi : ∃ c, bitsToRat? c =
      some ((((3 : Rat) / 2) * ((3 : Rat) / 2)) + ((3 : Rat) / 2)) :=
    ⟨bitsFifteenQuarters, three_halves_mul_add.symm ▸ bitsToRat?_fifteenQuarters⟩
  have hadd := add_mem hsq hx
    ⟨_, hmul_lo⟩ ⟨_, bitsToRat?_half⟩ ⟨_, hmul_hi⟩ ⟨_, bitsToRat?_threeHalves⟩
  have hhi_bits := (add_exact hmul_hi bitsToRat?_threeHalves hsum_hi).2
  have hv := bitsToEVal_rat_of_bitsToRat? hhi_bits
  have : x * x + x ≤ ((3 : Rat) / 2) * ((3 : Rat) / 2) + (3 : Rat) / 2 := by
    simpa [hiEncloses?, hiEncloses, hv] using hadd.2
  rwa [three_halves_mul_add] at this

end Interval64Proofs.Capstone
