/-
Float-level transfer for the kernel fast path: `toF n = Float.ofBits n`, and each
`Directed` operation / comparison on `toF` values equals `toF` of the `KF` Nat function.
-/
import Interval64Proofs.KernelEq
import Interval64.Interval

set_option linter.unusedSimpArgs false

namespace Interval64.KF

open Interval64.Spec
open Float.Model Float.Model.UnpackedFloat

/-- Canonical bit pattern (all NaNs collapsed to `qNaN`). -/
def canon (n : Nat) : Nat := if isNaN n then qNaN else n

theorem unpackN_qNaN : unpackN qNaN = .notANumber := by
  have : isNaN qNaN = true := by decide
  unfold unpackN; simp [this]

theorem packDirected_eq_packBits_unpackN {n : Nat} (h : n < 2 ^ 64) (up : Bool) :
    packDirected up (unpackN n) = packBits (unpackN n) := by
  unfold unpackN
  by_cases hn : isNaN n = true
  · simp [hn, packDirected]
  by_cases hi : isInf n = true
  · simp [hn, hi, packDirected]
  by_cases hz : isZero n = true
  · simp [hn, hi, hz, packDirected]
  simp only [hn, hi, hz, ite_false, dite_false, Bool.false_eq_true]
  have hq := (IsFin.qexp_le ⟨h, hn, hi, hz⟩)
  unfold packDirected
  dsimp only
  rw [ite_eq_right]
  intro hc
  have : ((qexp n : Int) - 1075 + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat =
      qexp n := by
    show ((qexp n : Int) - 1075 + 1023 + 52).toNat = qexp n
    omega
  rw [this] at hc
  have : 2 ^ spec64.exponentBits = 2048 := rfl
  omega

theorem packBits_unpackN {n : Nat} (h : n < 2 ^ 64) : (packBits (unpackN n)).toNat = canon n := by
  unfold canon
  by_cases hn : isNaN n = true
  · simp only [hn, ite_true]; unfold unpackN; simp only [hn, ite_true]; exact toNat_packBits_nan
  rw [ite_eq_right hn]
  by_cases hi : isInf n = true
  · unfold unpackN; simp only [hn, hi, ite_true, ite_false, Bool.false_eq_true]
    rw [toNat_packBits_inf]
    rw [isInf_iff] at hi
    have := n_split n
    rw [← sgn_sb h, sgn_eq]
    unfold infOf; rw [raw_add, raw_mul, signBit_eq, show infBits = 2047 * 2 ^ 52 by decide]
    omega
  by_cases hz : isZero n = true
  · unfold unpackN; simp only [hn, hi, hz, ite_true, ite_false, dite_true, Bool.false_eq_true]
    rw [toNat_packBits_zero]; exact zero_bits h hz
  rw [← packDirected_eq_packBits_unpackN h false]
  unfold unpackN; simp only [hn, hi, hz, ite_false, dite_false, Bool.false_eq_true]
  exact packDirected_unpackN ⟨h, hn, hi, hz⟩ false

theorem unpackN_canon (n : Nat) : unpackN (canon n) = unpackN n := by
  unfold canon
  by_cases hn : isNaN n = true
  · rw [ite_eq_left hn, unpackN_qNaN]; unfold unpackN; simp [hn]
  · rw [ite_eq_right hn]

theorem canon_lt {n : Nat} (h : n < 2 ^ 64) : canon n < 2 ^ 64 := by
  unfold canon; split
  · decide
  · exact h

/-- The float with bit pattern `n` (NaN canonicalized). -/
def toF (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)

theorem unpackBits_ofNat {n : Nat} (h : n < 2 ^ 64) : unpackBits (UInt64.ofNat n) = unpackN n := by
  rw [unpackBits_eq, UInt64.toNat_ofNat_of_lt' h]

/-- The key transfer fact: the unpacked value of `toF n` is `unpackN n`. -/
theorem unpack_toF {n : Nat} (h : n < 2 ^ 64) : unpackBits (toF n).toBits = unpackN n := by
  have e : (toF n).toBits = packBits (unpackN n) := by
    show (Float.Model.pack (UnpackedFloat.unpack spec64 (UInt64.ofNat n).toBitVec)).toBits = _
    show packBits (unpackBits (UInt64.ofNat n)) = _
    rw [unpackBits_ofNat h]
  rw [e, unpackBits_eq, packBits_unpackN h, unpackN_canon]

theorem toNat_toBits_toF {n : Nat} (h : n < 2 ^ 64) : (toF n).toBits.toNat = canon n := by
  have e : (toF n).toBits = packBits (unpackN n) := by
    show packBits (unpackBits (UInt64.ofNat n)) = _
    rw [unpackBits_ofNat h]
  rw [e, packBits_unpackN h]

theorem toF_congr {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : unpackN x = unpackN y) :
    toF x = toF y := by
  show Float.ofModel (Float.Model.pack (unpackBits (UInt64.ofNat x))) =
    Float.ofModel (Float.Model.pack (unpackBits (UInt64.ofNat y)))
  rw [unpackBits_ofNat hx, unpackBits_ofNat hy, h]

theorem toF_toNat (u : UInt64) : toF u.toNat = Float.ofBits u := by
  unfold toF; rw [UInt64.ofNat_toNat]

/-! ### Results stay below `2^64` -/

theorem add_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (up : Bool) : add x y up < 2 ^ 64 := by
  have := add_eq (UInt64.ofNat x) (UInt64.ofNat y) up
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this]; exact UInt64.toNat_lt _
theorem sub_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (up : Bool) : sub x y up < 2 ^ 64 := by
  have := sub_eq (UInt64.ofNat x) (UInt64.ofNat y) up
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this]; exact UInt64.toNat_lt _
theorem mul_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (up : Bool) : mul x y up < 2 ^ 64 := by
  have := mul_eq (UInt64.ofNat x) (UInt64.ofNat y) up
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this]; exact UInt64.toNat_lt _
theorem div_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (up : Bool) : div x y up < 2 ^ 64 := by
  have := div_eq (UInt64.ofNat x) (UInt64.ofNat y) up
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this]; exact UInt64.toNat_lt _
theorem sqrt_lt {x : Nat} (hx : x < 2 ^ 64) (up : Bool) : sqrt x up < 2 ^ 64 := by
  have := sqrt_eq (UInt64.ofNat x) up
  rw [UInt64.toNat_ofNat_of_lt' hx] at this
  rw [← this]; exact UInt64.toNat_lt _

/-! ### Directed operations on `toF` values -/

theorem toF_spec (u : UInt64) : toF u.toNat = Float.ofBits u := toF_toNat u

theorem addDown_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.addDown (toF x) (toF y) = toF (add x y false) := by
  have := add_eq (UInt64.ofNat x) (UInt64.ofNat y) false
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.add _ _ false) = Float.ofBits (Spec.add _ _ false)
  unfold Spec.add; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem addUp_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.addUp (toF x) (toF y) = toF (add x y true) := by
  have := add_eq (UInt64.ofNat x) (UInt64.ofNat y) true
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.add _ _ true) = Float.ofBits (Spec.add _ _ true)
  unfold Spec.add; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem subDown_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.subDown (toF x) (toF y) = toF (sub x y false) := by
  have := sub_eq (UInt64.ofNat x) (UInt64.ofNat y) false
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.sub _ _ false) = Float.ofBits (Spec.sub _ _ false)
  unfold Spec.sub; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem subUp_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.subUp (toF x) (toF y) = toF (sub x y true) := by
  have := sub_eq (UInt64.ofNat x) (UInt64.ofNat y) true
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.sub _ _ true) = Float.ofBits (Spec.sub _ _ true)
  unfold Spec.sub; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem mulDown_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.mulDown (toF x) (toF y) = toF (mul x y false) := by
  have := mul_eq (UInt64.ofNat x) (UInt64.ofNat y) false
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.mul _ _ false) = Float.ofBits (Spec.mul _ _ false)
  unfold Spec.mul; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem mulUp_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.mulUp (toF x) (toF y) = toF (mul x y true) := by
  have := mul_eq (UInt64.ofNat x) (UInt64.ofNat y) true
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.mul _ _ true) = Float.ofBits (Spec.mul _ _ true)
  unfold Spec.mul; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem divDown_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.divDown (toF x) (toF y) = toF (div x y false) := by
  have := div_eq (UInt64.ofNat x) (UInt64.ofNat y) false
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.div _ _ false) = Float.ofBits (Spec.div _ _ false)
  unfold Spec.div; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem divUp_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Directed.divUp (toF x) (toF y) = toF (div x y true) := by
  have := div_eq (UInt64.ofNat x) (UInt64.ofNat y) true
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.div _ _ true) = Float.ofBits (Spec.div _ _ true)
  unfold Spec.div; rw [unpack_toF hx, unpack_toF hy, unpackBits_ofNat hx, unpackBits_ofNat hy]
theorem sqrtDown_toF {x : Nat} (hx : x < 2 ^ 64) :
    Directed.sqrtDown (toF x) = toF (sqrt x false) := by
  have := sqrt_eq (UInt64.ofNat x) false
  rw [UInt64.toNat_ofNat_of_lt' hx] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.sqrt _ false) = Float.ofBits (Spec.sqrt _ false)
  unfold Spec.sqrt; rw [unpack_toF hx, unpackBits_ofNat hx]
theorem sqrtUp_toF {x : Nat} (hx : x < 2 ^ 64) :
    Directed.sqrtUp (toF x) = toF (sqrt x true) := by
  have := sqrt_eq (UInt64.ofNat x) true
  rw [UInt64.toNat_ofNat_of_lt' hx] at this
  rw [← this, toF_toNat]
  show Float.ofBits (Spec.sqrt _ true) = Float.ofBits (Spec.sqrt _ true)
  unfold Spec.sqrt; rw [unpack_toF hx, unpackBits_ofNat hx]

/-! ### Predicates and comparisons on `toF` values -/

theorem cmpN {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    cmp x y = codeOf ((unpackN x).compare (unpackN y)) := by
  have := cmp_eq (UInt64.ofNat x) (UInt64.ofNat y)
  rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy, unpackBits_ofNat hx,
    unpackBits_ofNat hy] at this

theorem isNaN_toF {x : Nat} (hx : x < 2 ^ 64) : (toF x).isNaN = isNaN x := by
  show (unpackBits (toF x).toBits).isNaN = _
  rw [unpack_toF hx]; unfold unpackN
  by_cases hn : isNaN x = true
  · simp [hn, UnpackedFloat.isNaN]
  · simp only [hn, ite_false, Bool.false_eq_true]
    have : isNaN x = false := by simpa using hn
    split
    · rfl
    · split <;> rfl

theorem isInf_toF {x : Nat} (hx : x < 2 ^ 64) : (toF x).isInf = (!isNaN x && isInf x) := by
  show (unpackBits (toF x).toBits).isInf = _
  rw [unpack_toF hx]; unfold unpackN
  by_cases hn : isNaN x = true
  · simp [hn, UnpackedFloat.isInf]
  by_cases hi : isInf x = true
  · simp [hn, hi, UnpackedFloat.isInf]
  · simp only [hn, hi, ite_false, Bool.false_eq_true]
    have h1 : isNaN x = false := by simpa using hn
    have h2 : isInf x = false := by simpa using hi
    split <;> rfl

theorem lt_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    decide (toF x < toF y) = lt x y := by
  have e : decide (toF x < toF y) = (unpackN x).lt (unpackN y) := by
    show decide ((unpackBits (toF x).toBits).lt (unpackBits (toF y).toBits) = true) = _
    rw [unpack_toF hx, unpack_toF hy]; simp
  rw [e]; unfold lt UnpackedFloat.lt; rw [cmpN hx hy]
  generalize (unpackN x).compare (unpackN y) = o
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem le_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    decide (toF x ≤ toF y) = le x y := by
  have e : decide (toF x ≤ toF y) = (unpackN x).le (unpackN y) := by
    show decide ((unpackBits (toF x).toBits).le (unpackBits (toF y).toBits) = true) = _
    rw [unpack_toF hx, unpack_toF hy]; simp
  rw [e]; unfold le UnpackedFloat.le; rw [cmpN hx hy]
  generalize (unpackN x).compare (unpackN y) = o
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem beq_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (toF x == toF y) = beq x y := by
  have e : (toF x == toF y) = (unpackN x).beq (unpackN y) := by
    show (unpackBits (toF x).toBits).beq (unpackBits (toF y).toBits) = _
    rw [unpack_toF hx, unpack_toF hy]
  rw [e]; unfold beq UnpackedFloat.beq; rw [cmpN hx hy]
  generalize (unpackN x).compare (unpackN y) = o
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem neg_toF {x : Nat} (hx : x < 2 ^ 64) : -toF x = toF (negBits x) := by
  obtain ⟨hlt, -⟩ := negBits_fields hx
  show Float.ofModel (Float.Model.pack (unpackBits (toF x).toBits).neg) = _
  rw [unpack_toF hx, ← unpackN_neg hx]
  show _ = Float.ofModel (Float.Model.pack (unpackBits (UInt64.ofNat (negBits x))))
  rw [unpackBits_ofNat hlt]

end Interval64.KF
