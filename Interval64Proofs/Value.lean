/-
Extended values and enclosure predicates for binary64 bits.
-/
import Interval64Proofs.Pow2

namespace Interval64Proofs.Value

open Interval64.Spec
open Interval64Proofs.Pow2
open Float.Model
open Float.Model.UnpackedFloat

/-! ### binary64 format constants -/

theorem mantissaBitsWithoutImplicit_spec64 :
    spec64.mantissaBitsWithoutImplicit = 52 :=
  rfl

theorem exponentBits_spec64 : spec64.exponentBits = 11 :=
  rfl

theorem mantissaBits_spec64 : spec64.mantissaBits = 53 :=
  rfl

theorem numBits_spec64 : spec64.numBits = 64 :=
  rfl

theorem exponentBias_spec64 : spec64.exponentBias = 1023 :=
  rfl

theorem minExponent_spec64 : spec64.minExponent = -1074 :=
  rfl

/-- Overflow threshold: an unpacked finite with exponent ≥ 972 does not fit
    in binary64 (`biased ≥ 2047`). -/
def overflowExponent : Int := 972

theorem overflowExponent_eq :
    overflowExponent = (2 ^ spec64.exponentBits - 1 : Int) -
      (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) :=
  rfl

/-! ### Extended values -/

/-- Extended rational: a real binary64 payload is finite, ±∞, or NaN
    (represented as `none` at the `Option EVal` layer). -/
inductive EVal where
  | negInf : EVal
  | rat (q : Rat) : EVal
  | posInf : EVal
deriving Repr, DecidableEq

/-- Logical value of an unpacked float. `none` for NaN. -/
def toEVal : UnpackedFloat → Option EVal
  | .notANumber => none
  | .infinity .negative => some .negInf
  | .infinity .positive => some .posInf
  | .zero _ => some (.rat 0)
  | .finite s m e _ => some (.rat (signedVal s m e))

def bitsToEVal (b : UInt64) : Option EVal :=
  toEVal (unpackBits b)

/-- A lower bound `v` encloses `x` when `v ≤ x` in the extended reals
    (`-∞` encloses every rational; `+∞` encloses none). -/
def loEncloses : EVal → Rat → Prop
  | .negInf, _ => True
  | .rat q, x => q ≤ x
  | .posInf, _ => False

/-- An upper bound `v` encloses `x` when `x ≤ v` in the extended reals. -/
def hiEncloses : EVal → Rat → Prop
  | .posInf, _ => True
  | .rat q, x => x ≤ q
  | .negInf, _ => False

def loEncloses? : Option EVal → Rat → Prop
  | some v, x => loEncloses v x
  | none, _ => False

def hiEncloses? : Option EVal → Rat → Prop
  | some v, x => hiEncloses v x
  | none, _ => False

@[simp] theorem loEncloses_negInf (x : Rat) : loEncloses .negInf x := trivial
@[simp] theorem hiEncloses_posInf (x : Rat) : hiEncloses .posInf x := trivial
@[simp] theorem loEncloses_posInf (x : Rat) : loEncloses .posInf x = False := rfl
@[simp] theorem hiEncloses_negInf (x : Rat) : hiEncloses .negInf x = False := rfl
@[simp] theorem loEncloses_rat (q x : Rat) : loEncloses (.rat q) x = (q ≤ x) := rfl
@[simp] theorem hiEncloses_rat (q x : Rat) : hiEncloses (.rat q) x = (x ≤ q) := rfl

@[simp] theorem toEVal_nan : toEVal .notANumber = none := rfl
@[simp] theorem toEVal_negInf : toEVal (.infinity .negative) = some .negInf := rfl
@[simp] theorem toEVal_posInf : toEVal (.infinity .positive) = some .posInf := rfl
@[simp] theorem toEVal_zero (s : Sign) : toEVal (.zero s) = some (.rat 0) := rfl
@[simp] theorem toEVal_finite (s : Sign) (m : Nat) (e : Int) (h : 0 < m) :
    toEVal (.finite s m e h) = some (.rat (signedVal s m e)) :=
  rfl

theorem ofInt_ofNat (m : Nat) : Rat.ofInt (Int.ofNat m) = (m : Rat) :=
  rfl

theorem toRat?_zero (s : Sign) : toRat? (.zero s) = some 0 :=
  rfl

theorem toRat?_nan : toRat? .notANumber = none :=
  rfl

theorem toRat?_inf (s : Sign) : toRat? (.infinity s) = none :=
  rfl

theorem toRat?_finite (s : Sign) (m : Nat) (e : Int) (h : 0 < m) :
    toRat? (.finite s m e h) = some (signedVal s m e) := by
  simp only [toRat?, ofInt_ofNat]
  cases s with
  | positive =>
    simp [signedVal, mag]
  | negative =>
    simp [signedVal, mag]

theorem toRat?_eq_toEVal (u : UnpackedFloat) :
    toRat? u = match toEVal u with
      | some (.rat q) => some q
      | _ => none := by
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => rfl
  | finite s m e h =>
    simp [toRat?_finite, toEVal_finite]

theorem bitsToRat?_eq_bitsToEVal (b : UInt64) :
    bitsToRat? b = match bitsToEVal b with
      | some (.rat q) => some q
      | _ => none :=
  toRat?_eq_toEVal _

theorem bitsToEVal_rat_of_bitsToRat? {b : UInt64} {q : Rat}
    (h : bitsToRat? b = some q) :
    bitsToEVal b = some (.rat q) := by
  have := bitsToRat?_eq_bitsToEVal b
  revert this
  simp [h]
  cases bitsToEVal b with
  | none =>
    intro ht
    cases ht
  | some v =>
    cases v with
    | negInf =>
      intro ht
      cases ht
    | posInf =>
      intro ht
      cases ht
    | rat q' =>
      intro ht
      simp at ht
      simp [ht]

/-- Finite bits (zero or finite, not Inf/NaN) are exactly those with a rational value. -/
theorem isFinite_iff_toRat? (u : UnpackedFloat) :
    UnpackedFloat.isFinite u = true ↔ ∃ q, toRat? u = some q := by
  cases u with
  | notANumber => simp [UnpackedFloat.isFinite, toRat?]
  | infinity s => simp [UnpackedFloat.isFinite, toRat?]
  | zero s => simp [UnpackedFloat.isFinite, toRat?]
  | finite s m e h => simp [UnpackedFloat.isFinite, toRat?_finite]

/-! ### Signed-value inequalities used by directed rounding -/

theorem signedVal_pos_le {m n : Nat} {e : Int} (h : m ≤ n) :
    signedVal .positive m e ≤ signedVal .positive n e := by
  simpa [signedVal, Sign.apply] using mag_le_mag h

theorem signedVal_pos_lt {m n : Nat} {e : Int} (h : m < n) :
    signedVal .positive m e < signedVal .positive n e := by
  simpa [signedVal, Sign.apply] using mag_lt_mag h

theorem neg_le_neg_iff {a b : Rat} : -a ≤ -b ↔ b ≤ a :=
  Rat.neg_le_neg_iff

theorem signedVal_neg_le {m n : Nat} {e : Int} (h : m ≤ n) :
    signedVal .negative n e ≤ signedVal .negative m e := by
  simpa [signedVal] using (neg_le_neg_iff.mpr (mag_le_mag (e := e) h))

theorem signedVal_neg_lt {m n : Nat} {e : Int} (h : m < n) :
    signedVal .negative n e < signedVal .negative m e := by
  simpa [signedVal] using (Rat.neg_lt_neg_iff.mpr (mag_lt_mag (e := e) h))

end Interval64Proofs.Value
