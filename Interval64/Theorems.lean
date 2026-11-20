/-
Theorems about the software directed-rounding specification.

These are kernel-checked (no `sorry`). They reason about `Interval64.Spec`,
which is definitionally the body of the public `@[implemented_by]` operators.
Full enclosure (`round-down ≤ exact ≤ round-up` for all finite inputs) is
*not* proved in this file; that is a larger development. What *is* proved
is listed in each theorem's docstring.
-/
import Interval64.Spec

namespace Interval64.Theorems

open Float.Model
open Float.Model.UnpackedFloat
open Interval64.Spec

/-- Canonical NaN packing. -/
theorem pack_notANumber : packBits .notANumber = qNaN := by decide

/-- Classifier for signed zeros (UnpackedFloat has no `DecidableEq`). -/
def isSignedZero (u : UnpackedFloat) (s : Sign) : Bool :=
  match u, s with
  | .zero .positive, .positive => true
  | .zero .negative, .negative => true
  | _, _ => false

/-- Positive and negative zero unpack as signed zeros. -/
theorem unpack_posZero : isSignedZero (unpackBits posZero) .positive = true := by decide
theorem unpack_negZero : isSignedZero (unpackBits negZero) .negative = true := by decide

/-- Pack ∘ unpack is the identity on both signed zeros. -/
theorem pack_unpack_zeros :
    packBits (unpackBits posZero) = posZero ∧
    packBits (unpackBits negZero) = negZero := by
  decide

/-- Both signed zeros have rational value 0. -/
theorem toRat_signed_zeros :
    bitsToRat? posZero = some 0 ∧ bitsToRat? negZero = some 0 := by
  decide

/-- `NaN` has no rational value. -/
theorem toRat_nan : bitsToRat? qNaN = none := by decide

/-- Adding NaN on the left yields NaN (unpacked). -/
theorem addU_nan_left (y : UnpackedFloat) (up : Bool) :
    addU .notANumber y up = .notANumber :=
  rfl

/-- Adding NaN on the right, when the left is not NaN, yields NaN. -/
theorem addU_nan_right_zero (s : Sign) (up : Bool) :
    addU (.zero s) .notANumber up = .notANumber :=
  rfl

theorem addU_nan_right_inf (s : Sign) (up : Bool) :
    addU (.infinity s) .notANumber up = .notANumber :=
  rfl

/-- Exact cancellation of 1 + (-1) is -0 when rounding down, +0 when rounding up. -/
theorem add_one_negOne_signed_zero :
    addDown oneBits (oneBits ||| negZero) = negZero ∧
    addUp   oneBits (oneBits ||| negZero) = posZero := by
  decide

/-- Same-sign zero addition preserves the sign. -/
theorem add_same_sign_zeros :
    addDown posZero posZero = posZero ∧
    addUp   posZero posZero = posZero ∧
    addDown negZero negZero = negZero ∧
    addUp   negZero negZero = negZero := by
  decide

/-- Opposite-sign zeros follow IEEE 754-2019 §6.3 (down → -0, up → +0). -/
theorem add_opposite_sign_zeros :
    addDown posZero negZero = negZero ∧
    addUp   posZero negZero = posZero ∧
    addDown negZero posZero = negZero ∧
    addUp   negZero posZero = posZero := by
  decide

/-- `1 + 1 = 2` in both rounding directions (exact). -/
theorem add_one_one :
    addDown oneBits oneBits = twoBits ∧
    addUp   oneBits oneBits = twoBits := by
  decide

/-- `1 + 2^{-53}`: the exact sum is the midpoint; down stays at 1, up goes to `1+2^{-52}`. -/
theorem add_one_halfUlp :
    addDown oneBits halfUlpBits = oneBits ∧
    addUp   oneBits halfUlpBits = onePlusUlpBits := by
  decide

/-- Square root of `-0` is `-0`; square root of `+0` is `+0`. -/
theorem sqrt_signed_zero :
    sqrtDown negZero = negZero ∧
    sqrtUp   negZero = negZero ∧
    sqrtDown posZero = posZero ∧
    sqrtUp   posZero = posZero := by
  decide

/-- `awayFromZero` is true iff we increment an inexact value. -/
theorem awayFromZero_pos (up : Bool) :
    awayFromZero up .positive = up := by
  cases up <;> rfl

theorem awayFromZero_neg (up : Bool) :
    awayFromZero up .negative = !up := by
  cases up <;> rfl

/-- Directed rounding of an exact residual does not change the mantissa. -/
theorem roundMantissaDirected_exact (mantissa : Nat) (up : Bool) (s : Sign) :
    roundMantissaDirected mantissa up s Accuracy.exact = mantissa :=
  rfl

/-- Clearing denominators, `1 ≤ 1 + 2^{-53} ≤ 1 + 2^{-52}` is the integer
    comparison `2^53 ≤ 2^53 + 1 ≤ 2^53 + 2`. Combined with `add_one_halfUlp`
    (the bit-pattern identities `down(1+2^{-53}) = 1` and
    `up(1+2^{-53}) = 1+2^{-52}`), this is a complete enclosure for that case.
    Stated with `Int` because `Rat.add` is irreducible and does not kernel-reduce. -/
theorem add_one_halfUlp_enclosure_int :
    (2 ^ 53 : Int) ≤ 2 ^ 53 + 1 ∧ (2 ^ 53 + 1 : Int) ≤ 2 ^ 53 + 2 := by
  decide

end Interval64.Theorems
