/-
Rational → binary64 directed rounding, representability, and `Interval64.ofRat`.

These are logical (spec) functions: they are computed in Lean, not by the C
kernels, but are `#eval`-able. Rounding is IEEE 754 directed rounding with
IEEE overflow: toward −∞ a huge positive goes to `+MaxFinite` and a huge
negative to `−∞`; toward +∞ dually. `ofRat 0` is `[+0, +0]`.

`ofRatU` reuses the same `roundDirected` / `packDirected` code path as the
arithmetic operators: it writes `|q| = Y · 2^E` with `E` chosen so that
`E = minExponent` or `⌊Y⌋ ≥ 2^52`, and hands `(⌊Y⌋, E)` with an exact /
inexact flag to `roundDirected`.
-/
import Interval64.Spec
import Interval64.Interval

namespace Interval64.Spec

open Float.Model
open Float.Model.UnpackedFloat

/-- A rational is representable when it is the value of some finite binary64
    (zero, subnormal, or normal). -/
def Representable (q : Rat) : Prop := ∃ b : UInt64, bitsToRat? b = some q

/-- Exponent used to scale `X > 0` before taking the floor:
    `max minExponent (log₂ num − log₂ den − 53)`, so that either
    `E = minExponent` or `X / 2^E ≥ 2^52`. -/
def ratExp (X : Rat) : Int :=
  max spec64.minExponent ((X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 53)

/-- Sign of a nonzero rational. -/
def ratSign (q : Rat) : Sign := if q < 0 then .negative else .positive
/-- Absolute value. -/
def ratAbs (q : Rat) : Rat := if q < 0 then -q else q
/-- `⌊X / 2^E⌋` with `E = ratExp X`. -/
def ratMant (X : Rat) : Nat := (X / pow2 (ratExp X)).floor.toNat
/-- Exact iff `X = ratMant X · 2^E`. -/
def ratAcc (X : Rat) : Accuracy :=
  if (ratMant X : Rat) = X / pow2 (ratExp X) then .exact else .inexact .lt

/-- Unpacked directed rounding of a rational (before overflow packing). -/
def ofRatU (q : Rat) (up : Bool) : UnpackedFloat :=
  if q = 0 then .zero .positive
  else roundDirected (ratSign q) (ratMant (ratAbs q)) (ratExp (ratAbs q)) (ratAcc (ratAbs q)) up

/-- Greatest binary64 `≤ q` (or `−∞` if none). -/
def ofRatDown (q : Rat) : UInt64 := packDirected false (ofRatU q false)
/-- Least binary64 `≥ q` (or `+∞` if none). -/
def ofRatUp (q : Rat) : UInt64 := packDirected true (ofRatU q true)

/-- Computable representability test: round down and compare. -/
def isRepresentable (q : Rat) : Bool := bitsToRat? (ofRatDown q) == some q

end Interval64.Spec

namespace Interval64

/-- `Float` round-down of a rational. -/
def Float.ofRatDown (q : Rat) : Float := Float.ofBits (Spec.ofRatDown q)
/-- `Float` round-up of a rational. -/
def Float.ofRatUp (q : Rat) : Float := Float.ofBits (Spec.ofRatUp q)

/-- Tightest `Interval64` containing the rational `q`. -/
def ofRat (q : Rat) : Interval64 := ⟨Float.ofRatDown q, Float.ofRatUp q⟩

/-- Tightest `Interval64` containing `[lo, hi]` (intended for `lo ≤ hi`). -/
def ofRatInterval (lo hi : Rat) : Interval64 := ⟨Float.ofRatDown lo, Float.ofRatUp hi⟩

end Interval64
