/-
Software specification of IEEE 754-2008 binary64 directed rounding.

Built on Lean 4.36's `Float.Model.UnpackedFloat` (unpack/pack, alignment,
`divCore`, `sqrtCore`). The standard model only rounds to nearest-even;
this module adds round-toward-±∞, including IEEE 754-2019 §6.3 signed
zeros and overflow to ±∞ vs ±MaxFinite.

These functions are computable (Nat/Int/BitVec). They are the logical
bodies of the `@[implemented_by]` directed operators.
-/
import Init.Data.Rat.Basic

namespace Interval64.Spec

open Float.Model
open Float.Model.UnpackedFloat

abbrev spec64 : Format := Format.binary64

/-- Canonical quiet NaN (positive, quiet bit set), matching `UnpackedFloat.packedNaN`. -/
def qNaN : UInt64 := 0x7FF8000000000000
def posZero : UInt64 := 0
def negZero : UInt64 := 0x8000000000000000
def posInf : UInt64 := 0x7FF0000000000000
def negInf : UInt64 := 0xFFF0000000000000
def oneBits : UInt64 := 0x3FF0000000000000
def twoBits : UInt64 := 0x4000000000000000
/-- `2^{-53}` -/
def halfUlpBits : UInt64 := 0x3CA0000000000000
/-- `1 + 2^{-52}` -/
def onePlusUlpBits : UInt64 := 0x3FF0000000000001

def unpackBits (b : UInt64) : UnpackedFloat :=
  UnpackedFloat.unpack spec64 b.toBitVec

def packBits (u : UnpackedFloat) : UInt64 :=
  UInt64.ofBitVec (UnpackedFloat.pack spec64 u)

/-- Largest finite binary64 magnitude, already in canonical unpacked form. -/
def maxFinite (s : Sign) : UnpackedFloat :=
  .finite s (2 ^ 53 - 1) 971 (by decide)

/-- True when directed rounding of a positive (resp. negative) value moves
    away from zero: toward +∞ for `up`, toward -∞ for `!up`. -/
def awayFromZero (up : Bool) (s : Sign) : Bool :=
  match s with
  | .positive => up
  | .negative => !up

/-- Directed rounding of a mantissa given residual accuracy bits. -/
def roundMantissaDirected (mantissa : Nat) (up : Bool) (s : Sign) : Accuracy → Nat
  | .exact => mantissa
  | .inexact _ => if awayFromZero up s then mantissa + 1 else mantissa

/-- Round a finite (mantissa, exponent, accuracy) toward +∞ (`up = true`) or -∞.

When the residual is exact and the mantissa is shorter than the format, we first
*decrease* the exponent (`decreaseExponent`), exactly as Lean's `round` does.
`shiftToTargetExponent` only ever shifts right, so without this step a 1-bit
mantissa such as `1 * 2^{-52}` would be packed as a subnormal.
`decreaseExponent` is not used on an inexact residual (`div` / `sqrt` cores
already produce enough bits; a left shift would mis-scale the accuracy). -/
def roundDirected (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (up : Bool) : UnpackedFloat :=
  let (mantissa, exponent) :=
    match accuracy with
    | .exact =>
      let target := spec64.targetExponent (totalExponent mantissa exponent)
      decreaseExponent mantissa exponent target
    | .inexact _ => (mantissa, exponent)
  let (em₁, e₁) := shiftToTargetExponent spec64 mantissa exponent accuracy
  let rounded := roundMantissaDirected em₁.mantissa up sign em₁.accuracy
  let (finalEM, finalE) := shiftToTargetExponent spec64 rounded e₁ Accuracy.exact
  let finalM := finalEM.mantissa
  if h : finalM = 0 then
    .zero sign
  else
    .finite sign finalM finalE (Nat.pos_of_ne_zero h)

/-- Pack, sending overflow to ±∞ or ±MaxFinite according to the rounding direction. -/
def packDirected (up : Bool) (u : UnpackedFloat) : UInt64 :=
  match u with
  | .finite s _m e _ =>
    let biased := (e + spec64.exponentBias + spec64.mantissaBitsWithoutImplicit).toNat
    if 2 ^ spec64.exponentBits ≤ biased + 1 then
      if awayFromZero up s then packBits (.infinity s) else packBits (maxFinite s)
    else
      packBits u
  | _ => packBits u

def normalizeDirected (mantissa : Int) (exponent : Int) (zeroSign : Sign) (up : Bool) :
    UnpackedFloat :=
  match compare mantissa 0 with
  | Ordering.lt => roundDirected .negative (-mantissa).toNat exponent Accuracy.exact up
  | Ordering.eq => .zero zeroSign
  | Ordering.gt => roundDirected .positive mantissa.toNat exponent Accuracy.exact up

/-- Exact-zero sign for directed rounding (IEEE 754-2019 §6.3):
    opposite-sign zeros / cancellation give +0 when rounding up, -0 when rounding down. -/
def cancelZero (up : Bool) : Sign :=
  if up then .positive else .negative

def addU (x y : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x, y with
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity s₁, .infinity s₂ =>
    if decide (s₁ = s₂) then .infinity s₁ else .notANumber
  | .infinity s, _ => .infinity s
  | _, .infinity s => .infinity s
  | .zero s₁, .zero s₂ =>
    if decide (s₁ = s₂) then .zero s₁ else .zero (cancelZero up)
  | .zero _, y => y
  | x, .zero _ => x
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    let smallerExponent := min e₁ e₂
    let (m₁', _) := decreaseExponent m₁ e₁ smallerExponent
    let (m₂', _) := decreaseExponent m₂ e₂ smallerExponent
    let mantissa := s₁.apply m₁' + s₂.apply m₂'
    normalizeDirected mantissa smallerExponent (cancelZero up) up

def mulU (x y : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x, y with
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity s₁, .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity s₁, .finite s₂ .. => .infinity (s₁ * s₂)
  | .finite s₁ .., .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity _, .zero _ => .notANumber
  | .zero _, .infinity _ => .notANumber
  | .finite s₁ .., .zero s₂ => .zero (s₁ * s₂)
  | .zero s₁, .finite s₂ .. => .zero (s₁ * s₂)
  | .zero s₁, .zero s₂ => .zero (s₁ * s₂)
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    roundDirected (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) Accuracy.exact up

def divU (x y : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x, y with
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity _, .infinity _ => .notANumber
  | .infinity s₁, .finite s₂ .. => .infinity (s₁ / s₂)
  | .finite s₁ .., .infinity s₂ => .zero (s₁ / s₂)
  | .infinity s₁, .zero s₂ => .infinity (s₁ / s₂)
  | .zero s₁, .infinity s₂ => .zero (s₁ / s₂)
  | .finite s₁ .., .zero s₂ => .infinity (s₁ / s₂)
  | .zero s₁, .finite s₂ .. => .zero (s₁ / s₂)
  | .zero _, .zero _ => .notANumber
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    let (m, e, acc) := divCore spec64 m₁ e₁ m₂ e₂
    roundDirected (s₁ / s₂) m e acc up

def sqrtU (x : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x with
  | .notANumber => .notANumber
  | .infinity .positive => .infinity .positive
  | .infinity .negative => .notANumber
  | .finite .negative .. => .notANumber
  | .zero s => .zero s
  | .finite .positive m e _ =>
    let (m', e', acc) := sqrtCore spec64 m e
    roundDirected .positive m' e' acc up

def add (a b : UInt64) (up : Bool) : UInt64 := packDirected up (addU (unpackBits a) (unpackBits b) up)
def mul (a b : UInt64) (up : Bool) : UInt64 := packDirected up (mulU (unpackBits a) (unpackBits b) up)
def div (a b : UInt64) (up : Bool) : UInt64 := packDirected up (divU (unpackBits a) (unpackBits b) up)
def sqrt (a : UInt64) (up : Bool) : UInt64 := packDirected up (sqrtU (unpackBits a) up)

/-- Subtraction is addition of the IEEE negation (sign bit flipped, NaN stays NaN). -/
def sub (a b : UInt64) (up : Bool) : UInt64 :=
  packDirected up (addU (unpackBits a) (unpackBits b).neg up)

def addDown (a b : UInt64) : UInt64 := add a b false
def addUp   (a b : UInt64) : UInt64 := add a b true
def subDown (a b : UInt64) : UInt64 := sub a b false
def subUp   (a b : UInt64) : UInt64 := sub a b true
def mulDown (a b : UInt64) : UInt64 := mul a b false
def mulUp   (a b : UInt64) : UInt64 := mul a b true
def divDown (a b : UInt64) : UInt64 := div a b false
def divUp   (a b : UInt64) : UInt64 := div a b true
def sqrtDown (a : UInt64) : UInt64 := sqrt a false
def sqrtUp   (a : UInt64) : UInt64 := sqrt a true

/-- `2^e` as a rational. -/
def pow2 (e : Int) : Rat :=
  if 0 ≤ e then ((2 : Rat) ^ e.toNat) else ((1 : Rat) / (2 : Rat) ^ e.natAbs)

/-- Rational value of a finite or zero unpacked float. `none` for Inf/NaN. -/
def toRat? : UnpackedFloat → Option Rat
  | .zero _ => some 0
  | .finite s m e _ =>
    let mag : Rat := Rat.ofInt (Int.ofNat m) * pow2 e
    some (match s with
      | .positive => mag
      | .negative => -mag)
  | _ => none

def bitsToRat? (b : UInt64) : Option Rat := toRat? (unpackBits b)

def isFiniteBits (b : UInt64) : Bool := (unpackBits b).isFinite
def isNaNBits (b : UInt64) : Bool := (unpackBits b).isNaN

end Interval64.Spec
