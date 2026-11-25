/-
`Interval128`: intervals whose endpoints are double-doubles.

The lower endpoint is `lh + ll` (rounded down), the upper `uh + ul` (rounded
up); each endpoint is the exact sum of its two binary64 words. A reversed
interval is simply empty: no validity check is ever made.

Every operation is a Lean definition (the specification, built from
round-to-nearest core `Float` operations and Interval64's directed
operations, all with logical models) with a single C kernel attached by
`@[implemented_by]` (`c/interval128.c`), bit-identical to the definition.

Policy, per endpoint: the double-double kernel is used when all input words
are finite (mul / div / sqrt) and the computed endpoint is finite; otherwise
that endpoint comes from the Interval64 operation on the outward binary64
hulls (`toInterval64`), which handles infinities, NaN and overflow.
* `div`: if the divisor contains 0, the result is the whole line.
* `sqrt`: an interval whose upper endpoint is negative gives the invalid
  (empty) interval; a negative lower endpoint is clipped to 0.
-/
import Interval128.DD

namespace Interval128

open Interval64 Interval64.Directed

/-- `[lh + ll, uh + ul]`. Flat (four scalar fields) so the runtime allocates one object.
Declared at the root (like `Interval64`), so the operations in namespace `Interval128` work
with dot notation (`X.width`, `X.sqrt`, `X.widthRat`). -/
structure _root_.Interval128 where
  lh : Float
  ll : Float
  uh : Float
  ul : Float
  deriving Repr, Inhabited

/- The type used to be `Interval128.Interval128`; keep that name as an alias for older code. -/
export _root_ (Interval128)

def lo (X : Interval128) : DD := ⟨X.lh, X.ll⟩
def hi (X : Interval128) : DD := ⟨X.uh, X.ul⟩

def ofDD (l u : DD) : Interval128 := ⟨l.hi, l.lo, u.hi, u.lo⟩

/-- Outward binary64 hull: `[RD(lh + ll), RU(uh + ul)]`. -/
def toInterval64 (X : Interval128) : Interval64 := ⟨addDown X.lh X.ll, addUp X.uh X.ul⟩

/-- Exact embedding of a binary64 interval. -/
def ofInterval64 (J : Interval64) : Interval128 := ⟨J.lo, 0, J.hi, 0⟩

def invalid : Interval128 := ofInterval64 Interval64.invalid
def whole : Interval128 := ofInterval64 Interval64.whole

/-- All four words finite. -/
def isFin (X : Interval128) : Bool :=
  X.lh.isFinite && X.ll.isFinite && X.uh.isFinite && X.ul.isFinite

/-- Choose the double-double endpoints where finite, else the Interval64 fallback. -/
def pick (l u : DD) (slow : Unit → Interval64) : Interval128 :=
  if l.isFin then
    if u.isFin then ofDD l u else ofDD l ⟨(slow ()).hi, 0⟩
  else
    if u.isFin then ofDD ⟨(slow ()).lo, 0⟩ u else ofInterval64 (slow ())

/-- Exact negation. -/
def neg (X : Interval128) : Interval128 := ⟨-X.uh, -X.ul, -X.lh, -X.ll⟩

/-! ### Specifications -/

def addSpec (X Y : Interval128) : Interval128 :=
  pick (DD.addLo X.lh X.ll Y.lh Y.ll) (DD.addHi X.uh X.ul Y.uh Y.ul)
    (fun _ => toInterval64 X + toInterval64 Y)

def subSpec (X Y : Interval128) : Interval128 :=
  pick (DD.addLo X.lh X.ll (-Y.uh) (-Y.ul)) (DD.addHi X.uh X.ul (-Y.lh) (-Y.ll))
    (fun _ => toInterval64 X - toInterval64 Y)

/-- Lower endpoint of the product, all words finite (sign-case analysis, exact sign tests). -/
def mulLoF (X Y : Interval128) : DD :=
  if DD.nonneg Y.lh Y.ll then
    (if DD.nonneg X.lh X.ll then DD.mulLo X.lh X.ll Y.lh Y.ll else DD.mulLo X.lh X.ll Y.uh Y.ul)
  else if DD.nonpos Y.uh Y.ul then
    (if DD.nonpos X.uh X.ul then DD.mulLo X.uh X.ul Y.uh Y.ul else DD.mulLo X.uh X.ul Y.lh Y.ll)
  else if DD.nonneg X.lh X.ll then DD.mulLo X.uh X.ul Y.lh Y.ll
  else if DD.nonpos X.uh X.ul then DD.mulLo X.lh X.ll Y.uh Y.ul
  else DD.minLo (DD.mulLo X.lh X.ll Y.uh Y.ul) (DD.mulLo X.uh X.ul Y.lh Y.ll)

/-- Upper endpoint of the product, all words finite. -/
def mulHiF (X Y : Interval128) : DD :=
  if DD.nonneg Y.lh Y.ll then
    (if DD.nonneg X.uh X.ul then DD.mulHi X.uh X.ul Y.uh Y.ul else DD.mulHi X.uh X.ul Y.lh Y.ll)
  else if DD.nonpos Y.uh Y.ul then
    (if DD.nonneg X.lh X.ll then DD.mulHi X.lh X.ll Y.uh Y.ul else DD.mulHi X.lh X.ll Y.lh Y.ll)
  else if DD.nonneg X.lh X.ll then DD.mulHi X.uh X.ul Y.uh Y.ul
  else if DD.nonpos X.uh X.ul then DD.mulHi X.lh X.ll Y.lh Y.ll
  else DD.maxHi (DD.mulHi X.lh X.ll Y.lh Y.ll) (DD.mulHi X.uh X.ul Y.uh Y.ul)

def mulSpec (X Y : Interval128) : Interval128 :=
  if X.isFin && Y.isFin then
    pick (mulLoF X Y) (mulHiF X Y) (fun _ => toInterval64 X * toInterval64 Y)
  else ofInterval64 (toInterval64 X * toInterval64 Y)

/-- Division by a positive divisor (`Y.lo > 0`), all words finite. -/
def divPos (X Y : Interval128) : Interval128 :=
  pick
    (if DD.nonneg X.lh X.ll then DD.divLo X.lh X.ll Y.uh Y.ul else DD.divLo X.lh X.ll Y.lh Y.ll)
    (if DD.nonneg X.uh X.ul then DD.divHi X.uh X.ul Y.lh Y.ll else DD.divHi X.uh X.ul Y.uh Y.ul)
    (fun _ => toInterval64 X / toInterval64 Y)

def divSpec (X Y : Interval128) : Interval128 :=
  if X.isFin && Y.isFin then
    if DD.pos Y.lh Y.ll then divPos X Y
    else if DD.neg Y.uh Y.ul then divPos (neg X) (neg Y)
    else whole
  else ofInterval64 (toInterval64 X / toInterval64 Y)

def sqrtSpec (X : Interval128) : Interval128 :=
  if X.isFin then
    if DD.neg X.uh X.ul then invalid
    else
      pick (if DD.nonneg X.lh X.ll then DD.sqrtLo X.lh X.ll else ⟨0, 0⟩) (DD.sqrtHi X.uh X.ul)
        (fun _ => Interval64.sqrt (toInterval64 X))
  else ofInterval64 (Interval64.sqrt (toInterval64 X))

/-! ### Runtime (C kernels, `c/interval128.c`) -/

@[extern "i128_add"] opaque addImpl (X Y : @& Interval128) : Interval128
@[extern "i128_sub"] opaque subImpl (X Y : @& Interval128) : Interval128
@[extern "i128_mul"] opaque mulImpl (X Y : @& Interval128) : Interval128
@[extern "i128_div"] opaque divImpl (X Y : @& Interval128) : Interval128
@[extern "i128_sqrt"] opaque sqrtImpl (X : @& Interval128) : Interval128

@[implemented_by addImpl] def add (X Y : @& Interval128) : Interval128 := addSpec X Y
@[implemented_by subImpl] def sub (X Y : @& Interval128) : Interval128 := subSpec X Y
@[implemented_by mulImpl] def mul (X Y : @& Interval128) : Interval128 := mulSpec X Y
@[implemented_by divImpl] def div (X Y : @& Interval128) : Interval128 := divSpec X Y
@[implemented_by sqrtImpl] def sqrt (X : @& Interval128) : Interval128 := sqrtSpec X

instance : Add Interval128 := ⟨add⟩
instance : Sub Interval128 := ⟨sub⟩
instance : Mul Interval128 := ⟨mul⟩
instance : Div Interval128 := ⟨div⟩
instance : Neg Interval128 := ⟨neg⟩

/-! ### Conversions -/

/-- Point interval of a double (exact). -/
@[coe] def point (x : Float) : Interval128 := ⟨x, 0, x, 0⟩

/-- Double-double rounded down: `hi = RD(q)`, `lo = RD(q - hi)`. -/
def ddOfRatDown (q : Rat) : DD :=
  let h := Float.ofRatDown q
  match Interval64.Spec.bitsToRat? h.toBits with
  | some r => ⟨h, Float.ofRatDown (q - r)⟩
  | none => ⟨h, 0⟩

/-- Double-double rounded up: `hi = RU(q)`, `lo = RU(q - hi)`. -/
def ddOfRatUp (q : Rat) : DD :=
  let h := Float.ofRatUp q
  match Interval64.Spec.bitsToRat? h.toBits with
  | some r => ⟨h, Float.ofRatUp (q - r)⟩
  | none => ⟨h, 0⟩

/-- Tight (about `2^-106` relative) enclosure of a rational. -/
@[coe] def ofRat (q : Rat) : Interval128 := ofDD (ddOfRatDown q) (ddOfRatUp q)

@[coe] def ofNat (n : Nat) : Interval128 := ofRat n
@[coe] def ofInt (n : Int) : Interval128 := ofRat n

/-- Enclosure of the exact decimal `m · 10^(±e)`. -/
def ofScientific (m : Nat) (s : Bool) (e : Nat) : Interval128 :=
  ofRat (OfScientific.ofScientific m s e : Rat)

instance instOfNat (n : Nat) : OfNat Interval128 n := ⟨ofNat n⟩
instance : NatCast Interval128 := ⟨ofNat⟩
instance : IntCast Interval128 := ⟨ofInt⟩
instance : OfScientific Interval128 := ⟨ofScientific⟩
instance : Coe Rat Interval128 := ⟨ofRat⟩
instance : Coe Float Interval128 := ⟨point⟩
instance : Coe Interval64 Interval128 := ⟨ofInterval64⟩

/-- Upper bound of the width `(uh + ul) - (lh + ll)` as a double. -/
def width (X : Interval128) : Float :=
  addUp (addUp (subUp X.uh X.lh) X.ul) (-X.ll)

end Interval128

namespace Interval128
/-- Compiled backend of the Interval128 kernels: 0 = AVX-512, 1 = RN + exact error. -/
@[extern "i128_backend_id"] opaque backendId (u : Unit) : UInt8
end Interval128
