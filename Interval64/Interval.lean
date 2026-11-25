import Interval64.Directed
import Interval64.Widen

/-!
Binary64 intervals with outward directed rounding.

Policy (documented, not IEEE 1788 decorations):
* If any endpoint is NaN, the result is the invalid interval `[NaN, NaN]`.
* `div`: if the denominator contains `0` (including `±0`), the result is
  the whole line `[-∞, +∞]`.
* `sqrt`: if `hi < 0`, the result is invalid. If `lo < 0 ≤ hi`, the domain
  is clipped to `[+0, hi]`. `sqrt(-0)` is `-0`, so `sqrt [-0, +0] = [-0, +0]`.
* Multiplication uses the four-corner rule. A `0 * ∞` corner is skipped;
  if every corner is `0 * ∞`, the result is the whole line (conservative).
* Division corners `±∞ / ±∞` are NaN. They are skipped (`divNaNCorners`, a slow
  path taken only when a corner is NaN); skipping them is sound because such a
  corner is never the extreme one (the finite-numerator corners give the limit).
  Before this fix `[1, ∞] / [1, ∞]` returned `invalid` (an empty enclosure).
-/

namespace Interval64

open Interval64.Directed

/-- A binary64 interval `[lo, hi]`. Declared at the root, so the operations in namespace
`Interval64` work with dot notation (`X.width`, `X.mid`, `X.sqrt`). -/
structure _root_.Interval64 where
  lo : Float
  hi : Float
  deriving Repr, Inhabited

/- The type used to be `Interval64.Interval64`; keep that name as an alias for older code. -/
export _root_ (Interval64)

instance : BEq Interval64 where
  beq a b := sameBitsOrNaN a.lo b.lo && sameBitsOrNaN a.hi b.hi

/-- The empty / invalid interval `[NaN, NaN]`. -/
def invalid : Interval64 := ⟨Float.nan, Float.nan⟩
/-- The whole line `[-∞, +∞]`. -/
def whole    : Interval64 := ⟨-Float.inf, Float.inf⟩
/-- The point interval `[0, 0]`. -/
def zero     : Interval64 := ⟨0.0, 0.0⟩

/-- True if either endpoint is NaN. -/
def isInvalid (i : Interval64) : Bool := i.lo.isNaN || i.hi.isNaN
/-- True if `i` is exactly `[-∞, +∞]`. -/
def isWhole (i : Interval64) : Bool :=
  i.lo.isInf && i.hi.isInf && decide (i.lo < 0) && decide (i.hi > 0)

/-- True if `0` lies in `[lo, hi]` (and the interval is not invalid). -/
def containsZero (i : Interval64) : Bool :=
  !isInvalid i && decide (i.lo ≤ 0) && decide (0 ≤ i.hi)

/-- Build `[lo, hi]`, swapping if reversed and returning invalid if either is NaN. -/
def ofBounds (lo hi : Float) : Interval64 :=
  if lo.isNaN || hi.isNaN then invalid
  else if decide (hi < lo) then ⟨hi, lo⟩
  else ⟨lo, hi⟩

/-- Minimum of two floats (`y` if they compare equal or `x < y` is false). -/
def fmin (x y : Float) : Float := if decide (x < y) then x else y
/-- Maximum of two floats. -/
def fmax (x y : Float) : Float := if decide (x > y) then x else y

/-- True if any of the four endpoints of `a` and `b` is NaN. -/
def anyNan (a b : Interval64) : Bool :=
  a.lo.isNaN || a.hi.isNaN || b.lo.isNaN || b.hi.isNaN

/-- AVX-512 directed interval addition. -/
def add (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else ⟨addDown a.lo b.lo, addUp a.hi b.hi⟩

/-- Outward-rounded interval subtraction. -/
def sub (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else ⟨subDown a.lo b.hi, subUp a.hi b.lo⟩

/-- Accumulate one multiplication corner into `[lo, hi]`, skipping `0 * ∞` and NaN. -/
def accCorner (x y : Float) (lo hi : Float) (got : Bool) : Float × Float × Bool :=
  if (x == 0 && y.isInf) || (y == 0 && x.isInf) then
    (lo, hi, got)
  else
    let d := mulDown x y
    let u := mulUp x y
    if d.isNaN || u.isNaN then (lo, hi, got)
    else if !got then (d, u, true)
    else (if decide (d < lo) then d else lo, if decide (u > hi) then u else hi, true)

/-- Outward-rounded interval multiplication (four-corner rule; see the module doc). -/
def mul (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else
    let (lo, hi, got) := accCorner a.lo b.lo 0 0 false
    let (lo, hi, got) := accCorner a.lo b.hi lo hi got
    let (lo, hi, got) := accCorner a.hi b.lo lo hi got
    let (lo, hi, got) := accCorner a.hi b.hi lo hi got
    if !got then whole else ⟨lo, hi⟩

/-- NaN-skipping minimum (`y` if `x` is NaN, `x` if `y` is NaN). -/
def fminN (x y : Float) : Float := if x.isNaN then y else if y.isNaN then x else fmin x y
/-- NaN-skipping maximum. -/
def fmaxN (x y : Float) : Float := if x.isNaN then y else if y.isNaN then x else fmax x y

/-- Slow path of `div`: some corner is NaN (only `±∞ / ±∞` can be). NaN corners are
    skipped; if all are NaN the result is `whole`. -/
@[noinline] def divNaNCorners (d0 d1 d2 d3 u0 u1 u2 u3 : Float) : Interval64 :=
  let lo := fminN d0 (fminN d1 (fminN d2 d3))
  let hi := fmaxN u0 (fmaxN u1 (fmaxN u2 u3))
  if lo.isNaN || hi.isNaN then whole else ⟨lo, hi⟩

/-- Division. If `0` lies in `b`, returns `whole`. -/
def div (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else if containsZero b then whole
  else
    let d0 := divDown a.lo b.lo
    let d1 := divDown a.lo b.hi
    let d2 := divDown a.hi b.lo
    let d3 := divDown a.hi b.hi
    let u0 := divUp a.lo b.lo
    let u1 := divUp a.lo b.hi
    let u2 := divUp a.hi b.lo
    let u3 := divUp a.hi b.hi
    let lo := fmin d0 (fmin d1 (fmin d2 d3))
    let hi := fmax u0 (fmax u1 (fmax u2 u3))
    if lo.isNaN || hi.isNaN then divNaNCorners d0 d1 d2 d3 u0 u1 u2 u3 else ⟨lo, hi⟩

/-- Outward-rounded interval square root. Invalid if `hi < 0`; a negative `lo` is clipped to `+0`. -/
def sqrt (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if decide (a.hi < 0) then invalid
  else
    let l := if decide (a.lo < 0) then 0.0 else a.lo
    ⟨sqrtDown l, sqrtUp a.hi⟩

/-- fesetround-backed interval addition (same policies as `add`). -/
def feAdd (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid else ⟨feAddDown a.lo b.lo, feAddUp a.hi b.hi⟩

/-- fesetround-backed interval subtraction (same policies as `sub`). -/
def feSub (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid else ⟨feSubDown a.lo b.hi, feSubUp a.hi b.lo⟩

/-- fesetround-backed interval multiplication (same policies as `mul`). -/
def feMul (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else
    let acc (x y lo hi : Float) (got : Bool) : Float × Float × Bool :=
      if (x == 0 && y.isInf) || (y == 0 && x.isInf) then (lo, hi, got)
      else
        let d := feMulDown x y
        let u := feMulUp x y
        if d.isNaN || u.isNaN then (lo, hi, got)
        else if !got then (d, u, true)
        else (if decide (d < lo) then d else lo, if decide (u > hi) then u else hi, true)
    let (lo, hi, got) := acc a.lo b.lo 0 0 false
    let (lo, hi, got) := acc a.lo b.hi lo hi got
    let (lo, hi, got) := acc a.hi b.lo lo hi got
    let (lo, hi, got) := acc a.hi b.hi lo hi got
    if !got then whole else ⟨lo, hi⟩

/-- fesetround-backed interval division (same policies as `div`). -/
def feDiv (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else if containsZero b then whole
  else
    let d0 := feDivDown a.lo b.lo
    let d1 := feDivDown a.lo b.hi
    let d2 := feDivDown a.hi b.lo
    let d3 := feDivDown a.hi b.hi
    let u0 := feDivUp a.lo b.lo
    let u1 := feDivUp a.lo b.hi
    let u2 := feDivUp a.hi b.lo
    let u3 := feDivUp a.hi b.hi
    let lo := fmin d0 (fmin d1 (fmin d2 d3))
    let hi := fmax u0 (fmax u1 (fmax u2 u3))
    if lo.isNaN || hi.isNaN then divNaNCorners d0 d1 d2 d3 u0 u1 u2 u3 else ⟨lo, hi⟩

/-- fesetround-backed interval square root (same policies as `sqrt`). -/
def feSqrt (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if decide (a.hi < 0) then invalid
  else
    let l := if decide (a.lo < 0) then 0.0 else a.lo
    ⟨feSqrtDown l, feSqrtUp a.hi⟩


instance : Add Interval64 := ⟨add⟩
instance : Sub Interval64 := ⟨sub⟩
instance : Mul Interval64 := ⟨mul⟩
instance : Div Interval64 := ⟨div⟩

/-- COMPARE.md-style kernel on two interval 3-vectors: 3 muls + 2 adds, square, compare. -/
def dot3SqCmp (a0 a1 a2 b0 b1 b2 : Interval64) : Bool :=
  let s := a0 * b0 + a1 * b1 + a2 * b2
  let q := s * s
  decide (q.hi < 0) || decide (q.lo > 0)

end Interval64
