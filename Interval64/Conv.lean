/-
Safe conversions into `Interval64` (no new runtime checks; existing operations
are untouched).

* `OfNat Interval64 n`      : `ofRat n` (exact if representable, else the
                              tightest outward enclosure).
* `OfScientific Interval64` : `ofRat` of the *exact* decimal `m · 10^±e`, so
                              `(0.1 : Interval64)` encloses `1/10` (a `Float`
                              literal `0.1` does not equal `1/10`).
* `NatCast`, `IntCast`      : `ofRat`; these give `↑n` coercions from `Nat`/`Int`.
* `Coe Rat Interval64`      : `ofRat` (core has no `RatCast` class).
* `Coe Float Interval64`    : the point interval `⟨x, x⟩` (`point`). The `Float`
                              is taken as the exact value it holds; NaN gives an
                              invalid interval, `±∞` gives `⟨±∞, ±∞⟩`, which
                              encloses no real (empty `toSet`).

With these, `X + 2`, `X * 0.1`, `X + (q : Rat)`, `X + (n : Nat)`, `X + (f : Float)`
elaborate via `binop%` to `Interval64` operations.
-/
import Interval64.OfRat

namespace Interval64

/-- Point interval `[x, x]` of a double (NaN → invalid; `±∞` → empty). -/
@[coe] def point (x : Float) : Interval64 := ⟨x, x⟩

/-- Tightest interval containing the natural number `n`. -/
@[coe] def ofNat (n : Nat) : Interval64 := ofRat n

/-- Tightest interval containing the integer `n`. -/
@[coe] def ofInt (n : Int) : Interval64 := ofRat n

attribute [coe] ofRat

/-- Tightest interval containing the exact decimal `m · 10^(±e)`. -/
def ofScientific (m : Nat) (s : Bool) (e : Nat) : Interval64 :=
  ofRat (OfScientific.ofScientific m s e : Rat)

instance instOfNat (n : Nat) : OfNat Interval64 n := ⟨ofNat n⟩
instance : NatCast Interval64 := ⟨ofNat⟩
instance : IntCast Interval64 := ⟨ofInt⟩
instance : OfScientific Interval64 := ⟨ofScientific⟩
instance : Coe Rat Interval64 := ⟨ofRat⟩
instance : Coe Float Interval64 := ⟨point⟩

@[simp] theorem ofNat_def (n : Nat) : (OfNat.ofNat n : Interval64) = ofRat n := rfl
@[simp] theorem natCast_def (n : Nat) : ((n : Nat) : Interval64) = ofRat n := rfl
@[simp] theorem intCast_def (n : Int) : ((n : Int) : Interval64) = ofRat n := rfl
@[simp] theorem ratCoe_def (q : Rat) : ((q : Rat) : Interval64) = ofRat q := rfl
@[simp] theorem floatCoe_def (x : Float) : ((x : Float) : Interval64) = ⟨x, x⟩ := rfl
@[simp] theorem ofScientific_def (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Interval64) = ofRat (OfScientific.ofScientific m s e : Rat) :=
  rfl

end Interval64
