/-
Readable display of `Interval128` values: `[lo, hi]` where each endpoint is the exact sum of
its two words, rounded to nearest at 34 significant digits. Display only.
-/
import Interval128.Interval
import Interval64.Display

namespace Interval128
namespace Interval128

/-- Exact value of a double-double endpoint `h + l` (`none` if a word is infinite or NaN). -/
def ddRat? (h l : Float) : Option Rat :=
  match Interval64.Spec.bitsToRat? h.toBits, Interval64.Spec.bitsToRat? l.toBits with
  | some a, some b => some (a + b)
  | _, _ => none

/-- Exact endpoints as rationals (`none` for an infinite or NaN endpoint). -/
def exact (X : Interval128) : Option Rat × Option Rat := (ddRat? X.lh X.ll, ddRat? X.uh X.ul)

/-- Exact width `hi - lo` as a rational. -/
def widthRat (X : Interval128) : Option Rat :=
  match X.exact with
  | (some l, some h) => some (h - l)
  | _ => none

private def fmtEnd (h l : Float) (sig : Nat) : String :=
  match ddRat? h l with
  | some q => if q == 0 then Interval64.fmtFloat h else Interval64.fmtRat q sig
  | none => Interval64.fmtFloat h

/-- `[lo, hi]` with 34 significant digits per endpoint. -/
protected def toString (X : Interval128) : String :=
  s!"[{fmtEnd X.lh X.ll 34}, {fmtEnd X.uh X.ul 34}]"

instance (priority := high) : Repr Interval128 := ⟨fun X _ => .text X.toString⟩
instance : ToString Interval128 := ⟨Interval128.toString⟩

end Interval128
end Interval128
