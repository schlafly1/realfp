/-
Readable, full-precision display of `Interval64` values.

`#eval X` prints `[lo, hi]` with each endpoint rounded to nearest at 17 significant digits,
which is enough for the decimal to read back as exactly the same double (so the two ends of
`(0.1 : Interval64)` print differently). For exact values use `X.exact` (endpoints as
rationals) and `X.widthRat`. Display only: nothing here is used by the arithmetic or proofs.
-/
import Interval64.Interval

namespace Interval64

/-- Decimal string of a rational with `sig` significant digits (round half up), in fixed
notation for exponents `-5 ≤ e < sig` and `d.ddde±x` otherwise; trailing zeros are dropped. -/
def fmtRat (q : Rat) (sig : Nat := 17) : String := Id.run do
  if q == 0 then return "0"
  let sig := max sig 1
  let neg := q < 0
  let a := if neg then -q else q
  let n := a.num.natAbs
  let d := a.den
  -- e = ⌊log₁₀ a⌋: start from the digit counts, then correct.
  let mut e : Int := ((toString n).length : Int) - ((toString d).length : Int)
  let ge (k : Int) : Bool :=  -- a ≥ 10^k
    if k ≥ 0 then n ≥ d * 10 ^ k.toNat else n * 10 ^ (-k).toNat ≥ d
  for _ in [0:4] do
    if !ge e then e := e - 1
  for _ in [0:4] do
    if ge (e + 1) then e := e + 1
  -- m = round(a · 10^(sig-1-e)), an integer with `sig` digits.
  let k : Int := (sig : Int) - 1 - e
  let (num, den) := if k ≥ 0 then (n * 10 ^ k.toNat, d) else (n, d * 10 ^ (-k).toNat)
  let mut m := (2 * num + den) / (2 * den)
  if m ≥ 10 ^ sig then
    m := m / 10
    e := e + 1
  let s := toString m
  let strip (t : String) : String := String.ofList (t.toList.reverse.dropWhile (· == '0')).reverse
  let body :=
    if -5 ≤ e ∧ e < sig then
      if e ≥ 0 then
        let ip := String.ofList (s.toList.take (e.toNat + 1))
        let fp := strip (String.ofList (s.toList.drop (e.toNat + 1)))
        if fp.isEmpty then ip else ip ++ "." ++ fp
      else
        "0." ++ "".pushn '0' ((-e).toNat - 1) ++ strip s
    else
      let fp := strip (String.ofList (s.toList.drop 1))
      String.ofList (s.toList.take 1) ++ (if fp.isEmpty then "" else "." ++ fp) ++ "e" ++
        (if e < 0 then "-" else "") ++ toString e.natAbs
  return (if neg then "-" else "") ++ body

/-- A double as a decimal with `sig` significant digits (17 by default: reads back exactly);
`NaN`, `inf`, `-inf`, `-0` for the special values. -/
def fmtFloat (f : Float) (sig : Nat := 17) : String :=
  if f.isNaN then "NaN"
  else if f.isInf then (if f < 0 then "-inf" else "inf")
  else match Spec.bitsToRat? f.toBits with
    | some q => if q == 0 && f.toBits ≥ 0x8000000000000000 then "-0" else fmtRat q sig
    | none => "NaN"

/-- `[lo, hi]` with 17 significant digits per endpoint. -/
protected def toString (X : Interval64) : String := s!"[{fmtFloat X.lo}, {fmtFloat X.hi}]"

/-- Exact endpoints as rationals (`none` for an infinite or NaN endpoint). -/
def exact (X : Interval64) : Option Rat × Option Rat :=
  (Spec.bitsToRat? X.lo.toBits, Spec.bitsToRat? X.hi.toBits)

/-- Exact width `hi - lo` as a rational (`none` if an endpoint is infinite or NaN). -/
def widthRat (X : Interval64) : Option Rat :=
  match X.exact with
  | (some l, some h) => some (h - l)
  | _ => none

instance (priority := high) : Repr Interval64 := ⟨fun X _ => .text X.toString⟩
instance : ToString Interval64 := ⟨Interval64.toString⟩

end Interval64
