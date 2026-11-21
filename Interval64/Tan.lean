/-
Directed-rounding `tan` (binary64).

Logical model (Mathlib-free): `tan q = sin q / cos q` from the `trigBounds` enclosures once the
sign of `cos q` is certified (`tanRes`). If the sign is not certified at precision 2058
(never the case for a binary64 input in practice), the result is `-∞` / `+∞`.
Runtime: CORE-MATH `cr_tan` under RD / RU.
-/
import Interval64.Hyp

namespace Interval64.Tan

open Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig Interval64.Hyp
open Float.Model Float.Model.UnpackedFloat

/-- `tan q` from `trigBounds q p` when `cos q` has a certified sign. -/
def tanRes (q : Rat) (p : Nat) : Option (Rat × Rat) :=
  let t := trigBounds q p
  if 0 < t.2.1 then some (divPos t.1 t.2)
  else if t.2.2 < 0 then some (divPos (-t.1.2, -t.1.1) (-t.2.2, -t.2.1))
  else none

/-- Certified sign of `cos q` at a fixed precision (fallback for `tanBounds`). -/
def tanFallback (q : Rat) : Option (Rat × Rat) :=
  match tanRes q 138 with
  | some b => some b
  | none => tanRes q 2058

def tanBounds (q : Rat) (p : Nat) : Rat × Rat :=
  match tanRes q (p + 10) with
  | some b => b
  | none => (tanFallback q).getD (0, 0)

def tanRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  match tanFallback q with
  | some _ => rndD (tanBounds q) up
  | none => (if up then posInf else negInf, 0, true)

/-- `tan` on bits: NaN, ±∞ → NaN; `tan ±0 = ±0`. -/
def tanBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (qNaN, 0, true)
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => tanRat q up
    | none => (qNaN, 0, true)

def tanDownBits (b : UInt64) : UInt64 := (tanBitsD b false).1
def tanUpBits (b : UInt64) : UInt64 := (tanBitsD b true).1

end Interval64.Tan

namespace Interval64.Directed

def tanDownSpec (a : Float) : Float := Float.ofBits (Tan.tanDownBits a.toBits)
def tanUpSpec (a : Float) : Float := Float.ofBits (Tan.tanUpBits a.toBits)

@[extern "iv64_dir_tan_down"] opaque tanDownImpl (a : Float) : Float
@[extern "iv64_dir_tan_up"] opaque tanUpImpl (a : Float) : Float

/-- Correctly rounded `tan` toward `-∞` (C: CORE-MATH under RD). -/
@[implemented_by tanDownImpl] def tanDown (a : Float) : Float := tanDownSpec a
@[implemented_by tanUpImpl] def tanUp (a : Float) : Float := tanUpSpec a

end Interval64.Directed

namespace Interval64

open Interval64.Directed

/-- Interval `tan`: `[tanDown lo, tanUp hi]` when `[lo, hi]` provably contains no pole
    `π/2 + kπ` (`Trig.avoids` for `c = 1` and `c = 3`), else the whole line. -/
def tan (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else
    match Spec.bitsToRat? a.lo.toBits, Spec.bitsToRat? a.hi.toBits with
    | some x, some y =>
      if Trig.avoids x y 1 && Trig.avoids x y 3 then ⟨tanDown a.lo, tanUp a.hi⟩ else whole
    | _, _ => whole

end Interval64
