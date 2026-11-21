/-
Directed-rounding `asin`, `acos` (binary64).

Logical model (Mathlib-free), for `0 < q < 1`:
* tiny `q` (`q ≤ 1/32`, `q² ≲ 2^-p`): `q ≤ asin q ≤ q + q³/5`;
* otherwise an unverified candidate `c ≈ atan (q / √(1-q²))` gives `[a, b]` that is certified by
  the `sin` enclosures: `0 ≤ a ≤ π/2`, `sin a ≤ q` and `b ≤ π/2`, `q ≤ sin b` (failures fall back
  to `0` / `π/2`);
* `asin (-q) = -asin q`, `asin (±1) = ±π/2`; `acos q = π/2 - asin q` (`acos 1 = 0` exactly),
  computed with 64 extra bits.
Runtime: CORE-MATH `cr_asin`, `cr_acos` under RD / RU.
-/
import Interval64.Tan

namespace Interval64.Asin

open Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig
open Float.Model Float.Model.UnpackedFloat

/-- Enclosure of `asin q` for `0 < q < 1`. -/
def asinPos (q : Rat) (p : Nat) : Rat × Rat :=
  let e := relShift q
  let pb := piBounds (p + 20) false
  if q ≤ 1 / 32 ∧ p + 10 ≤ 2 * e then (q, q + q ^ 3 / 5) else
  let P := p + e + 8
  let W := P + 80
  let c := atanCand (q / sqrtD (1 - q * q) W) W
  let a := floorP (c - 1 / 2 ^ P) (P + 2)
  let b := ceilP (c + 1 / 2 ^ P) (P + 2)
  let cp := P + 64
  let lo := if 0 ≤ a ∧ a ≤ pb.1 / 2 ∧ (trigBounds a cp).1.2 ≤ q then a else 0
  let hi := if 0 ≤ b ∧ b ≤ pb.1 / 2 ∧ q ≤ (trigBounds b cp).1.1 then b else pb.2 / 2
  (lo, hi)

/-- Enclosure of `asin q` for `|q| ≤ 1`. -/
def asinBounds (q : Rat) (p : Nat) : Rat × Rat :=
  if q = 0 then (0, 0)
  else if q = 1 then piMul (1 / 2) p
  else if q = -1 then piMul (-1 / 2) p
  else if 0 < q then asinPos q p
  else let s := asinPos (-q) p; (-s.2, -s.1)

/-- Enclosure of `acos q = π/2 - asin q` for `|q| ≤ 1`. -/
def acosBounds (q : Rat) (p : Nat) : Rat × Rat :=
  if q = 1 then (0, 0)
  else
    let s := asinBounds q (p + 64)
    let pb := piBounds (p + 64) false
    (pb.1 / 2 - s.2, pb.2 / 2 - s.1)

/-- `asin` on bits: NaN, ±∞, `|x| > 1` → NaN; `asin ±0 = ±0`. -/
def asinBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (qNaN, 0, true)
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => if ratAbs' q ≤ 1 then rndD (asinBounds q) up else (qNaN, 0, true)
    | none => (qNaN, 0, true)

/-- `acos` on bits: NaN, ±∞, `|x| > 1` → NaN; `acos ±0 = π/2`. -/
def acosBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (qNaN, 0, true)
  | .zero _ => rndD (piMul (1 / 2)) up
  | .finite .. =>
    match bitsToRat? b with
    | some q => if ratAbs' q ≤ 1 then rndD (acosBounds q) up else (qNaN, 0, true)
    | none => (qNaN, 0, true)

def asinDownBits (b : UInt64) : UInt64 := (asinBitsD b false).1
def asinUpBits (b : UInt64) : UInt64 := (asinBitsD b true).1
def acosDownBits (b : UInt64) : UInt64 := (acosBitsD b false).1
def acosUpBits (b : UInt64) : UInt64 := (acosBitsD b true).1

end Interval64.Asin

namespace Interval64.Directed

def asinDownSpec (a : Float) : Float := Float.ofBits (Asin.asinDownBits a.toBits)
def asinUpSpec (a : Float) : Float := Float.ofBits (Asin.asinUpBits a.toBits)
def acosDownSpec (a : Float) : Float := Float.ofBits (Asin.acosDownBits a.toBits)
def acosUpSpec (a : Float) : Float := Float.ofBits (Asin.acosUpBits a.toBits)

@[extern "iv64_dir_asin_down"] opaque asinDownImpl (a : Float) : Float
@[extern "iv64_dir_asin_up"] opaque asinUpImpl (a : Float) : Float
@[extern "iv64_dir_acos_down"] opaque acosDownImpl (a : Float) : Float
@[extern "iv64_dir_acos_up"] opaque acosUpImpl (a : Float) : Float

@[implemented_by asinDownImpl] def asinDown (a : Float) : Float := asinDownSpec a
@[implemented_by asinUpImpl] def asinUp (a : Float) : Float := asinUpSpec a
@[implemented_by acosDownImpl] def acosDown (a : Float) : Float := acosDownSpec a
@[implemented_by acosUpImpl] def acosUp (a : Float) : Float := acosUpSpec a

end Interval64.Directed

namespace Interval64

open Interval64.Directed

/-- Lower bound of `Real.arcsin` at an endpoint (`arcsin` is clamped outside `[-1, 1]`). -/
def asinLo (x : Float) : Float :=
  if decide (x < -1) then negHalfPi.lo else if decide (1 < x) then halfPi.lo else asinDown x
def asinHi (x : Float) : Float :=
  if decide (x < -1) then negHalfPi.hi else if decide (1 < x) then halfPi.hi else asinUp x
/-- Lower bound of `Real.arccos` at an endpoint (`arccos` is clamped outside `[-1, 1]`). -/
def acosLo (x : Float) : Float :=
  if decide (x < -1) then pi.lo else if decide (1 < x) then 0 else acosDown x
def acosHi (x : Float) : Float :=
  if decide (x < -1) then pi.hi else if decide (1 < x) then 0 else acosUp x

/-- Interval `asin` (Mathlib's `Real.arcsin`, increasing, constant `±π/2` outside `[-1, 1]`). -/
def asin (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid else ⟨asinLo a.lo, asinHi a.hi⟩

/-- Interval `acos` (Mathlib's `Real.arccos`, decreasing). -/
def acos (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid else ⟨acosLo a.hi, acosHi a.lo⟩

end Interval64
