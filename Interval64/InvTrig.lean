/-
Directed-rounding `atan`, `atan2` and the constant `π` (binary64).

Logical model (Mathlib-free), as for `sin`/`cos` (`Interval64.Trig`):
* `atanCand q W` : an *unverified* approximation of `atan q`, `0 < q ≤ 1`
  (`k ≤ 12` half-angle steps `t ↦ t / (1 + √(1 + t²))` with rounded square roots,
  then the alternating Taylor series, times `2^k`).
* `atanSmallBounds q p` : the candidate `c` widened to `[a, b]` is *certified*
  with the `trigBounds` enclosures of `sin`/`cos`: `|a|, |b| ≤ 1` (so
  `cos > 0`), `sin a ≤ q·cos a` and `q·cos b ≤ sin b`, i.e. `tan a ≤ q ≤ tan b`,
  hence `a ≤ atan q ≤ b`. If the certificate fails the result is `[-2, 2]`.
  Precision is relative (`e = ⌊log₂ (1/q)⌋` extra bits). For tiny `q`
  (`q² ≤ 2^-(p+10)`) the result is `[q - q³/3, q - q³/3 + q⁵/5]` instead.
* `atanBounds q p` : odd symmetry, and `atan q = π/2 - atan (1/q)` for `q > 1`.
* `atan2Bounds y x p` : `arg (x + y i)` for finite `y ≠ 0`:
  `x > 0`: `atan (y/x)`; `x < 0`: `atan (y/x) ± π`; `x = 0`: `±π/2`.
Runtime: CORE-MATH `cr_atan` / `cr_atan2` under RD / RU (`c/iv64_transc.c`).
Special values follow C99 Annex F (= CORE-MATH): `atan ±∞ = ±π/2`,
`atan2 (±0, x)` is `±0` for `x = +0` or `x > 0` and `±π` for `x = -0` or `x < 0`,
`atan2 (±∞, +∞) = ±π/4`, `atan2 (±∞, -∞) = ±3π/4`, ...
-/
import Interval64.Trig

namespace Interval64.InvTrig

open Interval64.Spec Interval64.Transc Interval64.Trig
open Float.Model Float.Model.UnpackedFloat

/-! ## Candidate (not trusted) -/

/-- `⌊√y · 2^W⌋ / 2^W` for `y ≥ 0`. -/
def sqrtD (y : Rat) (W : Nat) : Rat := (Nat.sqrt (y * 4 ^ W).floor.toNat : Rat) / 2 ^ W

/-- Half-angle steps while `t > 2^-12` (at most `fuel`); returns `(t, k)`. -/
def atanHalve (W : Nat) : Nat → Rat → Nat → Rat × Nat
  | 0, t, k => (t, k)
  | fuel + 1, t, k =>
    if t ≤ 1 / 2 ^ 12 then (t, k)
    else atanHalve W fuel (floorP (t / (1 + sqrtD (1 + t * t) W)) W) (k + 1)

/-- `∑_{j<m} (-1)^j t^(2j+1) / (2j+1)`, each term rounded to `2^-W`. -/
def atanSeries (t : Rat) (W : Nat) : Nat → Rat
  | 0 => 0
  | j + 1 => atanSeries t W j +
      floorP ((if j % 2 = 0 then 1 else -1) * t ^ (2 * j + 1) / ((2 * j + 1 : Nat) : Rat)) W

def atanCand (q : Rat) (W : Nat) : Rat :=
  let r := atanHalve W 12 q 0
  2 ^ r.2 * atanSeries r.1 W (W / 24 + 2)

/-! ## Certified enclosures -/

/-- `⌊log₂ (1/q)⌋` for `0 < q ≤ 1` (extra bits for relative precision). -/
def relShift (q : Rat) : Nat := Nat.log2 (q.den / q.num.toNat)

/-- Precision for the `sin`/`cos` certificate (few Taylor terms suffice for tiny `q`). -/
def certPrec (P e : Nat) : Nat := if P ≤ 8 * e then 0 else P + 10

/-- `true` if `[a, b] ∋ atan q` is certified by `trigBounds` (`0 ≤ q`). -/
def atanCheck (q a b : Rat) (p : Nat) : Bool :=
  let ta := trigBounds a p
  let tb := trigBounds b p
  decide (-1 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ ta.1.2 ≤ q * ta.2.1 ∧ q * tb.2.2 ≤ tb.1.1)

/-- Enclosure of `atan q` for `0 < q ≤ 1` (else / on failure `[-2, 2]`). -/
def atanSmallBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let e := relShift q
  if p + 10 ≤ 2 * e then (q - q ^ 3 / 3, q - q ^ 3 / 3 + q ^ 5 / 5) else
  let P := p + e + 8
  let c := atanCand q (P + 20)
  let a := floorP (c - 1 / 2 ^ P) (P + 2)
  let b := ceilP (c + 1 / 2 ^ P) (P + 2)
  if atanCheck q a b (certPrec P e) then (a, b) else (-2, 2)

/-- Enclosure of `atan q` for any rational `q`. -/
def atanBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let r := ratAbs' q
  let pos : Rat × Rat :=
    if r = 0 then (0, 0)
    else if r ≤ 1 then atanSmallBounds r p
    else
      let s := atanSmallBounds (1 / r) p
      let pb := piBounds p false
      (pb.1 / 2 - s.2, pb.2 / 2 - s.1)
  if q < 0 then (-pos.2, -pos.1) else pos

/-- Enclosure of `c · π` (`c` rational). -/
def piMul (c : Rat) (p : Nat) : Rat × Rat :=
  let pb := piBounds p false
  if 0 ≤ c then (c * pb.1, c * pb.2) else (c * pb.2, c * pb.1)

/-- Enclosure of `arg (x + y i)` for rationals `y ≠ 0`, any `x`. -/
def atan2Bounds (y x : Rat) (p : Nat) : Rat × Rat :=
  if x = 0 then piMul (if 0 < y then 1 / 2 else -1 / 2) p
  else
    let t := atanBounds (y / x) p
    if 0 < x then t
    else
      let s := piMul (if 0 < y then 1 else -1) p
      (t.1 + s.1, t.2 + s.2)

/-! ## Bit-level specifications -/

def rndD (f : Nat → Rat × Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if up then zivUp f else zivDown f

/-- `atan` on bits with diagnostics. -/
def atanBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity .positive => rndD (piMul (1 / 2)) up
  | .infinity .negative => rndD (piMul (-1 / 2)) up
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => rndD (atanBounds q) up
    | none => (qNaN, 0, true)

/-- `±1` for the sign of an unpacked float. -/
def sgnQ : Sign → Rat
  | .positive => 1
  | .negative => -1

/-- Bits of a signed zero. -/
def zeroBits : Sign → UInt64
  | .positive => 0
  | .negative => 0x8000000000000000

def isNeg : Sign → Bool
  | .positive => false
  | .negative => true

/-- `atan2 y x` on bits with diagnostics (C argument order). -/
def atan2BitsD (y x : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits y, unpackBits x with
  | .notANumber, _ => (qNaN, 0, true)
  | _, .notANumber => (qNaN, 0, true)
  | .zero sy, .zero sx => if isNeg sx then rndD (piMul (sgnQ sy)) up else (zeroBits sy, 0, true)
  | .zero sy, .infinity sx => if isNeg sx then rndD (piMul (sgnQ sy)) up else (zeroBits sy, 0, true)
  | .zero sy, .finite sx .. => if isNeg sx then rndD (piMul (sgnQ sy)) up else (zeroBits sy, 0, true)
  | .infinity sy, .infinity sx =>
    rndD (piMul (sgnQ sy * (if isNeg sx then 3 / 4 else 1 / 4))) up
  | .infinity sy, _ => rndD (piMul (sgnQ sy / 2)) up
  | .finite sy .., .zero _ => rndD (piMul (sgnQ sy / 2)) up
  | .finite sy .., .infinity sx => if isNeg sx then rndD (piMul (sgnQ sy)) up else (zeroBits sy, 0, true)
  | .finite .., .finite .. =>
    match bitsToRat? y, bitsToRat? x with
    | some qy, some qx => rndD (atan2Bounds qy qx) up
    | _, _ => (qNaN, 0, true)

def atanDownBits (b : UInt64) : UInt64 := (atanBitsD b false).1
def atanUpBits (b : UInt64) : UInt64 := (atanBitsD b true).1
def atan2DownBits (y x : UInt64) : UInt64 := (atan2BitsD y x false).1
def atan2UpBits (y x : UInt64) : UInt64 := (atan2BitsD y x true).1

/-- `π` rounded down / up. -/
def piDownBits : UInt64 := ofRatDown (piBounds 128 false).1
def piUpBits : UInt64 := ofRatUp (piBounds 128 false).2
/-- `π/2` rounded down / up. -/
def halfPiDownBits : UInt64 := ofRatDown ((piBounds 128 false).1 / 2)
def halfPiUpBits : UInt64 := ofRatUp ((piBounds 128 false).2 / 2)
/-- `-π` rounded down, `-π/2` rounded down / up. -/
def negPiDownBits : UInt64 := ofRatDown (-(piBounds 128 false).2)
def negHalfPiDownBits : UInt64 := ofRatDown (-(piBounds 128 false).2 / 2)
def negHalfPiUpBits : UInt64 := ofRatUp (-(piBounds 128 false).1 / 2)

end Interval64.InvTrig

namespace Interval64.Directed

/-! ## Float-level directed atan / atan2 -/

def atanDownSpec (a : Float) : Float := Float.ofBits (InvTrig.atanDownBits a.toBits)
def atanUpSpec   (a : Float) : Float := Float.ofBits (InvTrig.atanUpBits a.toBits)
def atan2DownSpec (y x : Float) : Float := Float.ofBits (InvTrig.atan2DownBits y.toBits x.toBits)
def atan2UpSpec   (y x : Float) : Float := Float.ofBits (InvTrig.atan2UpBits y.toBits x.toBits)

@[extern "iv64_dir_atan_down"] opaque atanDownImpl (a : Float) : Float
@[extern "iv64_dir_atan_up"]   opaque atanUpImpl   (a : Float) : Float
@[extern "iv64_dir_atan2_down"] opaque atan2DownImpl (y x : Float) : Float
@[extern "iv64_dir_atan2_up"]   opaque atan2UpImpl   (y x : Float) : Float

/-- Correctly rounded `atan` toward `-∞` (C: CORE-MATH under RD). -/
@[implemented_by atanDownImpl] def atanDown (a : Float) : Float := atanDownSpec a
@[implemented_by atanUpImpl]   def atanUp   (a : Float) : Float := atanUpSpec a
/-- Correctly rounded `atan2 y x` toward `-∞` (C: CORE-MATH under RD). -/
@[implemented_by atan2DownImpl] def atan2Down (y x : Float) : Float := atan2DownSpec y x
@[implemented_by atan2UpImpl]   def atan2Up   (y x : Float) : Float := atan2UpSpec y x

@[extern "iv64_cr_atan"] opaque crAtan (a : Float) : Float
@[extern "iv64_cr_atan2"] opaque crAtan2 (y x : Float) : Float

end Interval64.Directed

namespace Interval64

open Interval64.Directed

/-- `[π↓, π↑]`. -/
def pi : Interval64 := ⟨Float.ofBits InvTrig.piDownBits, Float.ofBits InvTrig.piUpBits⟩

/-- `atan` is increasing: `[atanDown lo, atanUp hi]`; invalid if an endpoint is NaN. -/
def atan (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else ⟨atanDown a.lo, atanUp a.hi⟩

/-- `[-π↓, π↑]` hull of the range of `arg`. -/
def argHull : Interval64 := ⟨Float.ofBits InvTrig.negPiDownBits, Float.ofBits InvTrig.piUpBits⟩
def halfPi : Interval64 := ⟨Float.ofBits InvTrig.halfPiDownBits, Float.ofBits InvTrig.halfPiUpBits⟩
def negHalfPi : Interval64 :=
  ⟨Float.ofBits InvTrig.negHalfPiDownBits, Float.ofBits InvTrig.negHalfPiUpBits⟩

/-- Interval `atan2 Y X` (C argument order), enclosing `Complex.arg (x + y i)` for
    `x ∈ X`, `y ∈ Y`:
    * `X > 0`: `atan (Y / X)`;
    * `Y > 0`: `π/2 - atan (X / Y)`; `Y < 0`: `-π/2 - atan (X / Y)`;
    * otherwise (the box meets the branch cut `y = 0, x ≤ 0` or the origin): `[-π, π]`.
    NaN endpoint → invalid. -/
def atan2 (y x : Interval64) : Interval64 :=
  if anyNan y x then invalid
  else if decide (x.lo > 0) then atan (div y x)
  else if decide (y.lo > 0) then sub halfPi (atan (div x y))
  else if decide (y.hi < 0) then sub negHalfPi (atan (div x y))
  else argHull

end Interval64
