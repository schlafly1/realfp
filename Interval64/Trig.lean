/-
Directed-rounding `sin` and `cos` (binary64).

Logical model (Mathlib-free), as for `exp`/`log` (`Interval64.Transc`):

* `trigSmall r n` : enclosures of `sin r`, `cos r` for `|r| ≤ 1` from the
  real / imaginary parts of the Taylor sum of `exp (r i)` with the
  `Complex.exp_bound` remainder.
* `piCheck P` : a rational enclosure `[a, b] ∋ π`. A Machin-formula
  approximation (unverified) is *certified* by `cos (a/4)` and `cos (b/4)`
  bounds (`cos (a/2) = 2 cos² (a/4) - 1 > 0 ⇒ a < π`, and `< 0 ⇒ b > π`). If
  the certificate fails the result is `[3, 3.15]`. `piBounds` caches the
  values for the Ziv precisions (lazy `Thunk`s).
* `trigBounds q p` : argument reduction `q = r + k·π/2` with `r` enclosed
  using the π enclosure; `sin`/`cos` at a rational `r₀ ≤ r` plus the
  Lipschitz term `r - r₀`; quadrant by `k mod 4`. `|q| ≤ 3/4` is evaluated
  directly (exact, relative precision for tiny `q`).
* `avoids a b c` : certifies that `[a, b]` contains no point `(4n + c)·π/2`
  (`c = 3`: minima of `sin`, `1`: maxima of `sin`, `2`/`0`: minima / maxima of
  `cos`); used by the interval versions, which return `-1` / `1` whenever the
  certificate fails.

Runtime: CORE-MATH `cr_sin` / `cr_cos` under RD / RU (`c/iv64_transc.c`).
-/
import Interval64.Transc

namespace Interval64.Trig

open Interval64.Spec Interval64.Transc
open Float.Model Float.Model.UnpackedFloat

/-- `∑_{m<n} (r i)^m / m!` as `(real part, imaginary part)`. -/
def cisTaylor (r : Rat) : Nat → Rat × Rat
  | 0 => (0, 0)
  | n + 1 =>
    let s := cisTaylor r n
    let t := r ^ n / (fact n : Rat)
    if n % 4 = 0 then (s.1 + t, s.2)
    else if n % 4 = 1 then (s.1, s.2 + t)
    else if n % 4 = 2 then (s.1 - t, s.2)
    else (s.1, s.2 - t)

/-- Bounds `(sinLo, sinHi, cosLo, cosHi)`. -/
structure TB where
  sl : Rat
  sh : Rat
  cl : Rat
  ch : Rat

/-- Enclosures of `sin r`, `cos r` for `|r| ≤ 1`, `n ≥ 1`. -/
def trigSmall (r : Rat) (n : Nat) : TB :=
  let c := cisTaylor r n
  let e := expErr (ratAbs' r) n
  ⟨c.2 - e, c.2 + e, c.1 - e, c.1 + e⟩

def trigTerms (p : Nat) : Nat := p / 4 + 10

/-! ## π -/

/-- `∑_{j<n} (-1)^j / ((2j+1) m^(2j+1))` (≈ `atan (1/m)`; not trusted). -/
def atanInvSum (m : Nat) : Nat → Rat
  | 0 => 0
  | j + 1 => atanInvSum m j +
      (if j % 2 = 0 then 1 else -1) / (((2 * j + 1 : Nat) : Rat) * (m : Rat) ^ (2 * j + 1))

/-- Machin: `π ≈ 16 atan(1/5) - 4 atan(1/239)` (only a candidate). -/
def machinPi (P : Nat) : Rat := 16 * atanInvSum 5 (P / 4 + 4) - 4 * atanInvSum 239 (P / 4 + 4)

/-- Certified enclosure of `π` (width about `2^(1-P)`), or `[3, 3.15]`. -/
def piCheck (P : Nat) : Rat × Rat :=
  let c := machinPi P
  let a := floorP (c - 1 / 2 ^ P) P
  let b := ceilP (c + 1 / 2 ^ P) P
  let n := P / 5 + 20
  let ca := (trigSmall (a / 4) n).cl
  let cb := (trigSmall (b / 4) n).ch
  if 3 ≤ a ∧ a ≤ b ∧ b ≤ 63 / 20 ∧ 0 < ca ∧ 1 < 2 * ca * ca ∧ 0 ≤ cb ∧ 2 * cb * cb < 1 then (a, b)
  else (3, 63 / 20)

/-- Working π precision for Ziv precision `p` (`big`: arguments `≥ 2^30`). -/
def piPrec (p : Nat) (big : Bool) : Nat := p + (if big then 1104 else 110)

/-- Lazily computed `piCheck` for the Ziv precisions `128 * 2^k`, `k < 5`. -/
def piCache : Array (Thunk (Rat × Rat)) :=
  (List.range 10).toArray.map fun i =>
    Thunk.mk fun _ => piCheck (piPrec (zivPrec (i / 2)) (i % 2 == 1))

def piIndex (p : Nat) (big : Bool) : Nat := 2 * Nat.log2 (p / 128) + (if big then 1 else 0)

/-- A certified enclosure of `π` (cached when `p` is a Ziv precision). -/
def piBounds (p : Nat) (big : Bool) : Rat × Rat :=
  if p = zivPrec (Nat.log2 (p / 128)) then
    match piCache[piIndex p big]? with
    | some t => t.get
    | none => piCheck (piPrec p big)
  else piCheck (piPrec p big)

/-! ## Argument reduction -/

/-- Quadrant selection: bounds of `f (r + j π/2)` from bounds of `sin r`, `cos r`
    (`sin`: `[s, c, -s, -c]`, `cos`: `[c, -s, -c, s]`) widened by `w`. -/
def quadSin (t : TB) (j : Int) (w : Rat) : Rat × Rat :=
  if j = 0 then (t.sl - w, t.sh + w)
  else if j = 1 then (t.cl - w, t.ch + w)
  else if j = 2 then (-t.sh - w, -t.sl + w)
  else (-t.ch - w, -t.cl + w)

def quadCos (t : TB) (j : Int) (w : Rat) : Rat × Rat :=
  if j = 0 then (t.cl - w, t.ch + w)
  else if j = 1 then (-t.sh - w, -t.sl + w)
  else if j = 2 then (-t.ch - w, -t.cl + w)
  else (t.sl - w, t.sh + w)

/-- `(sin bounds, cos bounds)` for a rational `q` at working precision `p`. -/
def trigBounds (q : Rat) (p : Nat) : (Rat × Rat) × (Rat × Rat) :=
  let n := trigTerms p
  if ratAbs' q ≤ 3 / 4 then
    let t := trigSmall q n
    ((t.sl, t.sh), (t.cl, t.ch))
  else
    let pb := piBounds p (!decide (ratAbs' q < 2 ^ 30))
    let k : Int := (q * 4 / (pb.1 + pb.2) + 1 / 2).floor
    let rl := if 0 ≤ k then q - k * pb.2 / 2 else q - k * pb.1 / 2
    let rh := if 0 ≤ k then q - k * pb.1 / 2 else q - k * pb.2 / 2
    let r0 := floorP rl (p + 40)
    let w := rh - r0
    if ratAbs' r0 ≤ 1 then
      let t := trigSmall r0 n
      (quadSin t (k % 4) w, quadCos t (k % 4) w)
    else ((-1, 1), (-1, 1))

/-! ## Bit-level specifications -/

def sinRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if up then zivUp (fun p => (trigBounds q p).1) else zivDown (fun p => (trigBounds q p).1)

def cosRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if up then zivUp (fun p => (trigBounds q p).2) else zivDown (fun p => (trigBounds q p).2)

/-- `sin` on bits with diagnostics: NaN, ±∞ → NaN; `sin ±0 = ±0`. -/
def sinBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (qNaN, 0, true)
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => sinRat q up
    | none => (qNaN, 0, true)

/-- `cos` on bits with diagnostics: NaN, ±∞ → NaN; `cos ±0 = 1`. -/
def cosBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (qNaN, 0, true)
  | .zero _ => (if up then ofRatUp 1 else ofRatDown 1, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => cosRat q up
    | none => (qNaN, 0, true)

def sinDownBits (b : UInt64) : UInt64 := (sinBitsD b false).1
def sinUpBits (b : UInt64) : UInt64 := (sinBitsD b true).1
def cosDownBits (b : UInt64) : UInt64 := (cosBitsD b false).1
def cosUpBits (b : UInt64) : UInt64 := (cosBitsD b true).1

/-! ## Extremum certificates for intervals -/

/-- Bounds of `m · π/2`. -/
def halfPiMul (m : Int) (pb : Rat × Rat) : Rat × Rat :=
  if 0 ≤ m then (m * pb.1 / 2, m * pb.2 / 2) else (m * pb.2 / 2, m * pb.1 / 2)

/-- `true` only if `[a, b] ⊆ [(4n+c)π/2, (4n+c+4)π/2]` for some integer `n`
    (so `[a, b]` contains no point `≡ c·π/2 (mod 2π)` in its interior). -/
def avoids (a b : Rat) (c : Int) : Bool :=
  let pb := piBounds 128 (!decide (ratAbs' a < 2 ^ 30 ∧ ratAbs' b < 2 ^ 30))
  let n : Int := ((a * 4 / (pb.1 + pb.2) - c) / 4).floor
  decide ((halfPiMul (4 * n + c) pb).2 ≤ a ∧ b ≤ (halfPiMul (4 * n + c + 4) pb).1)

end Interval64.Trig

namespace Interval64.Directed

/-! ## Float-level directed sin / cos -/

def sinDownSpec (a : Float) : Float := Float.ofBits (Trig.sinDownBits a.toBits)
def sinUpSpec   (a : Float) : Float := Float.ofBits (Trig.sinUpBits a.toBits)
def cosDownSpec (a : Float) : Float := Float.ofBits (Trig.cosDownBits a.toBits)
def cosUpSpec   (a : Float) : Float := Float.ofBits (Trig.cosUpBits a.toBits)

@[extern "iv64_dir_sin_down"] opaque sinDownImpl (a : Float) : Float
@[extern "iv64_dir_sin_up"]   opaque sinUpImpl   (a : Float) : Float
@[extern "iv64_dir_cos_down"] opaque cosDownImpl (a : Float) : Float
@[extern "iv64_dir_cos_up"]   opaque cosUpImpl   (a : Float) : Float

@[implemented_by sinDownImpl] def sinDown (a : Float) : Float := sinDownSpec a
@[implemented_by sinUpImpl]   def sinUp   (a : Float) : Float := sinUpSpec a
@[implemented_by cosDownImpl] def cosDown (a : Float) : Float := cosDownSpec a
@[implemented_by cosUpImpl]   def cosUp   (a : Float) : Float := cosUpSpec a

@[extern "iv64_cr_sin"] opaque crSin (a : Float) : Float
@[extern "iv64_cr_cos"] opaque crCos (a : Float) : Float

end Interval64.Directed

namespace Interval64

open Interval64.Directed

def minusOne : Float := Float.ofBits (Spec.ofRatDown (-1))
def plusOne : Float := Float.ofBits (Spec.ofRatUp 1)

/-- Interval `sin`. NaN endpoint → invalid; infinite endpoint → `[-1, 1]`.
    The lower end is `min (sinDown lo) (sinDown hi)` when `[lo, hi]` provably
    contains no minimum point `3π/2 + 2nπ`, else `-1`; similarly the upper end. -/
def sin (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else
    match Spec.bitsToRat? a.lo.toBits, Spec.bitsToRat? a.hi.toBits with
    | some x, some y =>
      ⟨if Trig.avoids x y 3 then fmin (sinDown a.lo) (sinDown a.hi) else minusOne,
       if Trig.avoids x y 1 then fmax (sinUp a.lo) (sinUp a.hi) else plusOne⟩
    | _, _ => ⟨minusOne, plusOne⟩

/-- Interval `cos` (minima at `π + 2nπ`, maxima at `2nπ`). -/
def cos (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else
    match Spec.bitsToRat? a.lo.toBits, Spec.bitsToRat? a.hi.toBits with
    | some x, some y =>
      ⟨if Trig.avoids x y 2 then fmin (cosDown a.lo) (cosDown a.hi) else minusOne,
       if Trig.avoids x y 0 then fmax (cosUp a.lo) (cosUp a.hi) else plusOne⟩
    | _, _ => ⟨minusOne, plusOne⟩

end Interval64
