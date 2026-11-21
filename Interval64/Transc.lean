/-
Directed-rounding `exp` and `log` (binary64).

Logical model (kernel-visible, Mathlib-free): computable rational enclosures
with explicit error terms, refined by a Ziv loop.

* `expBounds q p` / `logBounds q p` : rationals `lo ≤ f q ≤ hi`
  (proved over `ℝ` in `RealFPMathlib/Transc.lean`); `p` is a working
  precision in bits that only affects tightness, never validity.
* `ziv f rnd pick 0 fuel` : evaluates `f` at precisions `128 * 2^k`
  (`k < fuel`) and stops as soon as `rnd lo = rnd hi`, which is then the
  correctly rounded result. If the fuel runs out it returns `rnd lo` (down)
  or `rnd hi` (up) of the last enclosure: still a valid bound, possibly one
  ulp loose. The step counter / convergence flag are exposed for testing.

Runtime: CORE-MATH (`c/coremath`, MIT) run under RD / RU hardware rounding
(`c/iv64_transc.c`), attached with `@[implemented_by]`.
-/
import Interval64.OfRat
import Interval64.Interval

namespace Interval64.Transc

open Interval64.Spec
open Float.Model Float.Model.UnpackedFloat

/-! ## Rational helpers -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `q` rounded down to a multiple of `2^-p`. -/
def floorP (q : Rat) (p : Nat) : Rat := ((q * 2 ^ p).floor : Rat) / 2 ^ p

/-- `q` rounded up to a multiple of `2^-p`. -/
def ceilP (q : Rat) (p : Nat) : Rat := -floorP (-q) p

def ratAbs' (q : Rat) : Rat := if q < 0 then -q else q

/-! ## exp -/

/-- `∑_{m<n} r^m / m!`. -/
def expTaylor (r : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => expTaylor r n + r ^ n / (fact n : Rat)

/-- Remainder bound of `Real.exp_bound` for `|r| ≤ 1`, `0 < n`. -/
def expErr (r : Rat) (n : Nat) : Rat := r ^ n * (((n + 1 : Nat) : Rat) / ((fact n : Rat) * (n : Rat)))

/-- Enclosure of `exp r` for `0 ≤ r ≤ 1` (`n ≥ 1` Taylor terms). -/
def expSmall (r : Rat) (n : Nat) : Rat × Rat :=
  (expTaylor r n - expErr r n, expTaylor r n + expErr r n)

/-- Square an enclosure `s` times, rounding outward to `2^-p`. -/
def sqIter (p : Nat) : Nat → Rat × Rat → Rat × Rat
  | 0, b => b
  | s + 1, b =>
    let l := if b.1 < 0 then 0 else b.1
    sqIter p s (floorP (l * l) p, ceilP (b.2 * b.2) p)

/-- Number of Taylor terms (only affects tightness). -/
def expTerms (p : Nat) : Nat := p / 20 + 3

/-- Halving count `s` with `t / 2^s ≤ 2^-20` (for `t ≥ 0`). -/
def expShift (t : Rat) : Nat := Nat.log2 t.num.toNat + 21

/-- Enclosure of `exp t` for `t ≥ 0`. -/
def expPosBounds (t : Rat) (p : Nat) : Rat × Rat :=
  let n := expTerms p
  if t < 1 / 2 ^ 20 then expSmall t n
  else
    let s := expShift t
    sqIter p s (expSmall (t / 2 ^ s) n)

/-- Enclosure of `exp q` for any rational `q`. -/
def expBounds (q : Rat) (p : Nat) : Rat × Rat :=
  if 0 ≤ q then expPosBounds q p
  else
    let b := expPosBounds (-q) p
    (if 0 < b.2 then 1 / b.2 else 0, if 0 < b.1 then 1 / b.1 else 1)

/-! ## log -/

/-- `∑_{i<n} y^(i+1) / (i+1)` (so `log (1 - y) ≈ -logSeries y n`). -/
def logSeries (y : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => logSeries y n + y ^ (n + 1) / ((n + 1 : Nat) : Rat)

/-- Remainder bound of `Real.abs_log_sub_add_sum_range_le`. -/
def logErr (y : Rat) (n : Nat) : Rat := ratAbs' y ^ (n + 1) / (1 - ratAbs' y)

/-- Enclosure of `log 2 = -log (1 - 1/2)`. -/
def ln2Bounds (p : Nat) : Rat × Rat :=
  let n := p + 2
  let A := logSeries (1 / 2) n
  (A - logErr (1 / 2) n, A + logErr (1 / 2) n)

/-- Exponent `e` with `q / 2^e ∈ [3/4, 3/2)` (for `q > 0`; only affects tightness). -/
def logRedExp (q : Rat) : Int :=
  let e0 : Int := (Nat.log2 q.num.toNat : Int) - (Nat.log2 q.den : Int)
  let m0 := q / pow2 e0
  if 3 / 2 ≤ m0 then e0 + 1 else if m0 < 3 / 4 then e0 - 1 else e0

/-- Number of series terms for `|y| ≤ 2^-b` (only affects tightness). -/
def logTerms (y : Rat) (p : Nat) : Nat :=
  let ay := ratAbs' y
  let b := if ay = 0 then p else max 1 (Nat.log2 (1 / ay).floor.toNat)
  p / b + 2

/-- Enclosure of `log q` for `q > 0`. -/
def logBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let e := logRedExp q
  let y := 1 - q / pow2 e
  if ratAbs' y ≤ 1 / 2 then
    let n := logTerms y p
    let B := logSeries y n
    let E := logErr y n
    let L := ln2Bounds p
    let eL : Rat × Rat := if 0 ≤ e then ((e : Rat) * L.1, (e : Rat) * L.2)
      else ((e : Rat) * L.2, (e : Rat) * L.1)
    (eL.1 + (-B - E), eL.2 + (-B + E))
  else (1 - 1 / q, q - 1)

/-! ## Ziv loop -/

def zivPrec (k : Nat) : Nat := 128 * 2 ^ k

/-- Default fuel: precisions 128, 256, 512, 1024, 2048. -/
def zivFuel : Nat := 5

/-- Returns `(result, last step index, converged)`. -/
def ziv (f : Nat → Rat × Rat) (rnd : Rat → UInt64) (pick : Rat × Rat → Rat) (k : Nat) :
    Nat → UInt64 × Nat × Bool
  | 0 => (rnd (pick (f (zivPrec k))), k, false)
  | fuel + 1 =>
    let b := f (zivPrec k)
    if rnd b.1 == rnd b.2 then (rnd (pick b), k, true)
    else if fuel = 0 then (rnd (pick b), k, false)
    else ziv f rnd pick (k + 1) fuel

def zivDown (f : Nat → Rat × Rat) : UInt64 × Nat × Bool := ziv f ofRatDown Prod.fst 0 zivFuel
def zivUp (f : Nat → Rat × Rat) : UInt64 × Nat × Bool := ziv f ofRatUp Prod.snd 0 zivFuel

/-! ## Bit-level specifications -/

/- Finite constant results are written as `ofRatDown c` / `ofRatUp c` so that
   their correctness follows from `ofRatDown_isRoundDown`; their bit patterns
   (`+0`, `1`, MaxFinite `0x7FEFFFFFFFFFFFFF`, min subnormal `0x1`) are
   checked by the test executable. -/

/-- `2^1024 > MaxFinite`; `exp q ≥ 2^1024` for `q > 710`. -/
def expOvfBound : Rat := 2 ^ 1024
/-- `2^-1075 < min subnormal`; `exp q ≤ 2^-1075` for `q < -746`. -/
def expUnfBound : Rat := 1 / 2 ^ 1075

/-- `exp` of a finite rational, rounded down (`up = false`) or up. -/
def expRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if 710 < q then (if up then posInf else ofRatDown expOvfBound, 0, true)
  else if q < -746 then (if up then ofRatUp expUnfBound else ofRatDown 0, 0, true)
  else if up then zivUp (expBounds q) else zivDown (expBounds q)

/-- `exp` on bits with diagnostics. -/
def expBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity .negative => (if up then ofRatUp 0 else ofRatDown 0, 0, true)
  | .infinity .positive => (posInf, 0, true)
  | .zero _ => (if up then ofRatUp 1 else ofRatDown 1, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => expRat q up
    | none => (qNaN, 0, true)

/-- `log` of a finite rational, rounded down (`up = false`) or up. -/
def logRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if q < 0 then (qNaN, 0, true)
  else if q = 0 then (negInf, 0, true)
  else if q = 1 then (if up then ofRatUp 0 else ofRatDown 0, 0, true)
  else if up then zivUp (logBounds q) else zivDown (logBounds q)

def logBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity .negative => (qNaN, 0, true)
  | .infinity .positive => (posInf, 0, true)
  | .zero _ => (negInf, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => logRat q up
    | none => (qNaN, 0, true)

def expDownBits (b : UInt64) : UInt64 := (expBitsD b false).1
def expUpBits (b : UInt64) : UInt64 := (expBitsD b true).1
def logDownBits (b : UInt64) : UInt64 := (logBitsD b false).1
def logUpBits (b : UInt64) : UInt64 := (logBitsD b true).1

end Interval64.Transc

namespace Interval64.Directed

/-! ## Float-level directed exp / log -/

def expDownSpec (a : Float) : Float := Float.ofBits (Transc.expDownBits a.toBits)
def expUpSpec   (a : Float) : Float := Float.ofBits (Transc.expUpBits a.toBits)
def logDownSpec (a : Float) : Float := Float.ofBits (Transc.logDownBits a.toBits)
def logUpSpec   (a : Float) : Float := Float.ofBits (Transc.logUpBits a.toBits)

@[extern "iv64_dir_exp_down"] opaque expDownImpl (a : Float) : Float
@[extern "iv64_dir_exp_up"]   opaque expUpImpl   (a : Float) : Float
@[extern "iv64_dir_log_down"] opaque logDownImpl (a : Float) : Float
@[extern "iv64_dir_log_up"]   opaque logUpImpl   (a : Float) : Float

/-- Correctly rounded `exp` toward `-∞` (C: CORE-MATH under RD). -/
@[implemented_by expDownImpl] def expDown (a : Float) : Float := expDownSpec a
@[implemented_by expUpImpl]   def expUp   (a : Float) : Float := expUpSpec a
@[implemented_by logDownImpl] def logDown (a : Float) : Float := logDownSpec a
@[implemented_by logUpImpl]   def logUp   (a : Float) : Float := logUpSpec a

/-- Round-to-nearest CORE-MATH (benchmark reference only; not a model). -/
@[extern "iv64_cr_exp"] opaque crExp (a : Float) : Float
@[extern "iv64_cr_log"] opaque crLog (a : Float) : Float

end Interval64.Directed

namespace Interval64

open Interval64.Directed

/-- `exp` is increasing: `[expDown lo, expUp hi]`; invalid if an endpoint is NaN. -/
def exp (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else ⟨expDown a.lo, expUp a.hi⟩

/-- Lower endpoint of `log`: `logDown lo` for `lo > 0`, `-∞` for `lo ≤ 0`. -/
def logLo (x : Float) : Float :=
  match Spec.unpackBits x.toBits with
  | .finite .positive .. => logDown x
  | .infinity .positive => Float.ofBits Spec.posInf
  | .notANumber => Float.ofBits Spec.qNaN
  | _ => Float.ofBits Spec.negInf

/-- `log` is increasing on `(0, ∞)`. Policy (as for `sqrt`): if `hi < 0` the
    result is invalid; a lower end `≤ 0` gives `-∞`; `log ±0 = -∞`. -/
def log (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else
    match Spec.unpackBits a.hi.toBits with
    | .finite .positive .. => ⟨logLo a.lo, logUp a.hi⟩
    | .zero _ => ⟨logLo a.lo, Float.ofBits Spec.negInf⟩
    | .infinity .positive => ⟨logLo a.lo, Float.ofBits Spec.posInf⟩
    | _ => invalid

end Interval64
