/-
Directed-rounding `sinh`, `cosh`, `tanh`, `log2`, `log10` (binary64).

Logical model (Mathlib-free), from the `exp` / `log` enclosures of `Interval64.Transc`:
* `sinhBounds q p = ((a - d)/2, (b - c)/2)`, `coshBounds q p = ((a + c)/2, (b + d)/2)` where
  `[a, b] ∋ exp q`, `[c, d] ∋ exp (-q)` (exact Taylor sums for small `|q|`, so the relative
  precision survives the cancellation in `sinh`).
* `tanhBounds`: `sinh / cosh` with the positive `cosh` enclosure; `|q| ≥ 22`: `[1 - 2^-60, 1]`.
* `log2Bounds q p = log q / log 2`, `log10Bounds q p = log q / log 10` (interval quotient of the
  `logBounds` enclosures); exact results `k` for `q = 2^k` / `q = 10^k` are returned exactly.
Runtime: CORE-MATH `cr_sinh`, `cr_cosh`, `cr_tanh`, `cr_log2`, `cr_log10` under RD / RU.
-/
import Interval64.InvTrig

namespace Interval64.Hyp

open Interval64.Spec Interval64.Transc Interval64.InvTrig
open Float.Model Float.Model.UnpackedFloat

/-- Interval quotient `[a, b] / [c, d]` for `0 < c`. -/
def divPos (n d : Rat × Rat) : Rat × Rat :=
  (if 0 ≤ n.1 then n.1 / d.2 else n.1 / d.1, if 0 ≤ n.2 then n.2 / d.1 else n.2 / d.2)

def sinhBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let e := expBounds q p
  let f := expBounds (-q) p
  ((e.1 - f.2) / 2, (e.2 - f.1) / 2)

def coshBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let e := expBounds q p
  let f := expBounds (-q) p
  ((e.1 + f.1) / 2, (e.2 + f.2) / 2)

/-- `tanh q` for `|q| < 22` (`cosh ≥ 1`, so the lower `cosh` bound is clamped to `1`). -/
def tanhBounds (q : Rat) (p : Nat) : Rat × Rat :=
  let s := sinhBounds q p
  let c := coshBounds q p
  divPos s (max c.1 1, c.2)

/-- Overflow threshold: `sinh q ≥ 2^1024` and `cosh q ≥ 2^1024` for `q > 711`. -/
def hypOvf : Rat := 711

/-- Exact `log2`: `some k` if `q = 2^k`. -/
def log2Exact? (q : Rat) : Option Int :=
  if q.num = 1 then
    (if q.den == 2 ^ (Nat.log2 q.den) then some (-(Nat.log2 q.den : Int)) else none)
  else if q.den = 1 ∧ 0 < q.num then
    (if q.num.toNat == 2 ^ (Nat.log2 q.num.toNat) then some (Nat.log2 q.num.toNat : Int) else none)
  else none

/-- Exact `log10`: `some k` if `q = 10^k`, `0 ≤ k ≤ 22` (other powers are not doubles). -/
def log10Exact? (q : Rat) : Option Nat :=
  (List.range 23).find? (fun k => q == (10 : Rat) ^ k)

def ln10Bounds (p : Nat) : Rat × Rat := logBounds 10 p

def log2Bounds (q : Rat) (p : Nat) : Rat × Rat :=
  match log2Exact? q with
  | some k => (k, k)
  | none => divPos (logBounds q p) (ln2Bounds p)

def log10Bounds (q : Rat) (p : Nat) : Rat × Rat :=
  match log10Exact? q with
  | some k => (k, k)
  | none => divPos (logBounds q p) (ln10Bounds p)

/-! ## Bit-level specifications -/

def sinhRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if hypOvf < q then (if up then posInf else ofRatDown expOvfBound, 0, true)
  else if q < -hypOvf then (if up then ofRatUp (-expOvfBound) else negInf, 0, true)
  else rndD (sinhBounds q) up

def coshRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if hypOvf < ratAbs' q then (if up then posInf else ofRatDown expOvfBound, 0, true)
  else rndD (coshBounds q) up

def tanhRat (q : Rat) (up : Bool) : UInt64 × Nat × Bool :=
  if 22 ≤ q then (if up then ofRatUp 1 else ofRatDown (1 - 1 / 2 ^ 60), 0, true)
  else if q ≤ -22 then (if up then ofRatUp (-1 + 1 / 2 ^ 60) else ofRatDown (-1), 0, true)
  else rndD (tanhBounds q) up

def sinhBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (b, 0, true)
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => sinhRat q up
    | none => (qNaN, 0, true)

def coshBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity _ => (posInf, 0, true)
  | .zero _ => (if up then ofRatUp 1 else ofRatDown 1, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => coshRat q up
    | none => (qNaN, 0, true)

def tanhBitsD (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity .positive => (if up then ofRatUp 1 else ofRatDown 1, 0, true)
  | .infinity .negative => (if up then ofRatUp (-1) else ofRatDown (-1), 0, true)
  | .zero _ => (b, 0, true)
  | .finite .. =>
    match bitsToRat? b with
    | some q => tanhRat q up
    | none => (qNaN, 0, true)

/-- `log2` / `log10` (`ten = true`) on bits: NaN or `< 0` → NaN, `±0` → `-∞`, `+∞` → `+∞`. -/
def logBBitsD (ten : Bool) (b : UInt64) (up : Bool) : UInt64 × Nat × Bool :=
  match unpackBits b with
  | .notANumber => (qNaN, 0, true)
  | .infinity .negative => (qNaN, 0, true)
  | .infinity .positive => (posInf, 0, true)
  | .zero _ => (negInf, 0, true)
  | .finite .negative .. => (qNaN, 0, true)
  | .finite .positive .. =>
    match bitsToRat? b with
    | some q => rndD (if ten then log10Bounds q else log2Bounds q) up
    | none => (qNaN, 0, true)

def sinhDownBits (b : UInt64) : UInt64 := (sinhBitsD b false).1
def sinhUpBits (b : UInt64) : UInt64 := (sinhBitsD b true).1
def coshDownBits (b : UInt64) : UInt64 := (coshBitsD b false).1
def coshUpBits (b : UInt64) : UInt64 := (coshBitsD b true).1
def tanhDownBits (b : UInt64) : UInt64 := (tanhBitsD b false).1
def tanhUpBits (b : UInt64) : UInt64 := (tanhBitsD b true).1
def log2DownBits (b : UInt64) : UInt64 := (logBBitsD false b false).1
def log2UpBits (b : UInt64) : UInt64 := (logBBitsD false b true).1
def log10DownBits (b : UInt64) : UInt64 := (logBBitsD true b false).1
def log10UpBits (b : UInt64) : UInt64 := (logBBitsD true b true).1

end Interval64.Hyp

namespace Interval64.Directed

def sinhDownSpec (a : Float) : Float := Float.ofBits (Hyp.sinhDownBits a.toBits)
def sinhUpSpec (a : Float) : Float := Float.ofBits (Hyp.sinhUpBits a.toBits)
def coshDownSpec (a : Float) : Float := Float.ofBits (Hyp.coshDownBits a.toBits)
def coshUpSpec (a : Float) : Float := Float.ofBits (Hyp.coshUpBits a.toBits)
def tanhDownSpec (a : Float) : Float := Float.ofBits (Hyp.tanhDownBits a.toBits)
def tanhUpSpec (a : Float) : Float := Float.ofBits (Hyp.tanhUpBits a.toBits)
def log2DownSpec (a : Float) : Float := Float.ofBits (Hyp.log2DownBits a.toBits)
def log2UpSpec (a : Float) : Float := Float.ofBits (Hyp.log2UpBits a.toBits)
def log10DownSpec (a : Float) : Float := Float.ofBits (Hyp.log10DownBits a.toBits)
def log10UpSpec (a : Float) : Float := Float.ofBits (Hyp.log10UpBits a.toBits)

@[extern "iv64_dir_sinh_down"] opaque sinhDownImpl (a : Float) : Float
@[extern "iv64_dir_sinh_up"] opaque sinhUpImpl (a : Float) : Float
@[extern "iv64_dir_cosh_down"] opaque coshDownImpl (a : Float) : Float
@[extern "iv64_dir_cosh_up"] opaque coshUpImpl (a : Float) : Float
@[extern "iv64_dir_tanh_down"] opaque tanhDownImpl (a : Float) : Float
@[extern "iv64_dir_tanh_up"] opaque tanhUpImpl (a : Float) : Float
@[extern "iv64_dir_log2_down"] opaque log2DownImpl (a : Float) : Float
@[extern "iv64_dir_log2_up"] opaque log2UpImpl (a : Float) : Float
@[extern "iv64_dir_log10_down"] opaque log10DownImpl (a : Float) : Float
@[extern "iv64_dir_log10_up"] opaque log10UpImpl (a : Float) : Float

@[implemented_by sinhDownImpl] def sinhDown (a : Float) : Float := sinhDownSpec a
@[implemented_by sinhUpImpl] def sinhUp (a : Float) : Float := sinhUpSpec a
@[implemented_by coshDownImpl] def coshDown (a : Float) : Float := coshDownSpec a
@[implemented_by coshUpImpl] def coshUp (a : Float) : Float := coshUpSpec a
@[implemented_by tanhDownImpl] def tanhDown (a : Float) : Float := tanhDownSpec a
@[implemented_by tanhUpImpl] def tanhUp (a : Float) : Float := tanhUpSpec a
@[implemented_by log2DownImpl] def log2Down (a : Float) : Float := log2DownSpec a
@[implemented_by log2UpImpl] def log2Up (a : Float) : Float := log2UpSpec a
@[implemented_by log10DownImpl] def log10Down (a : Float) : Float := log10DownSpec a
@[implemented_by log10UpImpl] def log10Up (a : Float) : Float := log10UpSpec a

end Interval64.Directed

namespace Interval64

open Interval64.Directed

def sinh (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid else ⟨sinhDown a.lo, sinhUp a.hi⟩

def tanh (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid else ⟨tanhDown a.lo, tanhUp a.hi⟩

/-- `cosh` (even, minimum `1` at `0`). -/
def cosh (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if decide (0 ≤ a.lo) then ⟨coshDown a.lo, coshUp a.hi⟩
  else if decide (a.hi ≤ 0) then ⟨coshDown a.hi, coshUp a.lo⟩
  else ⟨Float.ofBits (Spec.ofRatDown 1), fmax (coshUp a.lo) (coshUp a.hi)⟩

/-- Lower endpoint of `log2`/`log10`: `-∞` for `lo ≤ 0`. -/
def logBLo (ten : Bool) (x : Float) : Float :=
  match Spec.unpackBits x.toBits with
  | .finite .positive .. => if ten then log10Down x else log2Down x
  | .infinity .positive => Float.ofBits Spec.posInf
  | .notANumber => Float.ofBits Spec.qNaN
  | _ => Float.ofBits Spec.negInf

/-- `log2` / `log10` with the `log` policy. -/
def logB (ten : Bool) (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else
    match Spec.unpackBits a.hi.toBits with
    | .finite .positive .. => ⟨logBLo ten a.lo, if ten then log10Up a.hi else log2Up a.hi⟩
    | .zero _ => ⟨logBLo ten a.lo, Float.ofBits Spec.negInf⟩
    | .infinity .positive => ⟨logBLo ten a.lo, Float.ofBits Spec.posInf⟩
    | _ => invalid

def log2 (a : Interval64) : Interval64 := logB false a
def log10 (a : Interval64) : Interval64 := logB true a

end Interval64
