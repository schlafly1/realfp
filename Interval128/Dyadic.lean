/-
Kernel fast path for `(precision := 128)`: intervals with exact dyadic endpoints `m · 2^e`
(`m e : Int`), rounded outward to `prec = 128` significant bits after every operation.

Everything here is `Nat`/`Int` arithmetic that Lean's kernel evaluates with GMP
(`Nat.add/sub/mul/div/mod/pow/log2/shiftLeft`, `Int` by cases on `Nat`), so
`decide +kernel` runs these definitions one to two orders of magnitude faster than the
`Float`-based `Interval128` specification. Compiled code (the certificate search and
`native_decide`) runs the same definitions.

Nothing is trusted: every guess (bit lengths, square roots) is either irrelevant to soundness
or checked inside the definition. Soundness over `ℝ`: `RealFPMathlib/I128Dyadic.lean`.

An endpoint `none` is unbounded (`-∞` below, `+∞` above).
-/
import Interval128.Reflect
import Interval64.Kernel.Deriv

namespace Interval128.Dy

open Interval64 Interval64.KF

/-- The dyadic number `m · 2^e`. -/
structure Dy where
  m : Int
  e : Int
  deriving Repr, Inhabited, DecidableEq

/-- Significant bits kept after rounding. -/
def prec : Nat := 128

def zero : Dy := ⟨0, 0⟩

/-- Bit length of `n` (`0` for `0`). -/
def bitlen (n : Nat) : Nat := bif Nat.beq n 0 then 0 else Nat.log2 n + 1

/-- Right shift that brings `|m|` to at most `prec` bits (any value is sound). -/
def shiftOf (m : Int) : Nat := bitlen m.natAbs - prec

/-- `m · 2^e` rounded down to `prec` bits. -/
def rdn (m e : Int) : Dy :=
  let s := shiftOf m
  ⟨m / ((2 ^ s : Nat) : Int), e + s⟩

/-- `m · 2^e` rounded up to `prec` bits. -/
def rup (m e : Int) : Dy :=
  let s := shiftOf m
  ⟨-((-m) / ((2 ^ s : Nat) : Int)), e + s⟩

def neg (a : Dy) : Dy := ⟨-a.m, a.e⟩

/-- Exact sum. -/
def addX (a b : Dy) : Dy :=
  if a.e ≤ b.e then ⟨a.m + b.m * ((2 ^ (b.e - a.e).toNat : Nat) : Int), a.e⟩
  else ⟨a.m * ((2 ^ (a.e - b.e).toNat : Nat) : Int) + b.m, b.e⟩

/-- Exact product. -/
def mulX (a b : Dy) : Dy := ⟨a.m * b.m, a.e + b.e⟩

/-- `a ≤ b` (exact). -/
def le (a b : Dy) : Bool := decide ((addX a (neg b)).m ≤ 0)

def min (a b : Dy) : Dy := if le a b then a else b
def max (a b : Dy) : Dy := if le a b then b else a

/-- Exact value as a rational. -/
def toRat (a : Dy) : Rat :=
  if 0 ≤ a.e then ((a.m * ((2 ^ a.e.toNat : Nat) : Int) : Int) : Rat)
  else (a.m : Rat) / ((2 ^ (-a.e).toNat : Nat) : Rat)

/-- `q` rounded down / up to a dyadic with about `prec` bits. -/
def ofRatDn (q : Rat) : Dy :=
  let k : Nat := prec + bitlen q.den
  rdn ((q.num * ((2 ^ k : Nat) : Int)) / (q.den : Int)) (-(k : Int))
def ofRatUp (q : Rat) : Dy :=
  let k : Nat := prec + bitlen q.den
  rup (-((-(q.num * ((2 ^ k : Nat) : Int))) / (q.den : Int))) (-(k : Int))

/-- Lower bound of `1 / (m · 2^e)` for `m > 0`. -/
def invDnPos (m : Nat) (e : Int) : Dy :=
  let k : Nat := prec + bitlen m
  ⟨((2 ^ k / m : Nat) : Int), -e - k⟩
/-- Upper bound of `1 / (m · 2^e)` for `m > 0`. -/
def invUpPos (m : Nat) (e : Int) : Dy :=
  let k : Nat := prec + bitlen m
  ⟨(((2 ^ k + m - 1) / m : Nat) : Int), -e - k⟩

/-! ### Integer square roots (Newton guess, checked by the callers) -/

def newtonIter : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | f + 1, n, g => newtonIter f n (Nat.div (Nat.add g (Nat.div n g)) 2)

/-- Guess for `⌊√n⌋`. Not trusted. -/
def isqrtG (n : Nat) : Nat :=
  bif Nat.beq n 0 then 0 else
    let g := newtonIter 14 n (2 ^ (bitlen n / 2 + 1))
    bif Nat.blt n (g * g) then g - 1 else g

/-- Shift and exponent for a square root of `m · 2^e`: `m · 2^k` has at least `2 prec` bits
and `e - k` is even. -/
def sqrtShift (m : Nat) (e : Int) : Nat :=
  let k0 := 2 * prec - bitlen m
  if (e - k0) % 2 = 0 then k0 else k0 + 1

/-- Lower bound of `√(m · 2^e)`. -/
def sqrtDn (m : Nat) (e : Int) : Dy :=
  let k := sqrtShift m e
  let n := m * 2 ^ k
  let r := isqrtG n
  ⟨bif Nat.ble (r * r) n then (r : Int) else 0, (e - k) / 2⟩

/-- Upper bound of `√(m · 2^e)`. -/
def sqrtUp (m : Nat) (e : Int) : Dy :=
  let k := sqrtShift m e
  let n := m * 2 ^ k
  let r := isqrtG n
  ⟨bif Nat.ble n (r * r) then (r : Int) else bif Nat.ble n ((r + 1) * (r + 1)) then (r + 1 : Nat)
    else (n + 1 : Nat), (e - k) / 2⟩

/-! ### Intervals -/

/-- `[lo, hi]`; `none` is unbounded. -/
structure DI where
  lo : Option Dy
  hi : Option Dy
  deriving Repr, Inhabited

/-- The whole line (both ends unbounded). -/
def DI.whole : DI := ⟨none, none⟩
/-- The point interval `[0, 0]`. -/
def DI.zero : DI := ⟨some Dy.zero, some Dy.zero⟩
/-- Tight dyadic enclosure of a rational, at the working precision. -/
def DI.ofRat (q : Rat) : DI := ⟨some (ofRatDn q), some (ofRatUp q)⟩
/-- Enclosure of the rational interval `[a, b]`. -/
def DI.ofRatI (a b : Rat) : DI := ⟨some (ofRatDn a), some (ofRatUp b)⟩

/-- Exact negation. -/
def DI.neg (X : DI) : DI := ⟨X.hi.map Dy.neg, X.lo.map Dy.neg⟩

/-- Outward-rounded addition of dyadic intervals. -/
def DI.add (X Y : DI) : DI :=
  ⟨match X.lo, Y.lo with
    | some a, some b => some (let s := addX a b; rdn s.m s.e)
    | _, _ => none,
   match X.hi, Y.hi with
    | some a, some b => some (let s := addX a b; rup s.m s.e)
    | _, _ => none⟩

/-- Outward-rounded subtraction. -/
def DI.sub (X Y : DI) : DI := DI.add X (DI.neg Y)

/-- Outward-rounded multiplication (four-corner rule; whole line if an end is unbounded). -/
def DI.mul (X Y : DI) : DI :=
  match X.lo, X.hi, Y.lo, Y.hi with
  | some a, some b, some c, some d =>
    let p1 := mulX a c
    let p2 := mulX a d
    let p3 := mulX b c
    let p4 := mulX b d
    let l := min (min p1 p2) (min p3 p4)
    let u := max (max p1 p2) (max p3 p4)
    ⟨some (rdn l.m l.e), some (rup u.m u.e)⟩
  | _, _, _, _ => DI.whole

/-- `1 / X` when `X` has finite endpoints of one strict sign, else the whole line. -/
def DI.inv (X : DI) : DI :=
  match X.lo, X.hi with
  | some a, some b =>
    if 0 < a.m then ⟨some (invDnPos b.m.toNat b.e), some (invUpPos a.m.toNat a.e)⟩
    else if b.m < 0 then
      ⟨some (Dy.neg (invUpPos (-b.m).toNat b.e)), some (Dy.neg (invDnPos (-a.m).toNat a.e))⟩
    else DI.whole
  | _, _ => DI.whole

/-- Outward-rounded division (`X * 1/Y`). -/
def DI.div (X Y : DI) : DI := DI.mul X (DI.inv Y)

/-- `√X` (with `√x = 0` for `x < 0`, as `Real.sqrt`). -/
def DI.sqrt (X : DI) : DI :=
  ⟨some (match X.lo with
      | some a => if 0 < a.m then sqrtDn a.m.toNat a.e else Dy.zero
      | none => Dy.zero),
   match X.hi with
    | some b => some (if 0 < b.m then sqrtUp b.m.toNat b.e else Dy.zero)
    | none => none⟩

/-- Interval absolute value. -/
def DI.abs (X : DI) : DI :=
  match X.lo, X.hi with
  | some a, some b =>
    if 0 ≤ a.m then X else if b.m ≤ 0 then DI.neg X else ⟨some Dy.zero, some (max (Dy.neg a) b)⟩
  | some a, none => if 0 ≤ a.m then X else ⟨some Dy.zero, none⟩
  | none, some b => if b.m ≤ 0 then DI.neg X else ⟨some Dy.zero, none⟩
  | none, none => ⟨some Dy.zero, none⟩

def DI.mulPow (X : DI) : Nat → DI
  | 0 => DI.ofRat 1
  | n + 1 => DI.mul (DI.mulPow X n) X

/-- Natural-number power (`X ^ n`); even powers go through `abs`. -/
def DI.pow (X : DI) (n : Nat) : DI :=
  if n % 2 = 0 then DI.mulPow (DI.abs X) n else DI.mulPow X n

/-- `π` from the 40-digit bounds `RealFP.pi_gt_d40` / `pi_lt_d40`. -/
def piLo : Rat := 31415926535897932384626433832795028841971 / 10 ^ 40
/-- Strict 40-digit upper bound used in `DI.pi`. -/
def piHi : Rat := 31415926535897932384626433832795028841972 / 10 ^ 40
def DI.pi : DI := DI.ofRatI piLo piHi

/-! ### 128-bit elementary functions

Point enclosures from Taylor polynomials (Horner in interval arithmetic) with Mathlib's
remainder bounds, after exact argument halving (`exp`, `sin`, `cos`) or square roots (`log`).
Soundness: `RealFPMathlib/I128DyTransc.lean`. -/

/-- The point interval `[d, d]`. -/
def DI.pt (d : Dy) : DI := ⟨some d, some d⟩

/-- `[-r, r]` for a rational `r ≥ 0`. -/
def DI.pm (r : Rat) : DI := ⟨some (ofRatDn (-r)), some (ofRatUp r)⟩

/-- Multiply by `2^j` (exact). -/
def Dy.scale (j : Int) (d : Dy) : Dy := ⟨d.m, d.e + j⟩
def DI.scale (j : Int) (X : DI) : DI := ⟨X.lo.map (Dy.scale j), X.hi.map (Dy.scale j)⟩

/-- Coefficient list `[f k, f (k+1), …]` of length `n`. -/
def coefs (f : Nat → Rat) : Nat → Nat → List Rat
  | _, 0 => []
  | k, n + 1 => f k :: coefs f (k + 1) n

/-- `d · X` for a point `d` (two products instead of four corners). -/
def DI.mulPt (d : Dy) (X : DI) : DI :=
  match X.lo, X.hi with
  | some l, some h =>
    if 0 ≤ d.m then
      let p := mulX d l; let q := mulX d h
      ⟨some (rdn p.m p.e), some (rup q.m q.e)⟩
    else
      let p := mulX d h; let q := mulX d l
      ⟨some (rdn p.m p.e), some (rup q.m q.e)⟩
  | _, _ => DI.whole

/-- Horner evaluation of `c₀ + c₁ d + …` at a point `d`. -/
def horner (cs : List Rat) (d : Dy) : DI :=
  match cs with
  | [] => DI.zero
  | c :: cs => DI.add (DI.ofRat c) (DI.mulPt d (horner cs d))

/-- Taylor length and remainder for `|y| ≤ 2⁻⁸` (`Real.exp_bound`, `Complex.exp_bound`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def nT : Nat := 14
def remT : Rat := (1 / 256) ^ nT * (nT + 1 : Nat) / ((fact nT * nT : Nat) : Rat)

def expCoef (m : Nat) : Rat := 1 / (fact m : Rat)
/-- `Re (I^m) / m!` and `Im (I^m) / m!`. -/
def cosCoef (m : Nat) : Rat :=
  (if m % 4 = 0 then 1 else if m % 4 = 2 then -1 else 0) / (fact m : Rat)
def sinCoef (m : Nat) : Rat :=
  (if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0) / (fact m : Rat)

/-- Halvings bringing `d` to `|d / 2^s| ≤ 2⁻⁸` (any value is sound). -/
def halvings (d : Dy) : Nat := (((bitlen d.m.natAbs : Nat) : Int) + d.e + 8).toNat

def small (y : Dy) : Bool := decide (-(1 / 256) ≤ toRat y ∧ toRat y ≤ 1 / 256)

def sqIter : Nat → DI → DI
  | 0, X => X
  | n + 1, X => sqIter n (DI.mul X X)

/-- Enclosure of `exp d` (whole line if `d` is too large). -/
def expPt (d : Dy) : DI :=
  let s := halvings d
  let y : Dy := ⟨d.m, d.e - s⟩
  if small y && decide (s ≤ 64) then
    sqIter s (DI.add (horner (coefs expCoef 0 nT) y) (DI.pm remT))
  else DI.whole

def DI.exp (X : DI) : DI :=
  ⟨match X.lo with | some a => (expPt a).lo | none => some Dy.zero,
   match X.hi with | some b => (expPt b).hi | none => none⟩

def dblIter : Nat → DI × DI → DI × DI
  | 0, p => p
  | n + 1, (S, C) => dblIter n (DI.scale 1 (DI.mul S C), DI.sub (DI.mul C C) (DI.mul S S))

/-- `(sin d, cos d)`. -/
def sinCosPt (d : Dy) : DI × DI :=
  let s := halvings d
  let y : Dy := ⟨d.m, d.e - s⟩
  if small y && decide (s ≤ 64) then
    dblIter s (DI.add (horner (coefs sinCoef 0 nT) y) (DI.pm remT),
      DI.add (horner (coefs cosCoef 0 nT) y) (DI.pm remT))
  else (DI.whole, DI.whole)

def negOne : Dy := ⟨-1, 0⟩
def one : Dy := ⟨1, 0⟩

/-- Intersect with `[-1, 1]`. -/
def DI.clamp1 (X : DI) : DI :=
  ⟨some (match X.lo with | some l => Dy.max l negOne | none => negOne),
   some (match X.hi with | some h => Dy.min h one | none => one)⟩

/-- Centre and radius of a finite interval: `|x - c| ≤ r` on `[a, b]`. -/
def centre (a b : Dy) : Dy := let s := addX a b; rdn s.m (s.e - 1)
def radius (a b c : Dy) : Dy := Dy.max (addX b (Dy.neg c)) (addX c (Dy.neg a))

/-- `sin` / `cos` on an interval: value at the centre plus the Lipschitz bound, in `[-1, 1]`. -/
def DI.sinCos (cosQ : Bool) (X : DI) : DI :=
  match X.lo, X.hi with
  | some a, some b =>
    let c := centre a b
    let r := radius a b c
    let p := sinCosPt c
    DI.clamp1 (DI.add (if cosQ then p.2 else p.1) ⟨some (Dy.neg r), some r⟩)
  | _, _ => DI.clamp1 DI.whole

/-- Log series point: `log w = log (1 - u)`, `u = 1 - w`, `|u| ≤ 2⁻⁶`
(`Real.abs_log_sub_add_sum_range_le`). -/
def nL : Nat := 23
def remL : Rat := 2 * (1 / 64) ^ (nL + 1)
def logCoef (i : Nat) : Rat := 1 / ((i + 1 : Nat) : Rat)

def logSer (w : Dy) : DI :=
  let u := addX one (Dy.neg w)
  if decide (-(1 / 64) ≤ toRat u ∧ toRat u ≤ 1 / 64) then
    DI.add (DI.neg (DI.mulPt u (horner (coefs logCoef 0 nL) u))) (DI.pm remL)
  else DI.whole

def sqrtIter : Nat → DI → DI
  | 0, X => X
  | n + 1, X => sqrtIter n (DI.sqrt X)

/-- Square roots bringing `d` near `1`. -/
def roots (d : Dy) : Nat :=
  if decide (-(1 / 128) ≤ toRat (addX one (Dy.neg d)) ∧ toRat (addX one (Dy.neg d)) ≤ 1 / 128) then 0
  else bitlen ((((bitlen d.m.natAbs : Nat) : Int) + d.e).natAbs + 1) + 7

/-- Lower / upper bound of `log d` for `d > 0`. -/
def logLo (d : Dy) : Option Dy :=
  let j := roots d
  match (sqrtIter j (DI.pt d)).lo with
  | some w => if 0 < w.m then ((logSer w).lo).map (Dy.scale j) else none
  | none => none
def logHi (d : Dy) : Option Dy :=
  let j := roots d
  match (sqrtIter j (DI.pt d)).hi with
  | some w => if 0 < w.m then ((logSer w).hi).map (Dy.scale j) else none
  | none => none

/-- `log` on an interval with a positive lower end (else `none`: the caller falls back). -/
def DI.log? (X : DI) : Option DI :=
  match X.lo with
  | some a => if 0 < a.m then some ⟨logLo a, X.hi.bind logHi⟩ else none
  | none => none

/-- `log 2`, `log 10` enclosures. -/
def DI.logConst (q : Rat) : DI := ⟨logLo (ofRatDn q), logHi (ofRatUp q)⟩

/-- `sinh m / m!` at `0`: odd Taylor coefficients of `sinh`. -/
def sinhCoef (m : Nat) : Rat := (if m % 2 = 1 then 1 else 0) / (fact m : Rat)

/-- `sinh d`: odd Taylor series when `|d| ≤ 2⁻⁸` (no cancellation), else `(E - 1/E) / 2`. -/
def sinhPt (d : Dy) : DI :=
  if small d then DI.add (horner (coefs sinhCoef 0 nT) d) (DI.pm remT)
  else
    let E := expPt d
    DI.scale (-1) (DI.sub E (DI.inv E))

def coshPt (d : Dy) : DI :=
  let E := expPt d
  DI.scale (-1) (DI.add E (DI.inv E))

def DI.sinh (X : DI) : DI :=
  ⟨X.lo.bind (fun a => (sinhPt a).lo), X.hi.bind (fun b => (sinhPt b).hi)⟩

def DI.cosh (X : DI) : DI :=
  let A := DI.abs X
  ⟨match A.lo with | some a => if 0 ≤ a.m then (coshPt a).lo else some one | none => some one,
   A.hi.bind (fun b => (coshPt b).hi)⟩

/-- `tanh d`: `sinh d / cosh d` when `|d| ≤ 2⁻⁸`, else `1 - 2 / (exp (2d) + 1)`. -/
def tanhPt (d : Dy) : DI :=
  if small d then DI.div (sinhPt d) (coshPt d)
  else DI.sub (DI.ofRat 1) (DI.mul (DI.ofRat 2) (DI.inv (DI.add (expPt (Dy.scale 1 d)) (DI.ofRat 1))))

/-- `tanh` is increasing: endpoint values, clamped to `[-1, 1]`. -/
def DI.tanh (X : DI) : DI :=
  DI.clamp1 ⟨X.lo.bind (fun a => (tanhPt a).lo), X.hi.bind (fun b => (tanhPt b).hi)⟩

/-! ### Functions through the Interval64 kernel evaluator -/

/-- Lower endpoint from a binary64 bit pattern (`none` if infinite / NaN). -/
def decLo (n : Nat) : Option Dy :=
  if KF.isNaN n then none else (Spec.bitsToRat? (UInt64.ofNat n)).map ofRatDn
def decHi (n : Nat) : Option Dy :=
  if KF.isNaN n then none else (Spec.bitsToRat? (UInt64.ofNat n)).map ofRatUp

variable [ExtTbl]

def lift1 (f : IExpr) (X : DI) : DI :=
  match X.lo, X.hi with
  | some a, some b =>
    let R := evalK [KI.ofRatInterval (toRat a) (toRat b)] f
    ⟨decLo R.lo, decHi R.hi⟩
  | _, _ => DI.whole

def lift2 (f : IExpr) (X Y : DI) : DI :=
  match X.lo, X.hi, Y.lo, Y.hi with
  | some a, some b, some c, some d =>
    let R := evalK [KI.ofRatInterval (toRat a) (toRat b), KI.ofRatInterval (toRat c) (toRat d)] f
    ⟨decLo R.lo, decHi R.hi⟩
  | _, _, _, _ => DI.whole

def evalQ (env : List DI) : IExpr → DI
  | .var i => env.getD i DI.zero
  | .rat q => DI.ofRat q
  | .add a b => DI.add (evalQ env a) (evalQ env b)
  | .sub a b => DI.sub (evalQ env a) (evalQ env b)
  | .mul a b => DI.mul (evalQ env a) (evalQ env b)
  | .div a b => DI.div (evalQ env a) (evalQ env b)
  | .neg a => DI.neg (evalQ env a)
  | .inv a => DI.inv (evalQ env a)
  | .sqrt a => DI.sqrt (evalQ env a)
  | .abs a => DI.abs (evalQ env a)
  | .pow a n => DI.pow (evalQ env a) n
  | .exp a => DI.exp (evalQ env a)
  | .log a =>
    let X := evalQ env a
    match DI.log? X with | some Y => Y | none => lift1 (.log (.var 0)) X
  | .sin a => DI.sinCos false (evalQ env a)
  | .cos a => DI.sinCos true (evalQ env a)
  | .pi => DI.pi
  | .atan a => lift1 (.atan (.var 0)) (evalQ env a)
  | .atan2 a b => lift2 (.atan2 (.var 0) (.var 1)) (evalQ env a) (evalQ env b)
  | .sinh a => DI.sinh (evalQ env a)
  | .cosh a => DI.cosh (evalQ env a)
  | .tanh a => DI.tanh (evalQ env a)
  | .log2 a =>
    let X := evalQ env a
    match DI.log? X with
    | some Y => DI.div Y (DI.logConst 2) | none => lift1 (.log2 (.var 0)) X
  | .log10 a =>
    let X := evalQ env a
    match DI.log? X with
    | some Y => DI.div Y (DI.logConst 10) | none => lift1 (.log10 (.var 0)) X
  | .tan a => lift1 (.tan (.var 0)) (evalQ env a)
  | .asin a => lift1 (.asin (.var 0)) (evalQ env a)
  | .acos a => lift1 (.acos (.var 0)) (evalQ env a)
  | .ext k d a => lift1 (.ext k d (.var 0)) (evalQ env a)

/-- Functions evaluated through Interval64 (binary64 precision) at precision 128. `log`,
`logb 2`, `logb 10` are listed too: they fall back when the argument is not known to be `> 0`. -/
def lifted : IExpr → List String
  | .var _ | .rat _ | .pi => []
  | .add a b | .sub a b | .mul a b | .div a b => lifted a ++ lifted b
  | .neg a | .inv a | .sqrt a | .abs a | .pow a _ | .exp a | .sin a | .cos a | .sinh a
  | .cosh a | .tanh a => lifted a
  | .log a => "log (on arguments not known to be positive)" :: lifted a
  | .log2 a => "logb 2 (on arguments not known to be positive)" :: lifted a
  | .log10 a => "logb 10 (on arguments not known to be positive)" :: lifted a
  | .atan a => "arctan" :: lifted a
  | .atan2 a b => "atan2" :: (lifted a ++ lifted b)
  | .tan a => "tan" :: lifted a
  | .asin a => "arcsin" :: lifted a
  | .acos a => "arccos" :: lifted a
  | .ext _ _ a => "extension function" :: lifted a

/-! ### Goal predicates and certificates -/

def gLe (c : Rat) (F : DI) : Bool := match F.hi with | some u => decide ((toRat u) ≤ c) | none => false
def gLt (c : Rat) (F : DI) : Bool := match F.hi with | some u => decide ((toRat u) < c) | none => false
def gGe (c : Rat) (F : DI) : Bool := match F.lo with | some l => decide (c ≤ (toRat l)) | none => false
def gGt (c : Rat) (F : DI) : Bool := match F.lo with | some l => decide (c < (toRat l)) | none => false



/-- `Dy` from base-`2^62` limbs (most significant first). Certificates are emitted this way:
the kernel handles terms with `Nat` literals of `2^63` or more much more slowly. -/
def ofLimbs (neg : Bool) (ls : List Nat) (e : Int) : Dy :=
  let m : Nat := ls.foldl (fun acc l => acc * 4611686018427387904 + l) 0
  ⟨if neg then -(m : Int) else (m : Int), e⟩

def limbs (n : Nat) : List Nat :=
  if n < 4611686018427387904 then [n] else limbs (n / 4611686018427387904) ++ [n % 4611686018427387904]
decreasing_by omega

/-- Bisection certificate: `split i d l r` cuts variable `i` at the dyadic `d`. -/
inductive Cert where
  | leaf
  | split (i : Nat) (d : Dy) (l r : Cert)
  deriving Repr, Inhabited

def Cert.leaves : Cert → Nat
  | .leaf => 1
  | .split _ _ l r => l.leaves + r.leaves

def leftAt (X : DI) (d : Dy) : DI := ⟨X.lo, some d⟩
def rightAt (X : DI) (d : Dy) : DI := ⟨some d, X.hi⟩

def checkQ (e : IExpr) (g : DI → Bool) : Cert → List DI → Bool
  | .leaf, env => g (evalQ env e)
  | .split i d l r, env =>
    checkQ e g l (env.set i (leftAt (env.getD i DI.zero) d)) &&
      checkQ e g r (env.set i (rightAt (env.getD i DI.zero) d))

def boxes : List (Rat × Rat) → List DI
  | [] => []
  | (a, b) :: t => DI.ofRatI a b :: boxes t

/-- Widest variable and its midpoint (a dyadic rounded to `prec` bits, strictly inside). -/
def pickSplit (env : List DI) : Option (Nat × Dy) := Id.run do
  let mut best : Option (Nat × Rat × Dy) := none
  for h : i in [0:env.length] do
    let X := env[i]
    match X.lo, X.hi with
    | some a, some b =>
      let (qa, qb) := (toRat a, toRat b)
      let s := addX a b
      let m := rdn s.m (s.e - 1)
      let qm := toRat m
      if qa < qm && qm < qb then
        let w := qb - qa
        match best with
        | some (_, w', _) => if w' < w then best := some (i, w, m)
        | none => best := some (i, w, m)
    | _, _ => pure ()
  return best.map fun (i, _, m) => (i, m)

partial def search (e : IExpr) (g : DI → Bool) (depth maxEvals : Nat) :
    List DI → StateM Nat (Option Cert)
  | env => do
    let n ← get
    if n ≥ maxEvals then return none
    set (n + 1)
    if g (evalQ env e) then return some .leaf
    if depth == 0 then return none
    match pickSplit env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i DI.zero
      let some l ← search e g (depth - 1) maxEvals (env.set i (leftAt X m)) | return none
      let some r ← search e g (depth - 1) maxEvals (env.set i (rightAt X m)) | return none
      return some (.split i m l r)

/-! ### Derivative certificates (monotonicity, centred form)

Mirror of `Interval64.KF.DCert` / `checkD` (`Interval64/Kernel/Deriv.lean`) with dyadic
endpoints. Soundness: `RealFP.I128Q.checkDQ_sound` (`RealFPMathlib/I128Deriv.lean`). -/

/-- The lower endpoint is finite and `> 0`. -/
def posQ (X : DI) : Bool := match X.lo with | some a => decide (0 < a.m) | none => false
/-- The interval excludes `0` (finite endpoint of strict sign). -/
def nzQ (X : DI) : Bool :=
  posQ X || (match X.hi with | some b => decide (b.m < 0) | none => false)

/-- `e` is differentiable on the box (as `Interval64.KF.domOK`). -/
def domOKQ (env : List DI) : IExpr → Bool
  | .var _ => true
  | .rat _ => true
  | .add a b => domOKQ env a && domOKQ env b
  | .sub a b => domOKQ env a && domOKQ env b
  | .mul a b => domOKQ env a && domOKQ env b
  | .div a b => domOKQ env a && domOKQ env b && nzQ (evalQ env b)
  | .neg a => domOKQ env a
  | .inv a => domOKQ env a && nzQ (evalQ env a)
  | .sqrt a => domOKQ env a && posQ (evalQ env a)
  | .abs _ => false
  | .pow a _ => domOKQ env a
  | .exp a => domOKQ env a
  | .log a => domOKQ env a && posQ (evalQ env a)
  | .sin a => domOKQ env a
  | .cos a => domOKQ env a
  | .pi => true
  | .atan a => domOKQ env a
  | .atan2 _ _ => false
  | .sinh a => domOKQ env a
  | .cosh a => domOKQ env a
  | .tanh a => domOKQ env a
  | .log2 a => domOKQ env a && posQ (evalQ env a)
  | .log10 a => domOKQ env a && posQ (evalQ env a)
  | .tan a => domOKQ env a && nzQ (evalQ env (.cos a))
  | .asin a => domOKQ env a && posQ (evalQ env (.sub (.rat 1) (.pow a 2)))
  | .acos a => domOKQ env a && posQ (evalQ env (.sub (.rat 1) (.pow a 2)))
  | .ext _ _ _ => false

/-- Intersection (`none` = unbounded). -/
def DI.meet (A B : DI) : DI :=
  ⟨match A.lo, B.lo with
    | some a, some b => some (Dy.max a b) | some a, none => some a | none, b => b,
   match A.hi, B.hi with
    | some a, some b => some (Dy.min a b) | some a, none => some a | none, b => b⟩

/-- Centred form in variable `i` around the point `d`, intersected with the plain enclosure. -/
def centerQ (env : List DI) (e : IExpr) (i : Nat) (d : Dy) : DI :=
  DI.meet (evalQ env e)
    (DI.add (evalQ (env.set i (DI.pt d)) e)
      (DI.mul (evalQ env (e.deriv i)) (DI.sub (env.getD i DI.zero) (DI.pt d))))

/-- `d` lies in `X` (both endpoints finite). -/
def inside (X : DI) (d : Dy) : Bool :=
  match X.lo, X.hi with
  | some a, some b => decide (toRat a ≤ toRat d ∧ toRat d ≤ toRat b)
  | _, _ => false

inductive DCert where
  | leaf
  | split (i : Nat) (d : Dy) (l r : DCert)
  /-- `∂ᵢe ≥ 0` (`inc`) or `≤ 0` on the box (certificate `dc`); continue at the endpoint. -/
  | mono (i : Nat) (inc : Bool) (dc c : DCert)
  /-- Centred form in variable `i` at the dyadic `d`. -/
  | center (i : Nat) (d : Dy)
  deriving Repr, Inhabited

def DCert.leaves : DCert → Nat
  | .leaf => 1
  | .split _ _ l r => l.leaves + r.leaves
  | .mono _ _ dc c => dc.leaves + c.leaves
  | .center _ _ => 1

/-- `upper`: the goal predicate is downward closed (`f ≤ c`, `f < c`); otherwise upward closed. -/
def checkDQ (e : IExpr) (g : DI → Bool) (upper : Bool) : DCert → List DI → Bool
  | .leaf, env => g (evalQ env e)
  | .split i d l r, env =>
    checkDQ e g upper l (env.set i (leftAt (env.getD i DI.zero) d)) &&
      checkDQ e g upper r (env.set i (rightAt (env.getD i DI.zero) d))
  | .mono i inc dc c, env =>
    Nat.blt i env.length && domOKQ env e &&
      (bif inc then checkDQ (e.deriv i) (gGe 0) false dc env
       else checkDQ (e.deriv i) (gLe 0) true dc env) &&
      (match (bif inc == upper then (env.getD i DI.zero).hi else (env.getD i DI.zero).lo) with
       | some p => checkDQ e g upper c (env.set i (DI.pt p))
       | none => false)
  | .center i d, env =>
    Nat.blt i env.length && domOKQ env e && inside (env.getD i DI.zero) d &&
      g (centerQ env e i d)

/-- Variables whose interval is not a point, widest first. -/
def wideVarsQ (env : List DI) : List Nat :=
  let ws := (List.range env.length).filterMap fun i =>
    let X := env.getD i DI.zero
    match X.lo, X.hi with
    | some a, some b => if toRat a < toRat b then some (i, toRat b - toRat a) else none
    | _, _ => none
  (ws.mergeSort (fun p q => decide (q.2 ≤ p.2))).map (·.1)

/-- Certificate search (compiled, untrusted), as `RealFP.IntervalTactic.searchD`: plain enclosure,
then monotonicity with the derivative sign visible, then the centred form at the midpoint of the
widest variable, then monotonicity with the sign proved by higher derivatives, else bisection. -/
partial def searchDQ (deriv : Bool) (maxEvals : Nat) (e : IExpr) (g : DI → Bool) (upper : Bool)
    (order : Nat) (allowSplit : Bool) : Nat → List DI → StateM Nat (Option DCert)
  | depth, env => do
    modify (· + 1)
    if g (evalQ env e) then return some .leaf
    if (← get) ≥ maxEvals then return none
    if deriv && domOKQ env e then
      let tryEnd (i : Nat) (inc : Bool) (dc : DCert) : StateM Nat (Option DCert) := do
        let X := env.getD i DI.zero
        let some p := (if inc == upper then X.hi else X.lo) | return none
        let some c ← searchDQ deriv maxEvals e g upper order allowSplit depth (env.set i (DI.pt p))
          | return none
        return some (.mono i inc dc c)
      for i in wideVarsQ env do
        modify (· + 1)
        let D := evalQ env (e.deriv i)
        if gGe 0 D then
          if let some c ← tryEnd i true .leaf then return some c
        if gLe 0 D then
          if let some c ← tryEnd i false .leaf then return some c
      if let some (i, m) := pickSplit env then
        modify (· + 1)
        if checkDQ e g upper (.center i m) env then return some (.center i m)
      if order > 0 then
        for i in wideVarsQ env do
          for inc in [true, false] do
            let gs := if inc then gGe 0 else gLe 0
            if let some dc ← searchDQ deriv maxEvals (e.deriv i) gs (!inc) (order - 1) false depth env then
              if let some c ← tryEnd i inc dc then return some c
    if depth == 0 || !allowSplit || (← get) ≥ maxEvals then return none
    match pickSplit env with
    | none => return none
    | some (i, m) =>
      let X := env.getD i DI.zero
      let some l ← searchDQ deriv maxEvals e g upper order allowSplit (depth - 1)
        (env.set i (leftAt X m)) | return none
      let some r ← searchDQ deriv maxEvals e g upper order allowSplit (depth - 1)
        (env.set i (rightAt X m)) | return none
      return some (.split i m l r)

/-- Display. -/
def fmtEnd (d : Option Dy) (inf : String) : String :=
  match d with
  | some a => Interval64.decimalOfRat (toRat a) 34
  | none => inf
def DI.toString (X : DI) : String := s!"[{fmtEnd X.lo "-inf"}, {fmtEnd X.hi "inf"}]"

end Interval128.Dy
