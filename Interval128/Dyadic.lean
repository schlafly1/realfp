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

def DI.whole : DI := ⟨none, none⟩
def DI.zero : DI := ⟨some Dy.zero, some Dy.zero⟩
def DI.ofRat (q : Rat) : DI := ⟨some (ofRatDn q), some (ofRatUp q)⟩
def DI.ofRatI (a b : Rat) : DI := ⟨some (ofRatDn a), some (ofRatUp b)⟩

def DI.neg (X : DI) : DI := ⟨X.hi.map Dy.neg, X.lo.map Dy.neg⟩

def DI.add (X Y : DI) : DI :=
  ⟨match X.lo, Y.lo with
    | some a, some b => some (let s := addX a b; rdn s.m s.e)
    | _, _ => none,
   match X.hi, Y.hi with
    | some a, some b => some (let s := addX a b; rup s.m s.e)
    | _, _ => none⟩

def DI.sub (X Y : DI) : DI := DI.add X (DI.neg Y)

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

def DI.div (X Y : DI) : DI := DI.mul X (DI.inv Y)

/-- `√X` (with `√x = 0` for `x < 0`, as `Real.sqrt`). -/
def DI.sqrt (X : DI) : DI :=
  ⟨some (match X.lo with
      | some a => if 0 < a.m then sqrtDn a.m.toNat a.e else Dy.zero
      | none => Dy.zero),
   match X.hi with
    | some b => some (if 0 < b.m then sqrtUp b.m.toNat b.e else Dy.zero)
    | none => none⟩

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

def DI.pow (X : DI) (n : Nat) : DI :=
  if n % 2 = 0 then DI.mulPow (DI.abs X) n else DI.mulPow X n

/-- `π` from the 40-digit bounds `RealFP.pi_gt_d40` / `pi_lt_d40`. -/
def piLo : Rat := 31415926535897932384626433832795028841971 / 10 ^ 40
def piHi : Rat := 31415926535897932384626433832795028841972 / 10 ^ 40
def DI.pi : DI := DI.ofRatI piLo piHi

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
  | .exp a => lift1 (.exp (.var 0)) (evalQ env a)
  | .log a => lift1 (.log (.var 0)) (evalQ env a)
  | .sin a => lift1 (.sin (.var 0)) (evalQ env a)
  | .cos a => lift1 (.cos (.var 0)) (evalQ env a)
  | .pi => DI.pi
  | .atan a => lift1 (.atan (.var 0)) (evalQ env a)
  | .atan2 a b => lift2 (.atan2 (.var 0) (.var 1)) (evalQ env a) (evalQ env b)
  | .sinh a => lift1 (.sinh (.var 0)) (evalQ env a)
  | .cosh a => lift1 (.cosh (.var 0)) (evalQ env a)
  | .tanh a => lift1 (.tanh (.var 0)) (evalQ env a)
  | .log2 a => lift1 (.log2 (.var 0)) (evalQ env a)
  | .log10 a => lift1 (.log10 (.var 0)) (evalQ env a)
  | .tan a => lift1 (.tan (.var 0)) (evalQ env a)
  | .asin a => lift1 (.asin (.var 0)) (evalQ env a)
  | .acos a => lift1 (.acos (.var 0)) (evalQ env a)
  | .ext k d a => lift1 (.ext k d (.var 0)) (evalQ env a)

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

/-- Display. -/
def fmtEnd (d : Option Dy) (inf : String) : String :=
  match d with
  | some a => Interval64.decimalOfRat (toRat a) 34
  | none => inf
def DI.toString (X : DI) : String := s!"[{fmtEnd X.lo "-inf"}, {fmtEnd X.hi "inf"}]"

end Interval128.Dy
