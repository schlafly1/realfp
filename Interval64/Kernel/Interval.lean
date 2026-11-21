/-
Kernel fast path for intervals: `KI` is an interval given by two `Nat` bit patterns, and each
operation below mirrors the `Interval64` operation of the same name using the `KF` scalar
functions (Nat arithmetic only on the arithmetic path). `Interval64Proofs/KernelInterval.lean`
proves `toI (KI.add X Y) = toI X + toI Y` etc., so nothing here is trusted.
`exp` / `log` / `sin` / `cos` call the existing bit-level specifications (`Transc` / `Trig`),
which are much slower in the kernel. Runtime code never calls these functions.
-/
import Interval64.Kernel.Nat
import Interval64.Transc
import Interval64.Trig
import Interval64.InvTrig
import Interval64.OfRat

namespace Interval64.KF

/-- An interval as two bit patterns. -/
structure KI where
  lo : Nat
  hi : Nat
  deriving Repr, Inhabited, DecidableEq

namespace KI

def negInfBits : Nat := 0xFFF0000000000000
def oneBits : Nat := 0x3FF0000000000000

def invalid : KI := ⟨qNaN, qNaN⟩
def whole : KI := ⟨negInfBits, infBits⟩
def one : KI := ⟨oneBits, oneBits⟩

def isInvalid (a : KI) : Bool := isNaN a.lo || isNaN a.hi
def anyNan (a b : KI) : Bool := isNaN a.lo || isNaN a.hi || isNaN b.lo || isNaN b.hi

def fmin (x y : Nat) : Nat := bif lt x y then x else y
def fmax (x y : Nat) : Nat := bif lt y x then x else y

def containsZero (a : KI) : Bool := !isInvalid a && le a.lo 0 && le 0 a.hi

def add (a b : KI) : KI :=
  bif anyNan a b then invalid else ⟨KF.add a.lo b.lo false, KF.add a.hi b.hi true⟩

def sub (a b : KI) : KI :=
  bif anyNan a b then invalid else ⟨KF.sub a.lo b.hi false, KF.sub a.hi b.lo true⟩

def accCorner (x y lo hi : Nat) (got : Bool) : Nat × Nat × Bool :=
  bif (beq x 0 && isInf y) || (beq y 0 && isInf x) then (lo, hi, got)
  else
    let d := KF.mul x y false
    let u := KF.mul x y true
    bif isNaN d || isNaN u then (lo, hi, got)
    else bif !got then (d, u, true)
    else (bif lt d lo then d else lo, bif lt hi u then u else hi, true)

def accStep (x y : Nat) (r : Nat × Nat × Bool) : Nat × Nat × Bool := accCorner x y r.1 r.2.1 r.2.2

def mulEnd (r : Nat × Nat × Bool) : KI := bif !r.2.2 then whole else ⟨r.1, r.2.1⟩

def mul (a b : KI) : KI :=
  bif anyNan a b then invalid
  else mulEnd (accStep a.hi b.hi (accStep a.hi b.lo (accStep a.lo b.hi (accCorner a.lo b.lo 0 0 false))))

def neg (a : KI) : KI := ⟨negBits a.hi, negBits a.lo⟩

def inv (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else bif containsZero a then whole
  else ⟨KF.div oneBits a.hi false, KF.div oneBits a.lo true⟩

def sqrt (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else bif lt a.hi 0 then invalid
  else ⟨KF.sqrt (bif lt a.lo 0 then 0 else a.lo) false, KF.sqrt a.hi true⟩

def abs (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else bif le 0 a.lo then a
  else bif le a.hi 0 then ⟨negBits a.hi, negBits a.lo⟩
  else ⟨0, fmax (negBits a.lo) a.hi⟩

def square (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else bif le 0 a.lo then ⟨KF.mul a.lo a.lo false, KF.mul a.hi a.hi true⟩
  else bif le a.hi 0 then ⟨KF.mul a.hi a.hi false, KF.mul a.lo a.lo true⟩
  else ⟨0, fmax (KF.mul a.lo a.lo true) (KF.mul a.hi a.hi true)⟩

def ipowAux : Nat → KI → Nat → KI → KI
  | 0, _, e, acc => bif Nat.beq e 0 then acc else whole
  | fuel + 1, b, e, acc =>
    bif Nat.beq e 0 then acc
    else ipowAux fuel (square b) (Nat.div e 2) (bif Nat.beq (Nat.mod e 2) 1 then mul acc b else acc)

def ipow (b : KI) (e : Nat) : KI := ipowAux 64 b e one

def powLo (f : Nat) (n : Nat) : Nat := bif isInf f then f else (ipow ⟨f, f⟩ n).lo
def powHi (f : Nat) (n : Nat) : Nat := bif isInf f then f else (ipow ⟨f, f⟩ n).hi

def pown (a : KI) (n : Nat) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else if n == 0 then one
  else if n % 2 == 1 then ⟨powLo a.lo n, powHi a.hi n⟩
  else
    let b := abs a
    ⟨powLo b.lo n, powHi b.hi n⟩

def hull (a b : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then b
  else bif isNaN b.lo || isNaN b.hi then a
  else ⟨fmin a.lo b.lo, fmax a.hi b.hi⟩

/-- `ofRat q` (endpoint rounding through the rational `Spec` functions). -/
def ofRat (q : Rat) : KI := ⟨(Spec.ofRatDown q).toNat, (Spec.ofRatUp q).toNat⟩
def ofRatInterval (lo hi : Rat) : KI := ⟨(Spec.ofRatDown lo).toNat, (Spec.ofRatUp hi).toNat⟩

def exp (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else ⟨(Transc.expDownBits (UInt64.ofNat a.lo)).toNat, (Transc.expUpBits (UInt64.ofNat a.hi)).toNat⟩

def logLo (x : Nat) : Nat :=
  match Spec.unpackBits (UInt64.ofNat x) with
  | .finite .positive .. => (Transc.logDownBits (UInt64.ofNat x)).toNat
  | .infinity .positive => infBits
  | .notANumber => qNaN
  | _ => negInfBits

def log (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else
    match Spec.unpackBits (UInt64.ofNat a.hi) with
    | .finite .positive .. => ⟨logLo a.lo, (Transc.logUpBits (UInt64.ofNat a.hi)).toNat⟩
    | .zero _ => ⟨logLo a.lo, negInfBits⟩
    | .infinity .positive => ⟨logLo a.lo, infBits⟩
    | _ => invalid

def minusOne : Nat := (Spec.ofRatDown (-1)).toNat
def plusOne : Nat := (Spec.ofRatUp 1).toNat

def sin (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else
    match Spec.bitsToRat? (UInt64.ofNat a.lo), Spec.bitsToRat? (UInt64.ofNat a.hi) with
    | some x, some y =>
      ⟨if Trig.avoids x y 3 then fmin (Trig.sinDownBits (UInt64.ofNat a.lo)).toNat
          (Trig.sinDownBits (UInt64.ofNat a.hi)).toNat else minusOne,
       if Trig.avoids x y 1 then fmax (Trig.sinUpBits (UInt64.ofNat a.lo)).toNat
          (Trig.sinUpBits (UInt64.ofNat a.hi)).toNat else plusOne⟩
    | _, _ => ⟨minusOne, plusOne⟩

def cos (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else
    match Spec.bitsToRat? (UInt64.ofNat a.lo), Spec.bitsToRat? (UInt64.ofNat a.hi) with
    | some x, some y =>
      ⟨if Trig.avoids x y 2 then fmin (Trig.cosDownBits (UInt64.ofNat a.lo)).toNat
          (Trig.cosDownBits (UInt64.ofNat a.hi)).toNat else minusOne,
       if Trig.avoids x y 0 then fmax (Trig.cosUpBits (UInt64.ofNat a.lo)).toNat
          (Trig.cosUpBits (UInt64.ofNat a.hi)).toNat else plusOne⟩
    | _, _ => ⟨minusOne, plusOne⟩

def atan (a : KI) : KI :=
  bif isNaN a.lo || isNaN a.hi then invalid
  else ⟨(InvTrig.atanDownBits (UInt64.ofNat a.lo)).toNat, (InvTrig.atanUpBits (UInt64.ofNat a.hi)).toNat⟩

def pi : KI := ⟨InvTrig.piDownBits.toNat, InvTrig.piUpBits.toNat⟩
def halfPi : KI := ⟨InvTrig.halfPiDownBits.toNat, InvTrig.halfPiUpBits.toNat⟩
def negHalfPi : KI := ⟨InvTrig.negHalfPiDownBits.toNat, InvTrig.negHalfPiUpBits.toNat⟩
def argHull : KI := ⟨InvTrig.negPiDownBits.toNat, InvTrig.piUpBits.toNat⟩

end KI

end Interval64.KF
