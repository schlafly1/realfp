/-
Kernel fast path: binary64 directed rounding on `Nat` bit patterns.

Lean's kernel computes `Nat.add/sub/mul/div/mod/beq/ble/land/lor/xor/shiftLeft/shiftRight/pow`
on literals with GMP and interprets everything else step by step. The definitions here use
only those operations plus `Bool.casesOn` (written `ifB c then t else e`): no `UInt64`,
`BitVec`, `Int`, type-class instances, or recursion on the common path. `decide +kernel`
evaluates one operation in about a hundred microseconds instead of several milliseconds.

The definitions mirror `Interval64.Spec` step by step (exponents are biased by `4096` so they
stay natural numbers). `Interval64Proofs/KernelEq.lean` proves
`(Spec.add a b up).toNat = KF.add a.toNat b.toNat up` etc. for all inputs, so nothing here is
trusted. Runtime code never calls these functions.
-/
namespace Interval64.KF

/-- `ifB c then t else e` is `Bool.casesOn c e t` at type `Nat` (one kernel step). -/
scoped macro "ifB " c:term " then " t:term " else " e:term : term =>
  `(Bool.casesOn (motive := fun _ => Nat) $c $e $t)

open Lean in
/-- Same at type `Bool`. -/
scoped macro "ifBB " c:term " then " t:term " else " e:term : term =>
  `(Bool.casesOn (motive := fun _ => Bool) $c $e $t)

/-! ## Fast `log2` and `sqrt` (a guess, then a check, so correctness is trivial) -/

/-- `∑ j < 128, 2 ^ (129 j)`. -/
def ones128 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 16512) 1) (Nat.sub (Nat.shiftLeft 1 129) 1)
/-- `∑ j < 128, (2 ^ 128 - 2 ^ j) 2 ^ (129 j)`. -/
def offs128 : Nat :=
  Nat.sub (Nat.shiftLeft ones128 128)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 16640) 1) (Nat.sub (Nat.shiftLeft 1 130) 1))

/-- Bit length of `n < 2 ^ 128` by the lane method (FloatLib's `laneLength`). Not trusted. -/
def len128 (n : Nat) : Nat :=
  Nat.mod (Nat.land (Nat.shiftRight (Nat.add (Nat.mul n ones128) offs128) 128) ones128)
    (Nat.sub (Nat.shiftLeft 1 129) 1)

/-- Bit length guess for `n < 2 ^ 4096` (binary search down to a 128-bit window). -/
def len256 (n : Nat) : Nat :=
  (fun u => ifB Nat.beq u 0 then len128 n else Nat.add 128 (len128 u)) (Nat.shiftRight n 128)
def len512 (n : Nat) : Nat :=
  (fun u => ifB Nat.beq u 0 then len256 n else Nat.add 256 (len256 u)) (Nat.shiftRight n 256)
def len1024 (n : Nat) : Nat :=
  (fun u => ifB Nat.beq u 0 then len512 n else Nat.add 512 (len512 u)) (Nat.shiftRight n 512)
def len2048 (n : Nat) : Nat :=
  (fun u => ifB Nat.beq u 0 then len1024 n else Nat.add 1024 (len1024 u)) (Nat.shiftRight n 1024)
def len4096 (n : Nat) : Nat :=
  (fun u => ifB Nat.beq u 0 then len2048 n else Nat.add 2048 (len2048 u)) (Nat.shiftRight n 2048)

/-- Guess for `Nat.log2 n`. Not trusted. -/
def lgGuess (n : Nat) : Nat :=
  Nat.sub (ifB Nat.ble (Nat.shiftLeft 1 128) n then len4096 n else len128 n) 1

/-- `Nat.log2 n`: the guess if it passes the check `2^k ≤ n < 2^(k+1)`, else `Nat.log2`. -/
def lg (n : Nat) : Nat :=
  (fun k =>
    ifB (Nat.ble (Nat.shiftLeft 1 k) n && Nat.blt n (Nat.shiftLeft 1 (Nat.succ k)))
    then k else Nat.log2 n) (lgGuess n)

/-- Newton step `⌊(g + n / g) / 2⌋`. -/
def newton (n g : Nat) : Nat := Nat.div (Nat.add g (Nat.div n g)) 2

/-- Guess for `Nat.sqrt n`, `n < 2 ^ 128`: 7 Newton steps from `2^(⌊lg/2⌋+1)`. Not trusted. -/
def isqrtGuess (n : Nat) : Nat :=
  (fun g => newton n (newton n (newton n (newton n (newton n (newton n (newton n g)))))))
    (Nat.shiftLeft 1 (Nat.succ (Nat.div (lg n) 2)))

/-- Fix up a guess that is one too large (Newton from above ends at `⌊√n⌋` or `⌊√n⌋ + 1`). -/
def isqrtFix (n g : Nat) : Nat :=
  ifB Nat.blt n (Nat.mul g g) then Nat.sub g 1 else g

/-- `Nat.sqrt n`: the guess if it passes `r² ≤ n < (r+1)²`, else `Nat.sqrt`. -/
def isqrt (n : Nat) : Nat :=
  (fun r =>
    ifB (Nat.ble (Nat.mul r r) n && Nat.blt n (Nat.mul (Nat.succ r) (Nat.succ r)))
    then r else Nat.sqrt n) (isqrtFix n (isqrtGuess n))

/-! ## Constants and fields of a binary64 bit pattern `n < 2^64` -/

def qNaN : Nat := 0x7FF8000000000000
def infBits : Nat := 0x7FF0000000000000
def maxBits : Nat := 0x7FEFFFFFFFFFFFFF
def signBit : Nat := 0x8000000000000000
def two52 : Nat := 0x10000000000000
def two53 : Nat := 0x20000000000000

/-- Sign bit (0 or 1). -/
def sgn (n : Nat) : Nat := Nat.shiftRight n 63
/-- Magnitude bits (exponent and fraction fields). -/
def magB (n : Nat) : Nat := Nat.land n 0x7FFFFFFFFFFFFFFF
/-- Biased exponent field. -/
def ex (n : Nat) : Nat := Nat.shiftRight (magB n) 52
/-- Fraction field. -/
def fr (n : Nat) : Nat := Nat.land n 0xFFFFFFFFFFFFF

def isNaN (n : Nat) : Bool := Nat.blt infBits (magB n)
def isInf (n : Nat) : Bool := Nat.beq (magB n) infBits
def isZero (n : Nat) : Bool := Nat.beq (magB n) 0
/-- Significand (with the implicit bit for normals). -/
def mant (n : Nat) : Nat := ifB Nat.beq (ex n) 0 then fr n else Nat.add (fr n) two52
/-- Exponent of the significand's unit, biased by 1075 (`e = q - 1075`, `q ≥ 1`). -/
def qexp (n : Nat) : Nat := ifB Nat.beq (ex n) 0 then 1 else ex n

/-- Bits of a signed zero / infinity. -/
def zeroOf (s : Nat) : Nat := Nat.mul s signBit
def infOf (s : Nat) : Nat := Nat.add (Nat.mul s signBit) infBits

/-- Rounding moves away from zero (toward +∞ for positive with `up`, toward −∞ for negative
    with `!up`). -/
def away (up : Bool) (s : Nat) : Bool := Bool.xor up (Nat.beq s 1)

def maxN (a b : Nat) : Nat := ifB Nat.ble a b then b else a
def minN (a b : Nat) : Nat := ifB Nat.ble a b then a else b

/-! ## Rounding and packing

`roundPack s m E inex up` is `packDirected up (roundDirected s m (E - 4096) acc up)` for
`m > 0`, where `inex` says whether `acc` is inexact. -/

/-- Target (canonical) exponent, biased by 4096. `3022 = 4096 - 1074`. -/
def tgt (m E : Nat) : Nat := maxN (Nat.sub (Nat.add (Nat.add (lg m) 1) E) 53) 3022

/-- Final packing of a rounded significand `Mf` with biased exponent `Ef` (`Mf > 0`). -/
def packF (s Mf Ef : Nat) (up : Bool) : Nat :=
  (fun biased =>
    ifB Nat.ble 2047 biased then
      (ifB away up s then infOf s else Nat.add (Nat.mul s signBit) maxBits)
    else ifB (Nat.ble two52 Mf && Nat.blt Mf two53) then
      Nat.add (Nat.add (Nat.mul s signBit) (Nat.mul (Nat.mod biased 2048) two52)) (Nat.mod Mf two52)
    else Nat.add (Nat.mul s signBit) (Nat.mod Mf two52))
  (Nat.sub Ef 3021)

/-- Second shift (after a rounding carry) and packing. -/
def finish (s R E1 : Nat) (up : Bool) : Nat :=
  (fun n2 =>
    (fun Mf => ifB Nat.beq Mf 0 then zeroOf s else packF s Mf (Nat.add E1 n2) up)
    (Nat.shiftRight R n2))
  (Nat.sub (tgt R E1) E1)

def roundPack (s m E : Nat) (inex up : Bool) : Nat :=
  (fun T =>
    (fun M0 E0 =>
      (fun n =>
        (fun Q lost =>
          finish s (ifB (lost && away up s) then Nat.succ Q else Q) (Nat.add E0 n) up)
        (Nat.shiftRight M0 n)
        (inex || !Nat.beq (Nat.mod M0 (Nat.shiftLeft 1 n)) 0))
      (Nat.sub T E0))
    (ifB inex then m else Nat.shiftLeft m (Nat.sub E T))
    (ifB inex then E else minN E T))
  (tgt m E)

/-! ## Operations on bit patterns -/

/-- Sign of the product / quotient. -/
def xs (a b : Nat) : Nat := Nat.xor (sgn a) (sgn b)

def mulFin (a b : Nat) (up : Bool) : Nat :=
  roundPack (xs a b) (Nat.mul (mant a) (mant b)) (Nat.add (Nat.add (qexp a) (qexp b)) 1946) false up

def mul (a b : Nat) (up : Bool) : Nat :=
  ifB (isNaN a || isNaN b) then qNaN
  else ifB isInf a then (ifB isZero b then qNaN else infOf (xs a b))
  else ifB isInf b then (ifB isZero a then qNaN else infOf (xs a b))
  else ifB (isZero a || isZero b) then zeroOf (xs a b)
  else mulFin a b up

/-- Sign of an exact zero sum of opposite signs (`cancelZero`). -/
def cancelSign (up : Bool) : Nat := ifB up then 0 else 1

def addFin (a b : Nat) (up : Bool) : Nat :=
  (fun q =>
    (fun A B =>
      ifB Nat.beq (sgn a) (sgn b) then roundPack (sgn a) (Nat.add A B) (Nat.add q 3021) false up
      else ifB Nat.blt B A then roundPack (sgn a) (Nat.sub A B) (Nat.add q 3021) false up
      else ifB Nat.blt A B then roundPack (sgn b) (Nat.sub B A) (Nat.add q 3021) false up
      else zeroOf (cancelSign up))
    (Nat.shiftLeft (mant a) (Nat.sub (qexp a) q))
    (Nat.shiftLeft (mant b) (Nat.sub (qexp b) q)))
  (minN (qexp a) (qexp b))

def add (a b : Nat) (up : Bool) : Nat :=
  ifB (isNaN a || isNaN b) then qNaN
  else ifB isInf a then (ifB (isInf b && !Nat.beq (sgn a) (sgn b)) then qNaN else infOf (sgn a))
  else ifB isInf b then infOf (sgn b)
  else ifB isZero a then
    (ifB isZero b then
      (ifB Nat.beq (sgn a) (sgn b) then zeroOf (sgn a) else zeroOf (cancelSign up))
     else b)
  else ifB isZero b then a
  else addFin a b up

/-- Flip the sign bit. -/
def negBits (b : Nat) : Nat := Nat.xor b signBit

def sub (a b : Nat) (up : Bool) : Nat := add a (negBits b) up

def divFin (a b : Nat) (up : Bool) : Nat :=
  (fun m₁ m₂ q₁ q₂ =>
    (fun d =>
      (fun te =>
        (fun m => roundPack (xs a b) (Nat.div m m₂) te (!Nat.beq (Nat.mod m m₂) 0) up)
        (Nat.shiftLeft m₁ (Nat.sub d te)))
      (minN d (maxN (Nat.sub (Nat.sub (Nat.add (Nat.add (lg m₁) q₁) 4096) (Nat.add (lg m₂) q₂)) 53)
        3022)))
    (Nat.sub (Nat.add q₁ 4096) q₂))
  (mant a) (mant b) (qexp a) (qexp b)

def div (a b : Nat) (up : Bool) : Nat :=
  ifB (isNaN a || isNaN b) then qNaN
  else ifB isInf a then (ifB isInf b then qNaN else infOf (xs a b))
  else ifB isInf b then zeroOf (xs a b)
  else ifB isZero b then (ifB isZero a then qNaN else infOf (xs a b))
  else ifB isZero a then zeroOf (xs a b)
  else divFin a b up

def sqrtFin (a : Nat) (up : Bool) : Nat :=
  (fun m q =>
    (fun te =>
      (fun m' => (fun r => roundPack 0 r te (!Nat.beq (Nat.sub m' (Nat.mul r r)) 0) up) (isqrt m'))
      (Nat.shiftLeft m (Nat.sub (Nat.add q 7117) (Nat.mul 2 te))))
    (minN (Nat.add (Nat.div (Nat.add q 1125) 2) 2996)
      (maxN (Nat.add (Nat.div (Nat.add (Nat.add (lg m) q) 1127) 2) 2943) 3022)))
  (mant a) (qexp a)

def sqrt (a : Nat) (up : Bool) : Nat :=
  ifB isNaN a then qNaN
  else ifB isInf a then (ifB Nat.beq (sgn a) 0 then infBits else qNaN)
  else ifB isZero a then a
  else ifB Nat.beq (sgn a) 1 then qNaN
  else sqrtFin a up

/-! ## Comparisons (IEEE: NaN unordered, `-0 = +0`) -/

/-- Lexicographic on (exponent, significand), as `UnpackedFloat.compare`: 0/1/2 = lt/eq/gt. -/
def cmpMag (a b : Nat) : Nat :=
  ifB Nat.blt (qexp a) (qexp b) then 0 else ifB Nat.blt (qexp b) (qexp a) then 2
  else ifB Nat.blt (mant a) (mant b) then 0 else ifB Nat.blt (mant b) (mant a) then 2 else 1

/-- IEEE comparison code: 0 = lt, 1 = eq, 2 = gt, 3 = unordered. -/
def cmp (a b : Nat) : Nat :=
  ifB (isNaN a || isNaN b) then 3
  else ifB isInf a then
    (ifB isInf b then
      (ifB Nat.beq (sgn a) (sgn b) then 1 else ifB Nat.beq (sgn a) 1 then 0 else 2)
     else ifB Nat.beq (sgn a) 0 then 2 else 0)
  else ifB isInf b then (ifB Nat.beq (sgn b) 0 then 0 else 2)
  else ifB isZero a then
    (ifB isZero b then 1 else ifB Nat.beq (sgn b) 0 then 0 else 2)
  else ifB isZero b then (ifB Nat.beq (sgn a) 0 then 2 else 0)
  else ifB Nat.beq (sgn a) 1 then (ifB Nat.beq (sgn b) 1 then Nat.sub 2 (cmpMag a b) else 0)
  else ifB Nat.beq (sgn b) 1 then 2 else cmpMag a b

def lt (a b : Nat) : Bool := Nat.beq (cmp a b) 0
def le (a b : Nat) : Bool := Nat.blt (cmp a b) 2
def beq (a b : Nat) : Bool := Nat.beq (cmp a b) 1

end Interval64.KF
