/-
Kernel fast path for the positive-definiteness certificate (`Interval64.Mat.pdCheck`).

`pdCheckK n A X` is the `pdCheck` computation on bit patterns: `A` is the row-major interval
matrix as `KI`s, `X` the congruence as `Nat` bit patterns. It only uses `KF`/`KI` operations
(GMP `Nat` arithmetic in the kernel), so `decide +kernel` is fast. Soundness:
`RealFP.KM.posDef_of_pdCheckK` (Mathlib layer) via `toI (KI.op ..) = op (toI ..) ..`.
-/
import Interval64.Kernel.Reflect
import Interval64.Matrix

namespace Interval64.KF.KM

open Interval64.KF

def idotK (f g : Nat → KI) : Nat → KI
  | 0 => zeroK
  | k + 1 => KI.add (idotK f g k) (KI.mul (f k) (g k))

def isumSkipK (f : Nat → KI) (skip : Nat) : Nat → KI
  | 0 => zeroK
  | k + 1 => if k = skip then isumSkipK f skip k else KI.add (isumSkipK f skip k) (f k)

def aget (n : Nat) (A : Array KI) (i j : Nat) : KI := A.getD (i * n + j) zeroK

def xentK (n : Nat) (X : Array Nat) (i j : Nat) : KI :=
  let v := X.getD (i * n + j) 0
  ⟨v, v⟩

def tEntryK (n : Nat) (A : Array KI) (X : Array Nat) (i k : Nat) : KI :=
  idotK (fun j => xentK n X i j) (fun j => aget n A j k) (i + 1)

def tArrK (n : Nat) (A : Array KI) (X : Array Nat) : Array KI :=
  Array.ofFn (n := n * n) fun k => tEntryK n A X (k.val / n) (k.val % n)

def bEntryK (n : Nat) (X : Array Nat) (T : Array KI) (i l : Nat) : KI :=
  idotK (fun k => T.getD (i * n + k) zeroK) (fun k => xentK n X l k) (l + 1)

def bArrK (n : Nat) (A : Array KI) (X : Array Nat) : Array KI :=
  let T := tArrK n A X
  Array.ofFn (n := n * n) fun k =>
    if k.val % n ≤ k.val / n then bEntryK n X T (k.val / n) (k.val % n) else zeroK

def bgetK (n : Nat) (B : Array KI) (i l : Nat) : KI :=
  if l ≤ i then B.getD (i * n + l) zeroK else B.getD (l * n + i) zeroK

def marginK (n : Nat) (B : Array KI) (i : Nat) : KI :=
  KI.sub (bgetK n B i i) (isumSkipK (fun l => KI.abs (bgetK n B i l)) i n)

/-- All entries are 64-bit patterns. -/
def wfA (A : Array KI) : Bool := A.all fun a => Nat.blt a.lo (2 ^ 64) && Nat.blt a.hi (2 ^ 64)

/-- `X i j` (`j ≤ i < n`) are finite 64-bit patterns. -/
def xFiniteK (n : Nat) (X : Array Nat) : Bool :=
  (List.range n).all fun i => (List.range (i + 1)).all fun j =>
    let x := X.getD (i * n + j) 0
    Nat.blt x (2 ^ 64) && !isNaN x && !isInf x

/-- The kernel PD certificate check. -/
def pdCheckK (n : Nat) (A : Array KI) (X : Array Nat) : Bool :=
  wfA A && xFiniteK n X &&
    let B := bArrK n A X
    (List.range n).all fun i => lt 0 (marginK n B i).lo

/-! ### Linear-time kernel check with precomputed `T`, `B`

The kernel does not share the value of `T` across the entries of `B`, so `pdCheckK`
recomputes `T`. `pdCheckL` takes `T` and `B` as literals (computed natively) and checks every
entry once against its defining formula; `pdCheckL → pdCheckK` is proved. -/

structure PDCert where
  X : Array Nat
  T : Array KI
  B : Array KI

/-- Entry checks for `T` (all `i, k < n`). -/
def tOK (n : Nat) (A : Array KI) (c : PDCert) : Bool :=
  (List.range n).all fun i => (List.range n).all fun k =>
    c.T.getD (i * n + k) zeroK == tEntryK n A c.X i k

/-- Entry checks for the lower triangle of `B`. -/
def bOK (n : Nat) (c : PDCert) : Bool :=
  (List.range n).all fun i => (List.range (i + 1)).all fun l =>
    c.B.getD (i * n + l) zeroK == bEntryK n c.X c.T i l

def pdCheckL (n : Nat) (A : Array KI) (c : PDCert) : Bool :=
  wfA A && xFiniteK n c.X && tOK n A c && bOK n c &&
    (List.range n).all fun i => lt 0 (marginK n c.B i).lo

/-- `q ∈ [lo, hi]` checked through the exact values of the endpoint bit patterns
    (cheap in the kernel, unlike rounding `q` with `KI.ofRat`). -/
def memQK (q : Rat) (a : KI) : Bool :=
  Nat.blt a.lo (2 ^ 64) && Nat.blt a.hi (2 ^ 64) && !isNaN a.lo && !isNaN a.hi &&
  match Spec.bitsToRat? (UInt64.ofNat a.lo), Spec.bitsToRat? (UInt64.ofNat a.hi) with
  | some l, some h => decide (l ≤ q) && decide (q ≤ h)
  | _, _ => false

/-- Every entry `(i, j)` of `A` contains the rational `f i j`. -/
def ratMatOK (n : Nat) (A : Array KI) (f : Nat → Nat → Rat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => memQK (f i j) (aget n A i j)

/-! ### Untrusted helpers (native) -/

def toFl (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)

/-- The `IMat` read off `A`. -/
def toIMat (n : Nat) (A : Array KI) : IMat :=
  IMat.ofFn n fun i j => let a := aget n A i j; ⟨toFl a.lo, toFl a.hi⟩

/-- Default congruence as bit patterns (`approxX` of `toIMat`). -/
def approxXK (n : Nat) (A : Array KI) : Array Nat :=
  let X := Mat.approxX (toIMat n A)
  Array.ofFn (n := n * n) fun k => (fget X k.val).toBits.toNat

/-- The certificate: `X = approxXK`, `T`, `B` evaluated natively. -/
def mkCert (n : Nat) (A : Array KI) : PDCert :=
  let X := approxXK n A
  let T := tArrK n A X
  ⟨X, T, bArrK n A X⟩

/-- Row-major `KI` matrix from rational entries. -/
def ofRatFn (n : Nat) (f : Nat → Nat → Rat) : Array KI :=
  Array.ofFn (n := n * n) fun k => KI.ofRat (f (k.val / n) (k.val % n))

end Interval64.KF.KM

