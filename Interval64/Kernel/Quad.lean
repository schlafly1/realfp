/-
Kernel-checkable Taylor quadrature (`decide +kernel` on `KF`/`KI` bit-pattern arithmetic).

For `f x = e.denote [x]`, derivatives `d₀ = e`, `d_{j+1} = d_j.deriv 0`, an even order `K`, and a
partition of `[a, b]` into cells `(lo, m, hi)` (`lo ≤ m ≤ hi`, all finite bit patterns), the cell
enclosure is

  `Σ_{j<K} d_j(m) · ∫_lo^hi (x-m)^j/j! dx  +  d_K([lo, hi]) · ∫_lo^hi (x-m)^K/K! dx`

(Taylor with Lagrange remainder; `K` even so the remainder weight is `≥ 0`). The moments are
`((hi-m)^{j+1} - (lo-m)^{j+1}) / (j+1)!`, enclosed with outward rounding. The error per cell is
`O(width(d_K([lo,hi])) · h^{K+1})`, i.e. `O(h^{K+2})`; the total `O(h^{K+1})`.
Soundness: `RealFP.KQ.integral_mem_quadK` (Mathlib layer). The partition is untrusted
(`uniformCells` computes one natively).
-/
import Interval64.Kernel.Deriv

namespace Interval64.KF.KQ

open Interval64.KF

/-- `[e, e', …, e^{(K)}]` (derivatives in variable `0`). -/
def derivs (e : IExpr) : Nat → List IExpr
  | 0 => [e]
  | k + 1 => e :: derivs (e.deriv 0) k

def pt (p : Nat) : KI := ⟨p, p⟩

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Enclosure of `∫_lo^hi (x - m)^j / j! dx = ((hi-m)^{j+1} - (lo-m)^{j+1}) / (j+1)!`. -/
def momK (lo m hi j : Nat) : KI :=
  KI.mul (KI.sub (KI.pown (KI.sub (pt hi) (pt m)) (j + 1)) (KI.pown (KI.sub (pt lo) (pt m)) (j + 1)))
    (KI.ofRat (1 / (fact (j + 1) : Rat)))

/-- Taylor part `Σ_{j<K} d_j(m) · mom_j` (over the list of derivatives, `j` counting up). -/
def taylorK (lo m hi : Nat) : Nat → List IExpr → KI
  | _, [] => zeroK
  | _, [_] => zeroK
  | j, d :: ds => KI.add (KI.mul (evalK [pt m] d) (momK lo m hi j)) (taylorK lo m hi (j + 1) ds)

/-- Remainder term `d_K([lo, hi]) · mom_K`. -/
def remK (lo m hi K : Nat) (dK : IExpr) : KI := KI.mul (evalK [⟨lo, hi⟩] dK) (momK lo m hi K)

/-- One cell. -/
def cellK (ds : List IExpr) (K : Nat) (dK : IExpr) (c : Nat × Nat × Nat) : KI :=
  KI.add (taylorK c.1 c.2.1 c.2.2 0 ds) (remK c.1 c.2.1 c.2.2 K dK)

/-- Validity of one cell: finite bit patterns `lo ≤ m ≤ hi`, and the derivatives `d_j`, `j < K`,
    are defined (`domOK`) on `[lo, hi]`. -/
def cellOK (ds : List IExpr) (c : Nat × Nat × Nat) : Bool :=
  finK c.1 && finK c.2.1 && finK c.2.2 && le c.1 c.2.1 && le c.2.1 c.2.2 &&
    (ds.dropLast).all fun d => domOK [⟨c.1, c.2.2⟩] d

/-- The cells chain from `a` to `b`. -/
def chainOK : Nat → Nat → List (Nat × Nat × Nat) → Bool
  | a, b, [] => Nat.beq a b
  | a, b, c :: cs => Nat.beq a c.1 && chainOK c.2.2 b cs

/-- Sum of the cell enclosures. -/
def sumCells (ds : List IExpr) (K : Nat) (dK : IExpr) : List (Nat × Nat × Nat) → KI
  | [] => zeroK
  | c :: cs => KI.add (cellK ds K dK c) (sumCells ds K dK cs)

/-- The quadrature enclosure of `∫_a^b e` (order `K`, cells `cs`) if the certificate is valid. -/
def quadK (e : IExpr) (K : Nat) (a b : Nat) (cs : List (Nat × Nat × Nat)) : Option KI :=
  let ds := derivs e K
  let dK := ds.getLastD e
  if Nat.beq (K % 2) 0 && chainOK a b cs && cs.all (cellOK ds) then some (sumCells ds K dK cs)
  else none

/-- Check `lo ≤ ∫ ≤ hi` style goals: `g` applied to the enclosure. -/
def quadCheck (e : IExpr) (K a b : Nat) (cs : List (Nat × Nat × Nat)) (g : KI → Bool) : Bool :=
  match quadK e K a b cs with
  | some R => g R
  | none => false

/-! ### Untrusted helpers -/

def toFl (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)
def bitsOf (x : Float) : Nat := x.toBits.toNat

/-- `N` equal cells on `[a, b]` (midpoints as cell points). -/
def uniformCells (a b : Float) (N : Nat) : List (Nat × Nat × Nat) :=
  let h := (b - a) / Float.ofNat N
  let pts := (List.range (N + 1)).map fun k => if k = N then b else a + Float.ofNat k * h
  (List.range N).map fun k =>
    let lo := pts.getD k a
    let hi := pts.getD (k + 1) b
    (bitsOf lo, bitsOf (0.5 * lo + 0.5 * hi), bitsOf hi)

end Interval64.KF.KQ
