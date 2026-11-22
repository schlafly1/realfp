/-
Kernel-checkable Taylor quadrature (`decide +kernel` on `KF`/`KI` bit-pattern arithmetic).

For `f x = e.denote [x]`, derivatives `d₀ = e`, `d_{j+1} = d_j.deriv 0`, an even order `K`, and a
partition of `[a, b]` into cells `(lo, m, hi)` (`lo ≤ m ≤ hi`, all finite bit patterns), the cell
enclosure is

  `Σ_{j<K} d_j(m) · ∫_lo^hi (x-m)^j/j! dx  +  d_K([lo, hi]) · ∫_lo^hi (x-m)^K/K! dx`

(Taylor with Lagrange remainder; `K > 0` even so the remainder weight is `≥ 0`). The moments are
`((hi-m)^{j+1} - (lo-m)^{j+1}) / (j+1)!`, enclosed with outward rounding. The error per cell is
`O(width(d_K([lo,hi])) · h^{K+1})`, i.e. `O(h^{K+2})`; the total `O(h^{K+1})`.
Soundness: `RealFP.KQ.integral_mem_quadK` (Mathlib layer). The partition is untrusted
(`uniformCells` computes one natively).
-/
import Interval64.Kernel.Deriv
import Interval64.Tape

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
  if Nat.beq (K % 2) 0 && Nat.blt 0 K && chainOK a b cs && cs.all (cellOK ds) then some (sumCells ds K dK cs)
  else none

/-- Check `lo ≤ ∫ ≤ hi` style goals: `g` applied to the enclosure. -/
def quadCheck (e : IExpr) (K a b : Nat) (cs : List (Nat × Nat × Nat)) (g : KI → Bool) : Bool :=
  match quadK e K a b cs with
  | some R => g R
  | none => false

/-- The rational value of a finite, non-NaN bit pattern. -/
def ratOf (p : Nat) : Option Rat :=
  if Nat.blt p (2 ^ 64) && !isNaN p then Spec.bitsToRat? (UInt64.ofNat p) else none

/-- `ql ≤ ∫_qa^qb e ≤ qh`, with `a`, `b` bit patterns of `qa`, `qb` (checked). -/
def quadBound (e : IExpr) (K a b : Nat) (cs : List (Nat × Nat × Nat)) (qa qb ql qh : Rat) : Bool :=
  decide (ratOf a = some qa) && decide (ratOf b = some qb) &&
  match quadK e K a b cs with
  | some R =>
    match ratOf R.lo, ratOf R.hi with
    | some l, some h => decide (ql ≤ l) && decide (h ≤ qh)
    | _, _ => false
  | none => false

/-! ### `Interval64` (Float) mirror, for native search

`quadF e K cs` performs the same `Interval64` operations as `quadK` (via `evalI`, which equals
`evalK` under `toI`: `evalK_toI`), on `Float` cells; at runtime it runs in C over a tape
(`iv64_quad_taylor`). Untrusted: the tactic only uses it to choose a certificate, which the
kernel then checks with `quadK`. -/

def ptF (x : Float) : Interval64 := ⟨x, x⟩

def momF (lo m hi : Float) (j : Nat) : Interval64 :=
  (pown (ptF hi - ptF m) (j + 1) - pown (ptF lo - ptF m) (j + 1)) *
    ofRat (1 / (fact (j + 1) : Rat))

def taylorF (lo m hi : Float) : Nat → List IExpr → Interval64
  | _, [] => zeroI
  | _, [_] => zeroI
  | j, d :: ds => evalI [ptF m] d * momF lo m hi j + taylorF lo m hi (j + 1) ds

def cellFSpec (ds : List IExpr) (K : Nat) (dK : IExpr) (c : Float × Float × Float) : Interval64 :=
  taylorF c.1 c.2.1 c.2.2 0 ds + evalI [⟨c.1, c.2.2⟩] dK * momF c.1 c.2.1 c.2.2 K

def sumF (ds : List IExpr) (K : Nat) (dK : IExpr) : List (Float × Float × Float) → Interval64
  | [] => zeroI
  | c :: cs => cellFSpec ds K dK c + sumF ds K dK cs

def quadFSpec (e : IExpr) (K : Nat) (cs : List (Float × Float × Float)) : Interval64 :=
  let ds := derivs e K
  sumF ds K (ds.getLastD e) cs

@[extern "iv64_quad_taylor"]
opaque quadTaylorExt (code : @& ByteArray) (consts : @& FloatArray)
  (fns : @& Array (Interval64 → Interval64)) (atan2 : @& (Interval64 → Interval64 → Interval64))
  (roots : @& ByteArray) (cells : @& FloatArray) : Interval64

@[extern "iv64_quad_taylor_cell"]
opaque quadTaylorCellExt (code : @& ByteArray) (consts : @& FloatArray)
  (fns : @& Array (Interval64 → Interval64)) (atan2 : @& (Interval64 → Interval64 → Interval64))
  (roots : @& ByteArray) (lo m hi : Float) : Interval64

def cellsArr (cs : List (Float × Float × Float)) : FloatArray :=
  cs.foldl (fun a c => ((a.push c.1).push c.2.1).push c.2.2) FloatArray.empty

/-- Tape of `d_0, …, d_K` (C needs `(K+1)! < 2^53`). -/
def derivTape (e : IExpr) (K : Nat) : Option Tape.Tape :=
  if K ≤ 17 then Tape.compile (derivs e K) else none

def quadFImpl (e : IExpr) (K : Nat) (cs : List (Float × Float × Float)) : Interval64 :=
  match derivTape e K with
  | some t => quadTaylorExt t.code t.consts Tape.unaryFns Tape.atan2Fn t.rootBytes (cellsArr cs)
  | none => quadFSpec e K cs

/-- Taylor quadrature on `Interval64` (C at runtime). -/
@[implemented_by quadFImpl]
def quadF (e : IExpr) (K : Nat) (cs : List (Float × Float × Float)) : Interval64 := quadFSpec e K cs

/-- One cell with a precompiled tape (for adaptive partitioning). -/
def cellTape (t : Tape.Tape) (c : Float × Float × Float) : Interval64 :=
  quadTaylorCellExt t.code t.consts Tape.unaryFns Tape.atan2Fn t.rootBytes c.1 c.2.1 c.2.2

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
