/-
Kernel-checkable 2D Taylor rule (`decide +kernel` on `KF`/`KI` bit-pattern arithmetic).

`taylor2K` performs exactly the `Interval64` operations of `Quad.taylor2` (under `toI`), on cells
of bit patterns; `taylor2Bound` checks `ql ≤ ∫_{qa}^{qb} ∫_{qc}^{qd} e ≤ qh` including
`allSmooth e K` (so the theorem has no side conditions).
Soundness: `RealFP.KTaylor2.integral2_bounds_of_taylor2Bound` (Mathlib layer).
-/
import Interval64.Quad2

namespace Interval64.KF.KQ

open Interval64.KF Interval64.Quad

def sumK (f : Nat → KI) : Nat → KI
  | 0 => zeroK
  | n + 1 => KI.add (sumK f n) (f n)

def t2InnerK (e : IExpr) (K i : Nat) (cx : Nat × Nat × Nat) (my : Nat) : KI :=
  KI.add (sumK (fun j => KI.mul (evalK [pt cx.2.1, pt my] (dxy e i j)) (momK cx.1 cx.2.1 cx.2.2 j)) K)
    (KI.mul (evalK [⟨cx.1, cx.2.2⟩, pt my] (dxy e i K)) (momK cx.1 cx.2.1 cx.2.2 K))

def t2CellK (e : IExpr) (K : Nat) (cx cy : Nat × Nat × Nat) : KI :=
  KI.add (sumK (fun i => KI.mul (momK cy.1 cy.2.1 cy.2.2 i) (t2InnerK e K i cx cy.2.1)) K)
    (KI.mul (KI.mul (evalK [⟨cx.1, cx.2.2⟩, ⟨cy.1, cy.2.2⟩] (dxy e K 0)) (momK cy.1 cy.2.1 cy.2.2 K))
      (KI.sub (pt cx.2.2) (pt cx.1)))

def t2SumK (e : IExpr) (K : Nat) (xs ys : List (Nat × Nat × Nat)) : KI :=
  xs.foldr (fun cx acc => KI.add (ys.foldr (fun cy acc' => KI.add (t2CellK e K cx cy) acc') zeroK) acc)
    zeroK

def cellOKK (c : Nat × Nat × Nat) : Bool :=
  finK c.1 && finK c.2.1 && finK c.2.2 && le c.1 c.2.1 && le c.2.1 c.2.2

def taylor2K (e : IExpr) (K : Nat) (a b c d : Nat) (xs ys : List (Nat × Nat × Nat)) : Option KI :=
  if Nat.beq (K % 2) 0 && Nat.blt 0 K && chainOK a b xs && chainOK c d ys && xs.all cellOKK &&
      ys.all cellOKK && allSmooth e K then some (t2SumK e K xs ys)
  else none

/-- `ql ≤ ∫_{qa}^{qb} ∫_{qc}^{qd} e(x, y) dy dx ≤ qh` (bit patterns `a b c d` of `qa qb qc qd`). -/
def taylor2Bound (e : IExpr) (K a b c d : Nat) (xs ys : List (Nat × Nat × Nat))
    (qa qb qc qd ql qh : Rat) : Bool :=
  decide (ratOf a = some qa) && decide (ratOf b = some qb) && decide (ratOf c = some qc) &&
  decide (ratOf d = some qd) &&
  match taylor2K e K a b c d xs ys with
  | some R =>
    match ratOf R.lo, ratOf R.hi with
    | some l, some h => decide (ql ≤ l) && decide (h ≤ qh)
    | _, _ => false
  | none => false

end Interval64.KF.KQ
