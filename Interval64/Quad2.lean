/-
Rigorous 2D quadrature over rectangles (iterated integrals `∫_a^b ∫_c^d f x y dy dx`).

* `integrate2 F a b c d tol fuel` : outer adaptive zeroth-order rule in `x` whose integrand
  enclosure on a cell `X` is the inner adaptive rule in `y` for `Y ↦ F X Y`.
* `integrate2E0 e …` : `IExpr` in variables `0` (`x`) and `1` (`y`), zeroth-order cells.
* `integrate2E1 e …` : inner second-order cells in `y` (derivative `e.diff 1`), outer zeroth order.
At runtime `integrate2E0` / `integrate2E1` run in C over a tape (`c/iv64_quad.h`).
* `taylor2 e K a b c d xs ys` : higher-order (Taylor) rule on the grid `xs × ys` of cells
  `(lo, m, hi)`: on each cell, order-`K` Taylor in `y` around `m_y` (Lagrange remainder enclosed on
  the cell), and order-`K` Taylor in `x` around `m_x` for each `y`-coefficient; error
  `O(h^{K+1})` per unit area. Soundness `RealFP.Taylor2.integral2_mem_taylor2`.
Soundness: `RealFP.Quad2` (Mathlib layer), with Fubini (`setIntegral_rect_eq`).
-/
import Interval64.Quad
import Interval64.Kernel.Quad

namespace Interval64.Quad

open Interval64.KF (IExpr evalI)

def integrate2 (F : Interval64 → Interval64 → Interval64) (a b c d tol : Float) (fuel : Nat) :
    Interval64 :=
  integrate (cell0 fun X => integrate (cell0 (F X)) c d tol fuel) a b tol fuel

@[extern "iv64_quad_integrate2"]
opaque integrate2TapeExt (code : @& ByteArray) (consts : @& FloatArray)
  (fns : @& Array (Interval64 → Interval64)) (atan2 : @& (Interval64 → Interval64 → Interval64))
  (rF rD : UInt32) (order : UInt8) (a b c d tol : Float) (fuel : @& Nat) : Interval64

def integrate2E0Impl (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  match KF.Tape.compile [e] with
  | some t => integrate2TapeExt t.code t.consts KF.Tape.unaryFns KF.Tape.atan2Fn t.roots[0]!
      t.roots[0]! 0 a b c d tol fuel
  | none => integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel

def integrate2E1Impl (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  match KF.Tape.compile [e, e.diff 1] with
  | some t => integrate2TapeExt t.code t.consts KF.Tape.unaryFns KF.Tape.atan2Fn t.roots[0]!
      t.roots[1]! 1 a b c d tol fuel
  | none => integrate (cell0 fun X =>
      integrate (cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel)
      a b tol fuel

@[implemented_by integrate2E0Impl]
def integrate2E0 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel

@[implemented_by integrate2E1Impl]
def integrate2E1 (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  integrate (cell0 fun X =>
    integrate (cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel)
    a b tol fuel

/-! ### Higher-order 2D rule (tensor Taylor cells) -/

open KF.KQ (momF ptF)

/-- `n`-fold derivative in variable `v`. -/
def dIt (v : Nat) : Nat → IExpr → IExpr
  | 0, e => e
  | n + 1, e => (dIt v n e).deriv v

/-- `∂ₓʲ ∂ᵧⁱ e` (`x` = var 0, `y` = var 1). -/
def dxy (e : IExpr) (i j : Nat) : IExpr := dIt 0 j (dIt 1 i e)

/-- `Σ_{k<n} f k`, left to right from `[0, 0]`. -/
def sumI (f : Nat → Interval64) : Nat → Interval64
  | 0 => KF.zeroI
  | n + 1 => sumI f n + f n

/-- Enclosure of `∫_{xl}^{xh} ∂ᵧⁱ e (x, m_y) dx` (order-`K` Taylor in `x` around `m_x`). -/
def t2Inner (e : IExpr) (K i : Nat) (cx : Float × Float × Float) (my : Float) : Interval64 :=
  sumI (fun j => evalI [ptF cx.2.1, ptF my] (dxy e i j) * momF cx.1 cx.2.1 cx.2.2 j) K +
    evalI [⟨cx.1, cx.2.2⟩, ptF my] (dxy e i K) * momF cx.1 cx.2.1 cx.2.2 K

/-- Enclosure of `∫_{cx} ∫_{cy} e` on one cell. -/
def t2Cell (e : IExpr) (K : Nat) (cx cy : Float × Float × Float) : Interval64 :=
  sumI (fun i => momF cy.1 cy.2.1 cy.2.2 i * t2Inner e K i cx cy.2.1) K +
    (evalI [⟨cx.1, cx.2.2⟩, ⟨cy.1, cy.2.2⟩] (dxy e K 0) * momF cy.1 cy.2.1 cy.2.2 K) *
      (ptF cx.2.2 - ptF cx.1)

/-- Finite `lo ≤ m ≤ hi`. -/
def cellOKF (c : Float × Float × Float) : Bool :=
  finite c.1 && finite c.2.1 && finite c.2.2 && decide (c.1 ≤ c.2.1) && decide (c.2.1 ≤ c.2.2)

/-- The cells chain from `a` to `b` (equal bit patterns at the joins). -/
def chainF : Float → Float → List (Float × Float × Float) → Bool
  | a, b, [] => a.toBits == b.toBits
  | a, b, c :: cs => a.toBits == c.1.toBits && chainF c.2.2 b cs

def t2Sum (e : IExpr) (K : Nat) (xs ys : List (Float × Float × Float)) : Interval64 :=
  xs.foldr (fun cx acc => ys.foldr (fun cy acc' => t2Cell e K cx cy + acc') KF.zeroI + acc) KF.zeroI

def t2OK (K : Nat) (a b c d : Float) (xs ys : List (Float × Float × Float)) : Bool :=
  K % 2 == 0 && decide (0 < K) && chainF a b xs && chainF c d ys && xs.all cellOKF && ys.all cellOKF

@[extern "iv64_quad_taylor2"]
opaque taylor2Ext (code : @& ByteArray) (consts : @& FloatArray)
  (fns : @& Array (Interval64 → Interval64)) (atan2 : @& (Interval64 → Interval64 → Interval64))
  (roots : @& ByteArray) (K : @& Nat) (xs ys : @& FloatArray) : Interval64

/-- Tape of `dxy e i j` for `i < K, j ≤ K` (root `i * (K+1) + j`) and `dxy e K 0` (last). -/
def t2Tape (e : IExpr) (K : Nat) : Option KF.Tape.Tape :=
  if K ≤ 17 then
    KF.Tape.compile ((List.range K).flatMap (fun i => (List.range (K + 1)).map (dxy e i)) ++ [dxy e K 0])
  else none

def taylor2Impl (e : IExpr) (K : Nat) (a b c d : Float) (xs ys : List (Float × Float × Float)) :
    Interval64 :=
  if t2OK K a b c d xs ys then
    match t2Tape e K with
    | some t => taylor2Ext t.code t.consts KF.Tape.unaryFns KF.Tape.atan2Fn t.rootBytes K
        (KF.KQ.cellsArr xs) (KF.KQ.cellsArr ys)
    | none => t2Sum e K xs ys
  else whole

/-- `∫_a^b ∫_c^d e(x, y) dy dx` by tensor Taylor cells of even order `K > 0` on the grid
    `xs × ys` (`whole` if the grid is not a valid partition). C at runtime. -/
@[implemented_by taylor2Impl]
def taylor2 (e : IExpr) (K : Nat) (a b c d : Float) (xs ys : List (Float × Float × Float)) :
    Interval64 :=
  if t2OK K a b c d xs ys then t2Sum e K xs ys else whole

/-- Structurally smooth (`Dom` everywhere): polynomial operations, `exp`, `sin`, `cos`, `atan`,
    `sinh`, `cosh`. -/
def smoothB : IExpr → Bool
  | .var _ => true
  | .rat _ => true
  | .add a b => smoothB a && smoothB b
  | .sub a b => smoothB a && smoothB b
  | .mul a b => smoothB a && smoothB b
  | .neg a => smoothB a
  | .pow a _ => smoothB a
  | .exp a => smoothB a
  | .sin a => smoothB a
  | .cos a => smoothB a
  | .pi => true
  | .atan a => smoothB a
  | .sinh a => smoothB a
  | .cosh a => smoothB a
  | _ => false

/-- All `∂ₓʲ ∂ᵧⁱ e`, `i, j ≤ K`, are `smoothB` (checkable by `decide +kernel`). -/
def allSmooth (e : IExpr) (K : Nat) : Bool :=
  (List.range (K + 1)).all fun i => (List.range (K + 1)).all fun j => smoothB (dxy e i j)

/-- `N` uniform cells on `[a, b]` (untrusted helper). -/
def ucells (a b : Float) (N : Nat) : List (Float × Float × Float) :=
  (KF.KQ.uniformCells a b N).map fun c => (KF.KQ.toFl c.1, KF.KQ.toFl c.2.1, KF.KQ.toFl c.2.2)

end Interval64.Quad
