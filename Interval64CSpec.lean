/-
Lean-only reference copies of the specifications that run in C at runtime, for the differential
tests (`Interval64Test.lean`) and benchmarks (`Interval64Bench.lean`).
-/
import Interval64

open Interval64

namespace CSpec

def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

end CSpec

/-! ### C kernels (poly / Bernstein / quadrature) vs the Lean specifications

The `…S` functions below are literal copies of the specification bodies of the definitions
that carry `@[implemented_by]` (with every nested attached call replaced by its copy), so they
run in Lean only; the C results must agree bit for bit (`sameIv`). -/

namespace CSpec
open Interval64.IPoly Interval64.KF

def evalS (P : IPoly) (X : Interval64) : Interval64 := hornerAux P.coeff X 0 P.size
def evalMVS (P dP : IPoly) (X : Interval64) : Interval64 :=
  let m := mid X
  let H := evalS P X
  if m.isInf then H else intersect H (evalS P (point m) + evalS dP X * (X - point m))
def rangeAuxS (P dP : IPoly) : Nat → Interval64 → Interval64
  | 0, X => evalMVS P dP X
  | fuel + 1, X => hull (rangeAuxS P dP fuel (bisect X).1) (rangeAuxS P dP fuel (bisect X).2)
def checkAuxS (P dP : IPoly) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (evalMVS P dP X)
  | fuel + 1, X => g (evalMVS P dP X) || (checkAuxS P dP g fuel (bisect X).1 && checkAuxS P dP g fuel (bisect X).2)
def goal (mode : Nat) (c : Float) (R : Interval64) : Bool :=
  match mode with
  | 0 => decide (c ≤ R.lo) | 1 => decide (c < R.lo) | 2 => decide (R.hi ≤ c) | _ => decide (R.hi < c)
def checkS (mode : Nat) (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxS P (deriv P) (goal mode c) fuel X
def eval2S (P : IPoly2) (X Y : Interval64) : Interval64 :=
  hornerAux (fun j => evalS (P.coeff j) X) Y 0 P.size
def checkAux2S (P : IPoly2) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (eval2S P X Y)
  | fuel + 1, X, Y => g (eval2S P X Y) ||
      (if decide (width Y ≤ width X) then checkAux2S P g fuel (bisect X).1 Y && checkAux2S P g fuel (bisect X).2 Y
       else checkAux2S P g fuel X (bisect Y).1 && checkAux2S P g fuel X (bisect Y).2)
def bernOnS (P : IPoly) (X : Interval64) (n : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then bern01 (P.comp #[point X.lo, point X.hi - point X.lo]) n
  else evalS P X
def bernRangeS (P : IPoly) (n : Nat) : Nat → Interval64 → Interval64
  | 0, X => bernOnS P X n
  | fuel + 1, X => hull (bernRangeS P n fuel (bisect X).1) (bernRangeS P n fuel (bisect X).2)
def checkAuxBS (P : IPoly) (n : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (bernOnS P X n)
  | fuel + 1, X => g (bernOnS P X n) || (checkAuxBS P n g fuel (bisect X).1 && checkAuxBS P n g fuel (bisect X).2)
def bern2OnS (P : IPoly2) (X Y : Interval64) (n m : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then
    let Q : IPoly2 := P.map fun Pj => Pj.comp #[point X.lo, point X.hi - point X.lo]
    let N := max n (IPoly2.maxSize Q - 1)
    hullUpTo (fun k => bernOnS (ofFn Q.size fun j => bernCoeffF (Q.coeff j).coeff N k) Y m) N
  else eval2S P X Y
def checkAux2BS (P : IPoly2) (n m : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (bern2OnS P X Y n m)
  | fuel + 1, X, Y => g (bern2OnS P X Y n m) ||
      (checkAux2BS P n m g fuel (bisect X).1 (bisect Y).1 && checkAux2BS P n m g fuel (bisect X).1 (bisect Y).2 &&
       checkAux2BS P n m g fuel (bisect X).2 (bisect Y).1 && checkAux2BS P n m g fuel (bisect X).2 (bisect Y).2)
def integrateE0S (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell0 fun X => evalI [X] e) a b tol fuel
def integrateE1S (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell1 (fun X => evalI [X] e) (fun X => evalI [X] (e.diff 0))) a b tol fuel
def integrate2E0S (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel
def integrate2E1S (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell0 fun X =>
    Quad.integrate (Quad.cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel) a b tol fuel

/-- Random expression in variables `0 .. nv-1`. -/
partial def randExpr (nv : Nat) (s : UInt64) : Nat → IExpr × UInt64
  | 0 =>
    let s := xorshift s
    if s % 3 == 0 then (.rat ((((xorshift s) % 41).toNat : Rat) / 8 - 2), xorshift s)
    else (.var ((s / 3 % nv.toUInt64).toNat), s)
  | d + 1 =>
    let s := xorshift s
    let k := (s % 22).toNat
    let (a, s) := randExpr nv s d
    let (b, s) := randExpr nv s (d / 2)
    let e : IExpr := match k with
      | 0 => .add a b | 1 => .sub a b | 2 => .mul a b | 3 => .div a b | 4 => .neg a
      | 5 => .inv a | 6 => .sqrt a | 7 => .abs a | 8 => .pow a ((s % 5).toNat) | 9 => .exp a
      | 10 => .log a | 11 => .sin a | 12 => .cos a | 13 => .atan a | 14 => .sinh a
      | 15 => .tanh a | 16 => .tan a | 17 => .asin a | 18 => .atan2 a b | 19 => .add a .pi
      | 20 => .mul a a | _ => .cosh a
    (e, s)
end CSpec
