import RealFPGridNative.Tape

/-! # RealFP.Grid: built-in CPU search (no external tool)

`searchGrid` builds a certificate by depth-first bisection with exactly the checker's rules
(split variable `l % d` at `midF`, leaf test `g (bitsOf (evalFE env fe))`). It is untrusted: its
output is checked like any other certificate. It is single-threaded native Lean code, about
3·10⁶ boxes/s for small expressions; the `realfp-grid` tool (`grid/`) is the fast path (CUDA or
multithreaded C). -/

open Interval64 Interval64.KF

namespace RealFP.Grid

/-- Bit accumulator: whole hex digits in `out`, the current partial digit in `cur` (`n` bits). -/
structure Bits where
  out : ByteArray := ByteArray.empty
  cur : Nat := 0
  n : Nat := 0

@[inline] def hexChar (v : Nat) : UInt8 := if v < 10 then (48 + v).toUInt8 else (87 + v).toUInt8

@[inline] def Bits.push (s : Bits) (b : Bool) : Bits :=
  let cur := 2 * s.cur + (if b then 1 else 0)
  if s.n == 3 then { out := s.out.push (hexChar cur), cur := 0, n := 0 }
  else { s with cur := cur, n := s.n + 1 }

def Bits.toHex (s : Bits) : String :=
  let out := if s.n == 0 then s.out else s.out.push (hexChar (s.cur * 2 ^ (4 - s.n)))
  String.fromUTF8! out

/-- Search state: bits so far and the number of boxes evaluated. -/
structure SearchSt where
  bits : Bits := {}
  boxes : Nat := 0

/-- Depth-first search below depth `l` (`maxDepth` total levels, `maxBoxes` evaluations).
Returns `false` (and stops) if some box fails at the depth limit or the box budget is used up. -/
partial def searchAux [ExtTbl] (fe : FExpr) (g : KI → Bool) (d maxDepth maxBoxes : Nat) (l : Nat)
    (env : Array Interval64) (st : SearchSt) : Bool × SearchSt :=
  let st := { st with boxes := st.boxes + 1 }
  if g (bitsOf (evalFE env.toList fe)) then (true, { st with bits := st.bits.push false })
  else if l ≥ maxDepth || st.boxes ≥ maxBoxes then (false, st)
  else
    let i := l % d
    let X := env.getD i zeroI
    let m := midF X.lo X.hi
    if m.isNaN then (false, st) else
    let st := { st with bits := st.bits.push true }
    let (ok, st) := searchAux fe g d maxDepth maxBoxes (l + 1) (env.set! i ⟨X.lo, m⟩) st
    if !ok then (false, st) else
    searchAux fe g d maxDepth maxBoxes (l + 1) (env.set! i ⟨m, X.hi⟩) st

/-- A certificate for `checkGrid fe upper c d 0 · env`, or `none` (with the number of boxes
tried) if none was found within the limits. -/
def searchGrid [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (env : List Interval64)
    (maxDepth maxBoxes : Nat) : Except Nat (String × Nat) :=
  let g := if upper then gLe c else gGe c
  let (ok, st) := searchAux fe g d maxDepth maxBoxes 0 env.toArray {}
  if ok then .ok (st.bits.toHex, st.boxes) else .error st.boxes

end RealFP.Grid
