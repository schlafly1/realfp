import Interval64.Kernel.Matrix
import Lean

/-! ### `pd_cert% n A`: the congruence, computed natively at elaboration time -/

namespace Interval64.KF.KM
open Lean Elab Term Meta

/-- `pd_cert% n A` elaborates to the literal `approxXK n A : Array Nat` (computed by the
    compiled/interpreted code; untrusted, it is only an input to `pdCheckK`). -/
elab "pd_cert% " n:term:max A:term:max : term => do
  let nE ← elabTermEnsuringType n (mkConst ``Nat)
  let AE ← elabTermEnsuringType A (mkApp (mkConst ``Array [Level.zero]) (mkConst ``KI))
  let e ← instantiateMVars (mkApp2 (mkConst ``approxXK) nE AE)
  let v ← unsafe evalExpr (Array Nat) (mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat)) e
  return toExpr v

instance : ToExpr KI where
  toExpr a := mkApp2 (mkConst ``KI.mk) (toExpr a.lo) (toExpr a.hi)
  toTypeExpr := mkConst ``KI

/-- `ki_lit% A` evaluates `A : Array KI` natively and elaborates to the literal array
    (so the kernel does not recompute expensive entries such as `KI.ofRat`). -/
elab "ki_lit% " A:term:max : term => do
  let ty := mkApp (mkConst ``Array [Level.zero]) (mkConst ``KI)
  let AE ← instantiateMVars (← elabTermEnsuringType A ty)
  let v ← unsafe evalExpr (Array KI) ty AE
  return toExpr v

instance : ToExpr PDCert where
  toExpr c := mkApp3 (mkConst ``PDCert.mk) (toExpr c.X) (toExpr c.T) (toExpr c.B)
  toTypeExpr := mkConst ``PDCert

/-- `pd_certs% n A` elaborates to the literal `mkCert n A : PDCert` (native; untrusted). -/
elab "pd_certs% " n:term:max A:term:max : term => do
  let nE ← elabTermEnsuringType n (mkConst ``Nat)
  let AE ← elabTermEnsuringType A (mkApp (mkConst ``Array [Level.zero]) (mkConst ``KI))
  let e ← instantiateMVars (mkApp2 (mkConst ``mkCert) nE AE)
  let v ← unsafe evalExpr PDCert (mkConst ``PDCert) e
  return toExpr v

end Interval64.KF.KM
