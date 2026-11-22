import Interval64.Kernel.Quad
import Lean

namespace Interval64.KF.KQ
open Lean Elab Term Meta

/-- `cells% a b N` elaborates to the literal `uniformCells a b N` (native; untrusted). -/
elab "cells% " a:term:max b:term:max N:term:max : term => do
  let fl := Lean.mkConst ``Float
  let aE ← elabTermEnsuringType a fl
  let bE ← elabTermEnsuringType b fl
  let NE ← elabTermEnsuringType N (Lean.mkConst ``Nat)
  let e ← instantiateMVars (mkApp3 (Lean.mkConst ``uniformCells) aE bE NE)
  let ty ← inferType e
  let v ← unsafe evalExpr (List (Nat × Nat × Nat)) ty e
  return toExpr v

/-- `bits% x` elaborates to the literal bit pattern of the float `x`. -/
elab "bits% " x:term:max : term => do
  let xE ← instantiateMVars (← elabTermEnsuringType x (Lean.mkConst ``Float))
  let v ← unsafe evalExpr Nat (Lean.mkConst ``Nat) (mkApp (Lean.mkConst ``bitsOf) xE)
  return toExpr v

end Interval64.KF.KQ
