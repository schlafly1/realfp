import Interval64
import Lean
open Lean Elab Command Meta
/-- `#kbench n "label" t₁ = v₁` : time `Kernel.isDefEq t₁ v₁` (n repetitions), print µs/rep. -/
elab "#kbench " n:num lbl:str t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | throwError "need equation"
  let env ← getEnv
  let t0 ← IO.monoNanosNow
  let mut ok := true
  for _ in [0:n.getNat] do
    match Kernel.isDefEq env {} lhs rhs with
    | .ok b => ok := ok && b
    | .error _ => ok := false
  let t1 ← IO.monoNanosNow
  logInfo m!"{lbl.getString}: {(t1 - t0) / 1000 / n.getNat} µs  ok={ok}"

#kbench 100 "add" (4591870180066957722+4614256656552045848 : Nat) = 9206126836619003570
#kbench 100 "Nat.add" (Nat.add 4591870180066957722 4614256656552045848) = 9206126836619003570
#kbench 100 "Nat.add x5" Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 4591870180066957722 4614256656552045848) 1) 1) 1) 1 = 9206126836619003574
#kbench 100 "add x5" (4591870180066957722+4614256656552045848+1+1+1+1 : Nat) = 9206126836619003574
#kbench 100 "lit" (4591870180066957722 : Nat) = 4591870180066957722
#kbench 100 "ble" (Nat.ble 4591870180066957722 4614256656552045848) = true
#kbench 100 "ite" (if Nat.ble 4591870180066957722 4614256656552045848 = true then 1 else 0 : Nat) = 1
#kbench 100 "cond" (cond (Nat.ble 4591870180066957722 4614256656552045848) 1 0 : Nat) = 1
#kbench 100 "log2" Nat.log2 4591870180066957722 = 61
