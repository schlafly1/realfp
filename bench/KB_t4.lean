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

open Interval64
def X : Interval64.Interval64 := ⟨Float.ofBits 4591870180066957722, Float.ofBits 4614256656552045848⟩
def Y : Interval64.Interval64 := ⟨Float.ofBits 4591870180066957722, Float.ofBits 4614256656552045848⟩
#kbench 5 "Float.lt" decide (Float.ofBits 4591870180066957722 < Float.ofBits 4614256656552045848) = true
#kbench 5 "Float.le" decide (Float.ofBits 4591870180066957722 ≤ Float.ofBits 4614256656552045848) = true
#kbench 5 "isNaN" (Float.ofBits 4591870180066957722).isNaN = false
#kbench 5 "beq0" (Float.ofBits 4591870180066957722 == 0) = false
#kbench 5 "lit 0.0" (0.0 : Float).toBits.toNat = 0
#kbench 5 "Directed.mulUp" (Directed.mulUp (Float.ofBits 4591870180066957722) (Float.ofBits 4614256656552045848)).toBits.toNat = 4596373779694328218
#kbench 5 "X+Y" (X + Y).hi.toBits.toNat = 0
#kbench 5 "X*Y" (X * Y).hi.toBits.toNat = 0
#kbench 5 "X/Y" (X / Y).hi.toBits.toNat = 0
#kbench 5 "bitsToRat" Spec.bitsToRat? 4591870180066957722 = none
