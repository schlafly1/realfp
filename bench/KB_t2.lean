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

#kbench 20 "add" (4591870180066957722+4614256656552045848 : Nat) = 9206126836619003570
#kbench 20 "mul" (4591870180066957722*4614256656552045848 : Nat) = 21188067544396801061870074004421638256
#kbench 20 "shr" (4591870180066957722 >>> 52 : Nat) = 1019
#kbench 20 "mod" (4591870180066957722 % 2048 : Nat) = 410
#kbench 20 "pow" (2 ^ 52 : Nat) = 4503599627370496
#kbench 20 "log2small" Nat.log2 1024 = 10
#kbench 20 "log2" Nat.log2 4591870180066957722 = 61
#kbench 20 "beq" (if (4591870180066957722 : Nat) = 5 then 1 else 0 : Nat) = 0
#kbench 20 "intsub" ((4591870180066957722:Nat):Int) - 1075 = 4591870180066956647
#kbench 20 "intsubneg" ((5:Nat):Int) - 1075 = -1070
#kbench 20 "tonat" ((5:Int) - 1075).toNat = 0
#kbench 20 "intmax" max ((5:Int) - 1075) (-1074) = -1070
