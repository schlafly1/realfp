import Interval64.Kernel.Nat
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
open Interval64 KF
#kbench 20 "warm" lg 50975255206344927097802955061360 = 105
#kbench 20 "lg" lg 50975255206344927097802955061360 = 105
#kbench 20 "lg small" lg 12345 = 13
#kbench 20 "ones128" (ones128 == 0) = false
#kbench 20 "len128" len128 50975255206344927097802955061360 = 106
#kbench 20 "mant" mant 4591870180066957722 = 7205759403792794
#kbench 20 "isNaN" isNaN 4591870180066957722 = false
#kbench 20 "tgt" tgt 50975255206344927097802955061360 3000 = 0
#kbench 20 "finish" finish 0 4503599627370501 3022 true = 0
#kbench 20 "roundPack" roundPack 0 50975255206344927097802955061360 3000 false true = 0
#kbench 20 "mul" mul 4591870180066957722 4614256656552045848 true = 0
#kbench 20 "mul x2" [mul 4591870180066957722 4614256656552045848 true, mul 4614256656552045848 4591870180066957722 true] = []
#kbench 20 "mul x10" [mul 4591870180066957722 4614256656552045848 true, mul 4614256656552045848 4591870180066957722 true, mul 4591870180066957722 4591870180066957722 true, mul 4614256656552045848 4614256656552045848 true, mul 4591870180066957722 4614256656552045848 false, mul 4614256656552045848 4591870180066957722 false, mul 4591870180066957722 4591870180066957722 false, mul 4614256656552045848 4614256656552045848 false, mul 4591870180066957723 4614256656552045848 false, mul 4614256656552045849 4591870180066957722 false] = []
