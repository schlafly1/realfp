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
def f1 (n : Nat) : Nat := Nat.add n 1
def f10 (n : Nat) : Nat := f1 (f1 (f1 (f1 (f1 (f1 (f1 (f1 (f1 (f1 n)))))))))
#kbench 50 "warm" Nat.beq (Nat.add 1 2) 3 = true
#kbench 50 "1 op" Nat.beq (Nat.add 1 2) 3 = true
#kbench 50 "10 nested ifB" (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 9 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 8 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 7 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 6 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 5 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 4 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 3 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 2 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 1 50975255206344927097802955061360) 7 (Bool.casesOn (motive := fun _ => Nat) (Nat.ble 0 50975255206344927097802955061360) 7 0)))))))))) = 0
#kbench 50 "10 adds" Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 50975255206344927097802955061360) 50975255206344927097802955061361) 50975255206344927097802955061362) 50975255206344927097802955061363) 50975255206344927097802955061364) 50975255206344927097802955061365) 50975255206344927097802955061366) 50975255206344927097802955061367) 50975255206344927097802955061368) 50975255206344927097802955061369) 0 = false
#kbench 50 "10 defs" f10 50975255206344927097802955061360 = 50975255206344927097802955061370
#kbench 50 "len128" Nat.beq (len128 50975255206344927097802955061360) 0 = false
#kbench 50 "lgGuess" Nat.beq (lgGuess 50975255206344927097802955061360) 0 = false
#kbench 50 "lg" Nat.beq (lg 50975255206344927097802955061360) 0 = false
#kbench 50 "ones" Nat.beq ones128 0 = false
#kbench 50 "offs" Nat.beq offs128 0 = false
