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

namespace P
def laneOnes (B : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul B (Nat.succ B))) 1) (Nat.sub (Nat.shiftLeft 1 (Nat.succ B)) 1)
def laneOffsets (B : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (laneOnes B) B)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul B (Nat.add B 2))) 1) (Nat.sub (Nat.shiftLeft 1 (Nat.add B 2)) 1))
def ones128 : Nat := laneOnes 128
def offs128 : Nat := laneOffsets 128
/-- bit length of n < 2^128 -/
def len128 (n : Nat) : Nat :=
  Nat.mod (Nat.land (Nat.shiftRight (Nat.add (Nat.mul n ones128) offs128) 128) ones128)
    (Nat.sub (Nat.shiftLeft 1 129) 1)
def lgGuess (n : Nat) : Nat := Nat.sub (len128 n) 1
def lg (n : Nat) : Nat :=
  (fun k => Bool.casesOn (motive := fun _ => Nat)
     (Bool.and (Nat.ble (Nat.shiftLeft 1 k) n) (Nat.blt n (Nat.shiftLeft 1 (Nat.succ k))))
     (Nat.log2 n) k) (lgGuess n)
end P
open P
#kbench 20 "len128" len128 50975255206344927097802955061360 = 106
#kbench 20 "lg" lg 50975255206344927097802955061360 = 105
#kbench 20 "ones" ones128 = 0
