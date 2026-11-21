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

open Interval64 Interval64.KF
def X : KI := KI.ofRatInterval 1 2
def Y : KI := KI.ofRatInterval (-3) (1/2)
#eval (KI.ofRat 3, KI.ofRatInterval 1 2, KI.ofRat (1/10))
#eval (X.add Y, X.mul Y, X.inv, X.sqrt, X.square, X.pown 3)
#kbench 1 "ofRat 3" KI.ofRat 3 = { lo := 4613937818241073152, hi := 4613937818241073152 }
#kbench 1 "ofRatInterval 1 2" KI.ofRatInterval 1 2 = { lo := 4607182418800017408, hi := 4611686018427387904 }
#kbench 1 "ofRat 1/10" KI.ofRat (1/10) = { lo := 4591870180066957721, hi := 4591870180066957722 }
def X' : KI := ⟨4607182418800017408, 4611686018427387904⟩
def Y' : KI := ⟨13835058055282163712, 4602678819172646912⟩
#kbench 1 "add" X'.add Y' = { lo := 13835058055282163712, hi := 4612811918334230528 }
#kbench 1 "mul" X'.mul Y' = { lo := 13841813454723219456, hi := 4607182418800017408 }
#kbench 1 "inv" X'.inv = { lo := 4602678819172646912, hi := 4607182418800017408 }
#kbench 1 "sqrt" X'.sqrt = { lo := 4607182418800017408, hi := 4609047870845172685 }
#kbench 1 "square" X'.square = { lo := 4607182418800017408, hi := 4616189618054758400 }
#kbench 1 "pown3" X'.pown 3 = { lo := 4607182418800017408, hi := 4620693217682128896 }
#eval (KF.div KI.oneBits 4611686018427387904 false, KI.containsZero X', KF.mul 4611686018427387904 4611686018427387904 true)
#kbench 1 "div1" KF.div KI.oneBits 4611686018427387904 false = 4602678819172646912
#kbench 1 "div1b" KF.div 4607182418800017408 4611686018427387904 false = 4602678819172646912
#kbench 1 "cz" KI.containsZero X' = false
#kbench 1 "mulUp" KF.mul 4611686018427387904 4611686018427387904 true = 4616189618054758400
def kiEq (a b : KI) : Bool := Nat.beq a.lo b.lo && Nat.beq a.hi b.hi
#kbench 1 "inv(b)" kiEq X'.inv { lo := 4602678819172646912, hi := 4607182418800017408 } = true
#kbench 1 "sqrt(b)" kiEq X'.sqrt { lo := 4607182418800017408, hi := 4609047870845172685 } = true
#kbench 1 "square(b)" kiEq X'.square { lo := 4607182418800017408, hi := 4616189618054758400 } = true
#kbench 1 "pown3(b)" kiEq (X'.pown 3) { lo := 4607182418800017408, hi := 4620693217682128896 } = true
#kbench 1 "ofRat 3(b)" kiEq (KI.ofRat 3) { lo := 4613937818241073152, hi := 4613937818241073152 } = true
#kbench 1 "ofRat 1/10(b)" kiEq (KI.ofRat (1/10)) { lo := 4591870180066957721, hi := 4591870180066957722 } = true
def ipowAux2 : Nat → KI → Nat → KI → KI
  | 0, _, e, acc => bif Nat.beq e 0 then acc else KI.whole
  | fuel + 1, b, e, acc =>
    bif Nat.beq e 0 then acc
    else ipowAux2 fuel (KI.square b) (Nat.div e 2) (bif Nat.beq (Nat.mod e 2) 1 then KI.mul acc b else acc)
def ipowAux3 (fuel : Nat) (b : KI) (e : Nat) (acc : KI) : KI :=
  Nat.rec (motive := fun _ => KI → Nat → KI → KI)
    (fun _ e acc => bif Nat.beq e 0 then acc else KI.whole)
    (fun _ ih b e acc => bif Nat.beq e 0 then acc
      else ih (KI.square b) (Nat.div e 2) (bif Nat.beq (Nat.mod e 2) 1 then KI.mul acc b else acc))
    fuel b e acc
#kbench 1 "ipow64" kiEq (KI.ipow X' 3) { lo := 4607182418800017408, hi := 4620693217682128896 } = true
#kbench 1 "ipowAux2 64" kiEq (ipowAux2 64 X' 3 KI.one) { lo := 4607182418800017408, hi := 4620693217682128896 } = true
#kbench 1 "ipowAux3 64" kiEq (ipowAux3 64 X' 3 KI.one) { lo := 4607182418800017408, hi := 4620693217682128896 } = true
#kbench 1 "ipowAux2 3" kiEq (ipowAux2 3 X' 3 KI.one) { lo := 4607182418800017408, hi := 4620693217682128896 } = true
#kbench 1 "mul" kiEq (KI.mul X' X') (KI.mul X' X') = true
