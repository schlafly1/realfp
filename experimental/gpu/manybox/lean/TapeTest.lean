import ManyBoxCert
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 50

/-! Agreement tests of the C batch checker (`checkHex`, C runtime) against its Lean
specification (`checkHexSpec` = `checkC3` on the decoded certificate), on passing and failing
bounds and on truncated / mutated certificates. (Not a proof; the proofs only use the spec.) -/

/-- C result vs Lean spec for a list of bounds. -/
def agree (fe : IExpr) (upper : Bool) (d : Nat) (hex : String) (env : List Interval64)
    (cs : List ℚ) : List (ℚ × Bool × Bool) :=
  cs.map fun c =>
    let cb := if upper then (KI.ofRat c).lo else (KI.ofRat c).hi
    (c, checkHex (compile fe) upper cb d hex env, checkHexSpec (compile fe) upper cb d hex env)

#eval (toTape (compile eP1)).isSome
#eval (toTape (compile eP2)).isSome
#eval agree eP1 true 2 (mb_cert% "../certs/p1_d4.cert") ((boxes box1).map toIC)
  [6, 5, 4, 3, 2, 21/10, 7, 100, -3]
#eval agree eP1 true 2 (mb_cert% "../certs/p1_d1.cert") ((boxes box1).map toIC)
  [3, 5/2, 2, 21/10, 31/10, 4]
#eval agree eP2 false 4 (mb_cert% "../certs/p2_d1.cert") ((boxes box2).map toIC)
  [-1, -1/2, 0, -2, -3/4, -100]
-- truncated / corrupted certificates
#eval agree eP1 true 2 "f" ((boxes box1).map toIC) [100, 1000, 6]
#eval agree eP1 true 2 "" ((boxes box1).map toIC) [100, 1000, 6]
#eval agree eP2 false 4 ((mb_cert% "../certs/p2_d1.cert").drop 3).toString ((boxes box2).map toIC) [-1, -10, -100]

/-- Mutated certificates: digit `k*step` replaced by each of `0`, `7`, `f`; returns
    (cases, C passes, C/Lean disagreements). -/
def mutTest (fe : IExpr) (upper : Bool) (cb d : Nat) (hex : String) (env : List Interval64)
    (step : Nat) : Nat × Nat × Nat := Id.run do
  let mut n := 0; let mut pass := 0; let mut bad := 0
  for k in List.range (hex.length / step) do
    for ch in ['0', '7', 'f'] do
      let i := k * step
      let h := (hex.take i).toString ++ ch.toString ++ (hex.drop (i + 1)).toString
      let a := checkHex (compile fe) upper cb d h env
      let b := checkHexSpec (compile fe) upper cb d h env
      n := n + 1; if a then pass := pass + 1; if a != b then bad := bad + 1
  return (n, pass, bad)

#eval mutTest eP1 true (KI.ofRat 3).lo 2 (mb_cert% "../certs/p1_d1.cert") ((boxes box1).map toIC) 7
#eval mutTest eP1 true (KI.ofRat (21/10)).lo 2 (mb_cert% "../certs/p1_d1.cert") ((boxes box1).map toIC) 7
#eval mutTest eP2 false (KI.ofRat (-1)).hi 4 (mb_cert% "../certs/p2_d1.cert") ((boxes box2).map toIC) 3
