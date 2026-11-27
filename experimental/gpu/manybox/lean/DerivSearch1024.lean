import ManyBoxCert
/-! P1 δ=1/1024: realfp's derivative certificate (`findCertDM`, 4,208 leaves): search time,
and the time of `checkM` on it run natively (what `native_decide` would evaluate). -/
open Interval64.KF ManyBox RealFP.IntervalTactic

def run : IO Unit := do
  let cfg : Cfg := { depth := 60, maxBoxes := 10000000 }
  let g := gLe (KI.ofRat (2 + 1/1024)).lo
  let t0 ← IO.monoNanosNow
  let (c?, evals) := findCertDM cfg eP1 g true 2 (boxes box1)
  match c? with
  | some (e', .inr c) =>
    IO.println s!"MCert {mLeaves c} leaves, {evals} evaluations"
    let t1 ← IO.monoNanosNow
    IO.println s!"search {(t1 - t0).toFloat / 1e9} s"
    let ok := checkM e' g true c (boxes box1)
    IO.println s!"checkM = {ok}"
    let t2 ← IO.monoNanosNow
    IO.println s!"checkM native {(t2 - t1).toFloat / 1e9} s"
  | some (_, .inl c) => IO.println s!"DCert {dLeaves c}"
  | none => IO.println "none"

#eval run
