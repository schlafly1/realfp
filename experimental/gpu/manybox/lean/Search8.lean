import ManyBoxCert
/-! The certificate search of realfp's `interval` tactic (`findCertDM`: derivative /
centred-form / Horner search; untrusted, compiled, C runtime) on the manybox problems:
size of the certificate it finds and the search time. The kernel/native check of that
certificate is a separate cost (see the README). -/
open Interval64.KF ManyBox RealFP.IntervalTactic

def report (name : String) (e : IExpr) (g : KI → Bool) (upper : Bool) (n : Nat) (bs : List (ℚ × ℚ))
    (cfg : Cfg := { depth := 60, maxBoxes := 10000000 }) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let (c?, evals) := findCertDM cfg e g upper n (boxes bs)
  let leaves := match c? with
    | some (_, .inl c) => s!"{dLeaves c} leaves (DCert {dStats c})"
    | some (_, .inr c) => s!"{mLeaves c} leaves (MCert {mStats c})"
    | none => "no certificate"
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {leaves}, {evals} evaluations, search {(t1 - t0).toFloat / 1e6} ms"

#eval report "P2 delta=1/8  default" eP2 (gGe (KI.ofRat (-1/8)).hi) false 4 box2
