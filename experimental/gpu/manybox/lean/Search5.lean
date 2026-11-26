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

#eval report "P1 delta=1/1024 default" eP1 (gLe (KI.ofRat (2 + 1/1024)).lo) true 2 box1
