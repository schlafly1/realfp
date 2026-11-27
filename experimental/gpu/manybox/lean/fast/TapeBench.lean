import ManyBoxTape

/-! Mathlib-free benchmark / agreement test of the C batch checker (run with `./bench.sh` from this
directory, certificates in `../../certs`). For each certificate: the C checker
(`checkHex` → `mb_check_tape`) vs its specification `checkC3 ∘ decodeCertC`, both compiled.
Also checks C = spec on mutated copies of the small certificates. Not used by any proof. -/

open Interval64 Interval64.KF ManyBox

def x2 (i : Nat) : IExpr := .pow (.var i) 2
def t8 (i : Nat) : IExpr :=
  .add (.mul (.sub (.mul (.add (.mul (.sub (.mul (.rat 128) (x2 i)) (.rat 256)) (x2 i)) (.rat 160))
    (x2 i)) (.rat 32)) (x2 i)) (.rat 1)
def eP1 : IExpr := .add (t8 0) (t8 1)
def eP2 : IExpr :=
  .sub (.add (.add (.add (.mul (x2 0) (x2 1)) (.mul (x2 1) (x2 2))) (.mul (x2 2) (x2 0)))
      (.pow (.var 3) 4))
    (.mul (.mul (.rat 4) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))

def env (d : Nat) : List Interval64 := (boxes (List.replicate d (-1, 1))).map toIC

def secs (t0 t1 : Nat) : Float := (t1 - t0).toFloat / 1e9

/-- The hex line of a certificate file (as `mb_cert%`). -/
def readCert (f : String) : IO String := do
  let txt ← IO.FS.readFile f
  return (txt.splitOn "\n").filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""

def bench (name : String) (e : IExpr) (upper : Bool) (c : Rat) (d : Nat) (file : String)
    (spec : Bool) : IO Unit := do
  let hex ← readCert file
  let cb := if upper then (KI.ofRat c).lo else (KI.ofRat c).hi
  let fe := compile e
  let t0 ← IO.monoNanosNow
  let a := checkHex fe upper cb d hex (env d)
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: C {a} {secs t0 t1} s"
  if spec then
    let t2 ← IO.monoNanosNow
    let b := checkHexSpec fe upper cb d hex (env d)
    let t3 ← IO.monoNanosNow
    IO.println s!"{name}: spec (checkC3, compiled) {b} {secs t2 t3} s"

def mutTest (name : String) (e : IExpr) (upper : Bool) (c : Rat) (d : Nat) (file : String)
    (step : Nat) : IO Unit := do
  let hex ← readCert file
  let cb := if upper then (KI.ofRat c).lo else (KI.ofRat c).hi
  let fe := compile e
  let mut n := 0; let mut pass := 0; let mut bad := 0
  for k in List.range (hex.length / step) do
    for ch in ['0', '7', 'f'] do
      let i := k * step
      let h := (hex.take i).toString ++ ch.toString ++ (hex.drop (i + 1)).toString
      let a := checkHex fe upper cb d h (env d)
      let b := checkHexSpec fe upper cb d h (env d)
      n := n + 1; if a then pass := pass + 1; if a != b then bad := bad + 1
  IO.println s!"{name} mutated: {n} cases, {pass} pass, {bad} C/spec disagreements"

def main (args : List String) : IO Unit := do
  let dir := "../../certs/"
  let spec := !args.contains "nospec"
  if !args.contains "nomut" then
    mutTest "p1_d1 c=3" eP1 true 3 2 (dir ++ "p1_d1.cert") 7
    mutTest "p1_d1 c=2.1" eP1 true (21/10) 2 (dir ++ "p1_d1.cert") 7
    mutTest "p2_d1 c=-1" eP2 false (-1) 4 (dir ++ "p2_d1.cert") 3
    mutTest "p1_d4 c=6" eP1 true 6 2 (dir ++ "p1_d4.cert") 1
    mutTest "p1_d64 c=2+1/64" eP1 true (2 + 1/64) 2 (dir ++ "p1_d64.cert") 20000
  bench "p1_d4" eP1 true 6 2 (dir ++ "p1_d4.cert") spec
  bench "p1_d1" eP1 true 3 2 (dir ++ "p1_d1.cert") spec
  bench "p1_d64" eP1 true (2 + 1/64) 2 (dir ++ "p1_d64.cert") spec
  bench "p1_d1024" eP1 true (2 + 1/1024) 2 (dir ++ "p1_d1024.cert") spec
  bench "p2_d8" eP2 false (-1/8) 4 (dir ++ "p2_d8.cert") spec
  bench "p2_d16" eP2 false (-1/16) 4 (dir ++ "p2_d16.cert") spec
  -- failing bounds (must be false)
  bench "p1_d1024 c=2" eP1 true 2 2 (dir ++ "p1_d1024.cert") false
  bench "p2_d16 c=0" eP2 false 0 4 (dir ++ "p2_d16.cert") false
