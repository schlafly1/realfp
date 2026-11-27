import ManyBoxTape
import ManyBoxProbs

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

/-! Random expressions (all tape ops, including division by intervals containing 0, square roots
of negative intervals, overflow to ±∞) on random boxes, bounds and certificate strings. -/

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def consts : Array Rat := #[0, 1, -1, 2, 1/2, -3, 1/3, 10 ^ 200, -(10 ^ 200), 1 / 10 ^ 200, 7/5]
def ends : Array Rat := #[-2, -1, -1/2, 0, 1/3, 1/2, 1, 2, 10 ^ 300, -(10 ^ 300), 1 / 10 ^ 300]

partial def genE (s : Nat) (depth : Nat) : IExpr × Nat :=
  let s := lcg s
  let k := (s >>> 33) % (if depth == 0 then 2 else 10)
  match k with
  | 0 => (.var ((s >>> 40) % 3), s)
  | 1 => (.rat consts[(s >>> 40) % consts.size]!, s)
  | 2 => let (a, s) := genE s (depth - 1); let (b, s) := genE s (depth - 1); (.add a b, s)
  | 3 => let (a, s) := genE s (depth - 1); let (b, s) := genE s (depth - 1); (.sub a b, s)
  | 4 => let (a, s) := genE s (depth - 1); let (b, s) := genE s (depth - 1); (.mul a b, s)
  | 5 => let (a, s) := genE s (depth - 1); let (b, s) := genE s (depth - 1); (.div a b, s)
  | 6 => let (a, s) := genE s (depth - 1); (.neg a, s)
  | 7 => let (a, s) := genE s (depth - 1); (.pow a ((s >>> 45) % 7), s)
  | _ => let (a, s) := genE s (depth - 1); (.sqrt a, s)

def randTest (n : Nat) : IO Unit := do
  let mut s := 12345; let mut bad := 0; let mut pass := 0; let mut cnt := 0
  let hexes := #["0", "8", "c0", "f000", "e00", "ff0000", "a8", "fc0000"]
  for _ in [0:n] do
    let (e, s1) := genE s 4
    s := s1
    let mut bs : List (Rat × Rat) := []
    for _ in [0:3] do
      s := lcg s
      let a := ends[(s >>> 33) % ends.size]!; let b := ends[(s >>> 45) % ends.size]!
      bs := bs ++ [if a ≤ b then (a, b) else (b, a)]
    s := lcg s
    let up := (s >>> 50) % 2 == 0
    let c := consts[(s >>> 33) % consts.size]!
    let hex := hexes[(s >>> 40) % hexes.size]!
    let cb := if up then (KI.ofRat c).lo else (KI.ofRat c).hi
    let env := (boxes bs).map toIC
    let fe := compile e
    let a := checkHex fe up cb 3 hex env
    let b := checkHexSpec fe up cb 3 hex env
    -- the sub-tree entry point (`checkHexAt`) at a random start depth / coordinates
    s := lcg s
    let l0 := (s >>> 33) % 7
    let cs0 := [(s >>> 20) % 5, (s >>> 30) % 3, (s >>> 40) % 9]
    let a2 := checkHexAt fe up cb 3 l0 cs0 hex env
    let b2 := checkHexAtSpec fe up cb 3 l0 cs0 hex env
    if a2 != b2 then
      bad := bad + 1
      IO.println s!"DISAGREE (at): C {a2} spec {b2} l0 {l0} cs0 {cs0} hex {hex} box {bs}"
    cnt := cnt + 1; if a then pass := pass + 1
    if a != b then
      bad := bad + 1
      IO.println s!"DISAGREE: C {a} spec {b} up {up} c {c} hex {hex} box {bs}"
  IO.println s!"random expressions: {cnt} cases (each checkHex and checkHexAt), {pass} pass, {bad} C/spec disagreements"

def main (args : List String) : IO Unit := do
  let dir := "../../certs/"
  let spec := !args.contains "nospec"
  let v2 := "../../certs/v2/"
  if args.contains "rand" then
    randTest 200000
    return
  if args.contains "v2" then
    -- div / sqrt (tape ops 7, 8): mutation agreement, then the certificates
    mutTest "nes_0.25" V2.eNES false (3/2 - 1/4) 3 (v2 ++ "nes_0.25.cert") 1
    mutTest "nes_0.25 c=3/2" V2.eNES false (3/2) 3 (v2 ++ "nes_0.25.cert") 1
    mutTest "pm_0.25" V2.ePM true (1/4) 3 (v2 ++ "pm_0.25.cert") 1
    mutTest "pm_0.25 c=0" V2.ePM true 0 3 (v2 ++ "pm_0.25.cert") 1
    mutTest "nes_1/64" V2.eNES false (3/2 - 1/64) 3 (v2 ++ "nes_0.015625.cert") 997
    mutTest "pm_1/64" V2.ePM true (1/64) 3 (v2 ++ "pm_0.015625.cert") 4999
    for (nm, e, up, c) in [("nes", V2.eNES, false, (3/2 - 1/64 : Rat)), ("pm", V2.ePM, true, 1/64)] do
      for f in ["_0.015625.cert", "_0.015625_f32.cert"] do
        bench (nm ++ f) e up c 3 (v2 ++ nm ++ f) spec
    return
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
