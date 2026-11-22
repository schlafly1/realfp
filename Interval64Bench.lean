import Interval64

open Interval64 Interval64.Directed

/-- Simple xorshift for reproducible Lean-side interval vectors. -/
def step (s : UInt64) : UInt64 × UInt64 :=
  let z0 := s + 0x9e3779b97f4a7c15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let z := z2 ^^^ (z2 >>> 31)
  (z, z)

def bitsToSmall (u : UInt64) : Float :=
  -- 12 signed bits scaled into roughly [-8, 8]
  let i : Float := Float.ofInt (Int.ofNat (u.toNat % 4096) - 2048)
  i * (1.0 / 256.0)

def mkIv (s0 : UInt64) : Interval64 × UInt64 :=
  let (u, s1) := step s0
  let (v, s2) := step s1
  let mid := bitsToSmall u
  let rad := (bitsToSmall v).abs * 0.1 + 0.001
  (⟨mid - rad, mid + rad⟩, s2)

def genN (n : Nat) (seed : UInt64) : Array (Interval64 × Interval64 × Interval64 ×
    Interval64 × Interval64 × Interval64) :=
  Id.run do
    let mut s := seed
    let mut out := #[]
    for _ in [0:n] do
      let (a0, s1) := mkIv s
      let (a1, s2) := mkIv s1
      let (a2, s3) := mkIv s2
      let (b0, s4) := mkIv s3
      let (b1, s5) := mkIv s4
      let (b2, s6) := mkIv s5
      s := s6
      out := out.push (a0, a1, a2, b0, b1, b2)
    return out

def kernel (t : Interval64 × Interval64 × Interval64 × Interval64 × Interval64 × Interval64) : Bool :=
  let (a0, a1, a2, b0, b1, b2) := t
  Interval64.dot3SqCmp a0 a1 a2 b0 b1 b2

/-- ns per call of a scalar `Float → Float` over `xs` (summing results so the
    calls are not dropped). -/
def benchScalar (name : String) (f : Float → Float) (xs : Array Float) (reps : Nat) : IO Unit := do
  let mut acc : Float := 0
  for x in xs do acc := acc + f x  -- warmup
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    for x in xs do acc := acc + f x
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / Float.ofNat (reps * xs.size)
  IO.println s!"  {name}: {ns} ns/call  (sink={acc})"

def transcBench : IO Unit := do
  IO.println "----- exp / log / sin / cos (Lean extern call, CORE-MATH) -----"
  let mut s : UInt64 := 0x1234
  let mut ex : Array Float := #[]
  let mut lx : Array Float := #[]
  let mut sx : Array Float := #[]
  for _ in [0:4096] do
    let (u, s1) := step s; s := s1
    let t := Float.ofNat (u >>> 11).toNat / 9007199254740992.0
    ex := ex.push (t * 40.0 - 20.0)
    lx := lx.push (Float.exp2 (t * 60.0 - 30.0))
    sx := sx.push (t * 200.0 - 100.0)
  benchScalar "cr_exp  (RN, reference)" crExp ex 200
  benchScalar "expDown (RD)" expDown ex 200
  benchScalar "expUp   (RU)" expUp ex 200
  benchScalar "cr_log  (RN, reference)" crLog lx 200
  benchScalar "logDown (RD)" logDown lx 200
  benchScalar "logUp   (RU)" logUp lx 200
  benchScalar "Float.exp (libm RN)" Float.exp ex 200
  benchScalar "Float.log (libm RN)" Float.log lx 200
  benchScalar "cr_sin  (RN, reference)" crSin sx 200
  benchScalar "sinDown (RD)" sinDown sx 200
  benchScalar "sinUp   (RU)" sinUp sx 200
  benchScalar "cr_cos  (RN, reference)" crCos sx 200
  benchScalar "cosDown (RD)" cosDown sx 200
  benchScalar "cosUp   (RU)" cosUp sx 200
  benchScalar "Float.sin (libm RN)" Float.sin sx 200
  benchScalar "Float.cos (libm RN)" Float.cos sx 200

/-- KMS matrix `ρ^|i-j|` (`ρ = 1/2`, `λ_min ≥ 1/3`), entries widened by `1e-12`. -/
def kms (n : Nat) : IMat :=
  IMat.ofFn n fun i j =>
    let v := Float.pow 0.5 (Float.ofNat (if i ≤ j then j - i else i - j))
    ⟨v - 1e-12, v + 1e-12⟩

def msSince (t0 : Nat) : IO Float := do
  let t1 ← IO.monoNanosNow
  return (t1 - t0).toFloat / 1e6

def nsBench : IO Unit := do
  IO.println "----- PD certificate (n×n KMS interval matrix) -----"
  for n in [50, 100, 200, 400] do
    let M := kms n
    let t0 ← IO.monoNanosNow
    let X := Mat.approxX M
    let tX ← msSince t0
    let t1 ← IO.monoNanosNow
    let m := Mat.pdMargins M X
    let tC ← msSince t1
    let ok := Mat.marginsPos n m && Mat.xFinite n X
    let tS ← if n ≤ 100 then do
        let t2 ← IO.monoNanosNow
        let r := Mat.pdMarginsSpec M X
        let t ← msSince t2
        pure s!"{t} ms (sink {r.size})"
      else pure "skipped"
    IO.println s!"  n={n}: approxX (Lean, untrusted) {tX} ms; pdMargins C {tC} ms; Lean spec {tS}; PD={ok}"
  IO.println "----- polynomials (degree 10) -----"
  let P : IPoly := (Array.range 11).map fun (k : Nat) => ofRat ((if k % 2 = 0 then 1 else -1) / ((k : Rat) + 1))
  let xs := (Array.range 1000).map fun (k : Nat) => ofRatInterval ((k : Rat) / 1000) ((k : Rat) / 1000 + 1 / 10000)
  let reps := 200
  let t0 ← IO.monoNanosNow
  let mut acc : Float := 0
  for _ in [0:reps] do
    for x in xs do acc := acc + (P.eval x).lo
  let te ← msSince t0
  IO.println s!"  Horner eval: {te * 1e6 / Float.ofNat (reps * xs.size)} ns/call (sink {acc})"
  let dP := P.deriv
  let t1 ← IO.monoNanosNow
  for _ in [0:reps] do
    for x in xs do acc := acc + (P.evalMV dP x).lo
  let tm ← msSince t1
  IO.println s!"  mean-value eval: {tm * 1e6 / Float.ofNat (reps * xs.size)} ns/call (sink {acc})"
  for fuel in [4, 8, 12] do
    let t2 ← IO.monoNanosNow
    let R := P.range (ofRatInterval 0 1) fuel
    let tr ← msSince t2
    IO.println s!"  range on [0,1], bisection depth {fuel}: [{R.lo}, {R.hi}] in {tr} ms"
  for (n, fuel) in [(10, 0), (20, 0), (10, 4)] do
    let t2 ← IO.monoNanosNow
    let R := P.bernRange n fuel (ofRatInterval 0 1)
    let tr ← msSince t2
    IO.println s!"  Bernstein range on [0,1], degree {n}, {2 ^ fuel} boxes: [{R.lo}, {R.hi}] in {tr} ms"
  IO.println "----- quadrature ∫₀¹ e^(-x²) -----"
  let g : KF.IExpr := .exp (.neg (.mul (.var 0) (.var 0)))
  for d in [6, 10, 14] do
    let t3 ← IO.monoNanosNow
    let R := Quad.integrateE1 g 0 1 0 d
    let tq ← msSince t3
    IO.println s!"  cell1, 2^{d} cells: width {R.hi - R.lo} in {tq} ms"
  for d in [10, 14] do
    let t3 ← IO.monoNanosNow
    let R := Quad.integrateE0 g 0 1 0 d
    let tq ← msSince t3
    IO.println s!"  cell0, 2^{d} cells: width {R.hi - R.lo} in {tq} ms"
  for (K, N) in [(4, 8), (4, 16), (6, 8), (8, 4), (8, 16)] do
    let cs := KF.KQ.uniformCells 0 1 N
    let t3 ← IO.monoNanosNow
    let R := KF.KQ.quadK g K (KF.KQ.bitsOf 0) (KF.KQ.bitsOf 1) cs
    let w := match R with
      | some R => KF.KQ.toFl R.hi - KF.KQ.toFl R.lo
      | none => Float.inf
    let tq ← msSince t3
    IO.println s!"  Taylor K={K} (kernel KF path, run natively), {N} cells: width {w} in {tq} ms"

def main : IO Unit := do
  IO.println "Interval64 benches"
  IO.println s!"C backend: {backendName}  AVX-512F available: {avx512fAvailable}"
  IO.println "----- C kernels (pinned by the caller if using taskset) -----"
  let sinkC := runCBenches ()
  IO.println s!"C bench returned sink={sinkC}"
  -- Lean Interval64 using AVX scalar externs (includes constructor allocation)
  let n := 3000
  let data := genN n 0xC0FFEE
  let rec warmup (k : Nat) (acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k'+1 =>
      let acc := data.foldl (fun a t => if kernel t then a+1 else a) acc
      warmup k' acc
  let acc0 := warmup 3 0
  let reps := 80
  let t0 ← IO.monoNanosNow
  let mut acc := acc0
  for _ in [0:reps] do
    acc := data.foldl (fun a t => if kernel t then a+1 else a) acc
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / (Float.ofNat (reps * n))
  IO.println s!"Lean Interval64 (AVX externs, allocated structs): {ns} ns/kernel  sink={acc}"
  transcBench
  nsBench
