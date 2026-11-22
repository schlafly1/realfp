import Interval64
import Interval64CSpec

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
  IO.println "----- 2D quadrature ∫∫_{[0,1]²} e^(-x²-y²) -----"
  let g2 : KF.IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
  for d in [4, 6, 8] do
    let t3 ← IO.monoNanosNow
    let R := Quad.integrate2E0 g2 0 1 0 1 0 d
    let tq ← msSince t3
    IO.println s!"  E0, 2^{d}×2^{d} cells: width {R.hi - R.lo} in {tq} ms"
    let t4 ← IO.monoNanosNow
    let R1 := Quad.integrate2E1 g2 0 1 0 1 0 d
    let tq1 ← msSince t4
    IO.println s!"  E1 (inner 2nd order), 2^{d}×2^{d} cells: width {R1.hi - R1.lo} in {tq1} ms"
  for (K, N) in [(2, 4), (2, 16), (4, 2), (4, 4), (4, 8), (6, 2), (6, 4), (8, 2)] do
    let cs := Quad.ucells 0 1 N
    let t5 ← IO.monoNanosNow
    let T := Quad.taylor2 g2 K 0 1 0 1 cs cs
    let tq2 ← msSince t5
    IO.println s!"  taylor2 K={K}, {N}×{N} cells (C): width {T.hi - T.lo} in {tq2} ms"

/-- Time `f i` for `i < reps`, returning ms per call. `f` gets the index so calls are not shared. -/
def timePer (reps : Nat) (f : Nat → Interval64) : IO (Float × Float) := do
  let mut acc : Float := 0
  let t0 ← IO.monoNanosNow
  for i in [0:reps] do
    let R := f i
    acc := acc + R.lo + R.hi
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / 1e6 / Float.ofNat reps, acc)

def cmpLine (name : String) (reps : Nat) (fc fl : Nat → Interval64) : IO Unit := do
  let (tc, a) ← timePer reps fc
  let (tl, b) ← timePer reps fl
  let unit := if tl < 0.1 then "µs" else "ms"
  let sc := if tl < 0.1 then 1000 else 1
  IO.println s!"  {name}: C {tc * sc} {unit}, Lean-compiled spec {tl * sc} {unit}, speedup ×{tl / tc} (sinks {a == b})"

def cBench : IO Unit := do
  IO.println "----- C kernels vs Lean-compiled specification (same results; per call) -----"
  let P : IPoly := (Array.range 21).map fun (k : Nat) => ofRat ((if k % 2 = 0 then 1 else -1 : Rat) / ((k : Rat) + 1))
  let dP := P.deriv
  let X := ofRatInterval 0 1
  let xs : Array Interval64 := (Array.range 64).map fun (k : Nat) => ofRatInterval ((k : Rat) / 64) ((k : Rat) / 64 + 1/1000)
  cmpLine "eval (deg 20)" 20000 (fun i => P.eval xs[i % 64]!) (fun i => CSpec.evalS P xs[i % 64]!)
  cmpLine "evalMV (deg 20)" 20000 (fun i => P.evalMV dP xs[i % 64]!) (fun i => CSpec.evalMVS P dP xs[i % 64]!)
  cmpLine "range, 2^8 boxes" 50 (fun i => P.range ⟨X.lo, X.hi + Float.ofNat (i % 2) * 0⟩ 8)
    (fun i => CSpec.rangeAuxS P dP 8 ⟨X.lo, X.hi + Float.ofNat (i % 2) * 0⟩)
  let e4 : IPoly := #[ofRat 1, ofRat (-1), ofRat (1/2), ofRat (-1/6), ofRat (1/24)]
  let bx := fun (i : Nat) => (⟨0, 4 + Float.ofNat (i % 2) * 0⟩ : Interval64)
  cmpLine "checkGt e4 > 0 on [0,4], fuel 12" 50
    (fun i => if e4.checkGt 0 (bx i) 12 then X else whole)
    (fun i => if CSpec.checkS 1 e4 0 (bx i) 12 then X else whole)
  cmpLine "bernRange deg 20, 16 boxes" 1 (fun i => P.bernRange 20 4 (bx i))
    (fun i => CSpec.bernRangeS P 20 4 (bx i))
  cmpLine "checkGtB e4, deg 6, fuel 4" 200
    (fun i => if e4.checkGtB 0 (bx i) 6 4 then X else whole)
    (fun i => if (CSpec.checkAuxBS e4 6 (CSpec.goal 1 0) 4 (bx i)) then X else whole)
  let P2 : IPoly2 := #[#[ofRat 1, ofRat (-1/2), ofRat (1/3)], #[ofRat (-1/2), ofRat 1], #[ofRat (1/5)]]
  cmpLine "bern2On (3×3, deg 6)" 2000 (fun i => P2.bern2On (bx i) X 6 6) (fun i => CSpec.bern2OnS P2 (bx i) X 6 6)
  cmpLine "checkGt2B, fuel 3" 20 (fun i => if P2.checkGt2B (-100) (bx i) X 4 4 3 then X else whole)
    (fun i => if CSpec.checkAux2BS P2 4 4 (CSpec.goal 1 (-100)) 3 (bx i) X then X else whole)
  let g : KF.IExpr := .exp (.neg (.mul (.var 0) (.var 0)))
  let one := fun (i : Nat) => 1 + Float.ofNat (i % 2) * 0
  cmpLine "integrateE0 ∫₀¹e^(-x²), 2^10 cells" 5 (fun i => Quad.integrateE0 g 0 (one i) 0 10)
    (fun i => CSpec.integrateE0S g 0 (one i) 0 10)
  cmpLine "integrateE1 ∫₀¹e^(-x²), 2^10 cells" 5 (fun i => Quad.integrateE1 g 0 (one i) 0 10)
    (fun i => CSpec.integrateE1S g 0 (one i) 0 10)
  let g2 : KF.IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
  cmpLine "integrate2E1 ∫∫e^(-x²-y²), 2^6×2^6" 1 (fun i => Quad.integrate2E1 g2 0 (one i) 0 1 0 6)
    (fun i => CSpec.integrate2E1S g2 0 (one i) 0 1 0 6)
  let c8 := Quad.ucells 0 1 8
  cmpLine "taylor2 ∫∫e^(-x²-y²) K=4, 8×8 cells" 1 (fun i => Quad.taylor2 g2 (4 + 0 * i) 0 1 0 1 c8 c8)
    (fun i => Quad.t2Sum g2 (4 + 0 * i) c8 c8)
  for (K, N) in [(4, 16), (8, 16)] do
    let csB := KF.KQ.uniformCells 0 1 N
    let cs := csB.map fun c => (KF.KQ.toFl c.1, KF.KQ.toFl c.2.1, KF.KQ.toFl c.2.2)
    cmpLine s!"Taylor quadF K={K}, {N} cells" 2 (fun i => KF.KQ.quadF g (K + 0 * i) cs)
      (fun i => KF.KQ.quadFSpec g (K + 0 * i) cs)
    let (tk, _) ← timePer 1 fun i => match KF.KQ.quadK g (K + 0 * i) (KF.KQ.bitsOf 0) (KF.KQ.bitsOf 1) csB with
      | some R => ⟨KF.KQ.toFl R.lo, KF.KQ.toFl R.hi⟩ | none => whole
    IO.println s!"    (same rule on the kernel KF/KI Nat path, run natively: {tk} ms)"
  let sx : KF.IExpr := .sin (.mul (.var 0) (.var 0))
  let csB := KF.KQ.uniformCells 0 3 64
  let cs := csB.map fun c => (KF.KQ.toFl c.1, KF.KQ.toFl c.2.1, KF.KQ.toFl c.2.2)
  cmpLine "Taylor quadF ∫₀³ sin(x²), K=8, 64 cells" 1 (fun i => KF.KQ.quadF sx (8 + 0 * i) cs)
    (fun i => KF.KQ.quadFSpec sx (8 + 0 * i) cs)

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
  cBench
