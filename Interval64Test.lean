import Interval64

open Interval64 Interval64.Directed

def hex64 (x : Float) : String :=
  let n := x.toBits.toNat
  let rec go (v : Nat) (k : Nat) (acc : String) : String :=
    if k = 0 then acc
    else
      let d := v % 16
      let ch := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
      go (v / 16) (k-1) (String.singleton ch ++ acc)
  "0x" ++ go n 16 ""

def showF (x : Float) : String :=
  if x.isNaN then "NaN" else s!"{x} [{hex64 x}]"

/-- Special bit patterns used in the C self-test. -/
def specials : Array UInt64 := #[
  0x0000000000000000, 0x8000000000000000,
  0x0000000000000001, 0x8000000000000001,
  0x000fffffffffffff, 0x800fffffffffffff,
  0x0010000000000000, 0x8010000000000000,
  0x3ff0000000000000, 0xbff0000000000000,
  0x3ff0000000000001, 0x3fe0000000000000,
  0x4000000000000000, 0x3fd5555555555555,
  0x7fefffffffffffff, 0xffefffffffffffff,
  0x7ff0000000000000, 0xfff0000000000000,
  0x7ff8000000000000, 0x7ff0000000000001,
  0xfff8000000000000, 0x0000000000000002,
  0x3fc0000000000000, 0xc000000000000000
]

structure Fail where
  op : String
  a : Float
  b : Float
  left : Float
  right : Float

def check2 (op : String) (a b left right : Float) (acc : Array Fail) : Array Fail :=
  if sameBitsOrNaN left right then acc else acc.push { op, a, b, left, right }

def failToString (f : Fail) : String :=
  s!"  {f.op} a={showF f.a} b={showF f.b} left={showF f.left} right={showF f.right}"

def xorshift (s : UInt64) : UInt64 :=
  let z0 := s + 0x9e3779b97f4a7c15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  z2 ^^^ (z2 >>> 31)


/-! ## Transcendentals: C (CORE-MATH under RD/RU) vs Lean Ziv spec -/

structure ZivStats where
  n : Nat := 0
  /-- `steps[k]` = number of results whose Ziv loop converged at precision
      `128 * 2^k` (constant-result special cases are counted at `k = 0`). -/
  steps : Array Nat := #[0, 0, 0, 0, 0]
  fallbacks : Nat := 0
  fails : Array String := #[]

def checkT (name : String) (impl : Float → Float) (specD : UInt64 → UInt64 × Nat × Bool)
    (x : Float) (st : ZivStats) : ZivStats :=
  let (b, k, ok) := specD x.toBits
  let sp := Float.ofBits b
  let c := impl x
  let st := { st with n := st.n + 1 }
  let st := if ok then { st with steps := st.steps.modify k (· + 1) }
    else { st with fallbacks := st.fallbacks + 1 }
  if sameBitsOrNaN c sp then st
  else { st with fails := st.fails.push s!"{name} x={showF x} C={showF c} spec={showF sp}" }

def checkExp (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT "exp.down" expDown (fun b => Transc.expBitsD b false) x st
  checkT "exp.up" expUp (fun b => Transc.expBitsD b true) x st

def checkLog (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT "log.down" logDown (fun b => Transc.logBitsD b false) x st
  checkT "log.up" logUp (fun b => Transc.logBitsD b true) x st

def checkSin (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT "sin.down" sinDown (fun b => Trig.sinBitsD b false) x st
  checkT "sin.up" sinUp (fun b => Trig.sinBitsD b true) x st

def checkCos (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT "cos.down" cosDown (fun b => Trig.cosBitsD b false) x st
  checkT "cos.up" cosUp (fun b => Trig.cosBitsD b true) x st

def hexVal (s : String) : UInt64 :=
  s.foldl (fun acc c =>
    let d : UInt64 := if '0' ≤ c && c ≤ '9' then (c.toNat - 48).toUInt64
      else if 'a' ≤ c && c ≤ 'f' then (c.toNat - 87).toUInt64
      else if 'A' ≤ c && c ≤ 'F' then (c.toNat - 55).toUInt64 else 0
    acc * 16 + d) 0

/-- Float in `[0, 1)` from random bits. -/
def unitF (u : UInt64) : Float := Float.ofNat (u >>> 11).toNat / 9007199254740992.0

def transcTests : IO Nat := do
  let t0 ← IO.monoMsNow
  let extra : Array Float := #[709.78, 709.7827128933840, 709.79, 710.0, 710.5, -745.13,
    -745.1332191019411, -745.14, -746.0, -746.5, 1.0e-300, 0.5, 1.5, 0.75, 2.0, 10.0, 1.0e10,
    1.0e-10, Float.ofBits 0x3FEFFFFFFFFFFFFF, Float.ofBits 0x3FF0000000000001,
    0.6931471805599453, 2.718281828459045]
  let mut e : ZivStats := {}
  let mut l : ZivStats := {}
  let mut sn : ZivStats := {}
  let mut cs : ZivStats := {}
  let trigExtra : Array Float := #[0.75, 0.7500000000000001, 0.7853981633974483, 1.5707963267948966,
    3.141592653589793, 4.71238898038469, 6.283185307179586, 355.0, 103993.0, 1.0e22, 1.0e300,
    1.7976931348623157e308, Float.ofBits 0x6CF0000000000000, 1.0e-300, 1.0e-10, 1073741824.0,
    1073741823.9999999]
  for hb in specials do
    e := checkExp (Float.ofBits hb) e; l := checkLog (Float.ofBits hb) l
    sn := checkSin (Float.ofBits hb) sn; cs := checkCos (Float.ofBits hb) cs
  for x in extra ++ trigExtra do
    e := checkExp x e; l := checkLog x l
    e := checkExp (-x) e; l := checkLog (-x) l
    sn := checkSin x sn; cs := checkCos x cs; sn := checkSin (-x) sn; cs := checkCos (-x) cs
  let mut s : UInt64 := 0x5EED
  for _ in [0:2000] do
    s := xorshift s; let x := Float.ofBits s
    e := checkExp x e; l := checkLog x l; l := checkLog x.abs l
    s := xorshift s; e := checkExp (unitF s * 1500.0 - 750.0) e
    s := xorshift s
    let y := (unitF s * 2.0 - 1.0) * Float.exp2 (Float.ofNat ((s % 64).toNat)) / 1.0e9
    e := checkExp y e
    s := xorshift s; l := checkLog (unitF s * 4.0) l
    s := xorshift s; l := checkLog (1.0 + (unitF s - 0.5) * 1.0e-6) l
    s := xorshift s; let z := Float.ofBits s
    sn := checkSin z sn; cs := checkCos z cs
    s := xorshift s; let w := unitF s * 20.0 - 10.0
    sn := checkSin w sn; cs := checkCos w cs
    s := xorshift s; let v := (unitF s * 2.0 - 1.0) * Float.exp2 (Float.ofNat ((s % 80).toNat) - 70.0)
    sn := checkSin v sn; cs := checkCos v cs
  -- CORE-MATH hard-to-round cases
  let hard ← (do let c ← IO.FS.readFile "tests/transc_hard.txt"; pure (c.splitOn "\n"))
  let mut nHard := 0
  for line in hard do
    match line.splitOn " " with
    | [fn, hx] =>
      let x := Float.ofBits (hexVal hx)
      if fn == "exp" then
        e := checkExp x e; nHard := nHard + 1
      else if fn == "log" then
        l := checkLog x l; nHard := nHard + 1
      else if fn == "sin" then
        sn := checkSin x sn; nHard := nHard + 1
      else if fn == "cos" then
        cs := checkCos x cs; nHard := nHard + 1
    | _ => pure ()
  let t1 ← IO.monoMsNow
  IO.println s!"exp: {e.n} checks (down+up); Ziv converged at step k (prec 128*2^k): {e.steps}; fallback hits: {e.fallbacks}; mismatches: {e.fails.size}"
  IO.println s!"log: {l.n} checks (down+up); Ziv converged at step k (prec 128*2^k): {l.steps}; fallback hits: {l.fallbacks}; mismatches: {l.fails.size}"
  IO.println s!"sin: {sn.n} checks (down+up); Ziv converged at step k (prec 128*2^k): {sn.steps}; fallback hits: {sn.fallbacks}; mismatches: {sn.fails.size}"
  IO.println s!"cos: {cs.n} checks (down+up); Ziv converged at step k (prec 128*2^k): {cs.steps}; fallback hits: {cs.fallbacks}; mismatches: {cs.fails.size}"
  IO.println s!"  (includes {nHard} CORE-MATH hard-to-round inputs; {t1 - t0} ms)"
  for f in (e.fails ++ l.fails ++ sn.fails ++ cs.fails)[:16] do IO.println s!"  {f}"
  -- interval policies
  let mut ivF := 0
  let ie := Interval64.exp ⟨-1.0, 1.0⟩
  if !(ie.lo.toBits == (expDown (-1.0)).toBits && ie.hi.toBits == (expUp 1.0).toBits) then ivF := ivF + 1
  if !(decide (ie.lo < 0.36788) && decide (0.36787 < ie.lo) && decide (2.71828 < ie.hi) && decide (ie.hi < 2.71829)) then ivF := ivF + 1
  let il := Interval64.log ⟨-1.0, 2.0⟩
  if !(il.lo.isInf && decide (il.lo < 0) && il.hi.toBits == (logUp 2.0).toBits) then ivF := ivF + 1
  if !(isInvalid (Interval64.log ⟨-2.0, -1.0⟩)) then ivF := ivF + 1
  let iz := Interval64.log ⟨0.0, 0.0⟩
  if !(iz.lo.isInf && iz.hi.isInf && decide (iz.hi < 0)) then ivF := ivF + 1
  if !(isInvalid (Interval64.exp ⟨Float.nan, 1.0⟩)) then ivF := ivF + 1
  -- π certificates: every cached enclosure must be certified (not the [3, 3.15] fallback)
  let mut piBad := 0
  for k in [0:5] do
    for big in [false, true] do
      let pb := Trig.piBounds (Transc.zivPrec k) big
      if !(decide (pb.2 - pb.1 < 1 / 2 ^ (Transc.zivPrec k + 100)) && decide (pb.1 < pb.2)) then piBad := piBad + 1
  IO.println s!"pi enclosures (10 cached precisions) not certified at full width: {piBad}"
  ivF := ivF + piBad
  -- sin / cos intervals
  let is1 := Interval64.sin ⟨0.0, 3.0⟩          -- contains the max π/2, no min
  if !(is1.hi.toBits == plusOne.toBits && is1.lo.toBits == (fmin (sinDown 0.0) (sinDown 3.0)).toBits) then ivF := ivF + 1
  let is2 := Interval64.sin ⟨4.0, 5.0⟩          -- contains the min 3π/2
  if !(is2.lo.toBits == minusOne.toBits) then ivF := ivF + 1
  let is3 := Interval64.sin ⟨0.1, 0.2⟩          -- monotone
  if !(is3.lo.toBits == (sinDown 0.1).toBits && is3.hi.toBits == (sinUp 0.2).toBits) then ivF := ivF + 1
  let ic1 := Interval64.cos ⟨-1.0, 1.0⟩         -- contains max 0
  if !(ic1.hi.toBits == plusOne.toBits && ic1.lo.toBits == (cosDown 1.0).toBits) then ivF := ivF + 1
  let ic2 := Interval64.cos ⟨3.0, 3.2⟩          -- contains min π
  if !(ic2.lo.toBits == minusOne.toBits) then ivF := ivF + 1
  let iw := Interval64.sin ⟨-Float.inf, 0.0⟩
  if !(iw.lo.toBits == minusOne.toBits && iw.hi.toBits == plusOne.toBits) then ivF := ivF + 1
  if !(isInvalid (Interval64.cos ⟨Float.nan, 1.0⟩)) then ivF := ivF + 1
  -- random intervals: sampled points (RN libm, then checked against directed C at the point) inside
  let mut nIv := 0
  let mut nSharp := 0
  for _ in [0:3000] do
    s := xorshift s; let c := (unitF s * 2.0 - 1.0) * Float.exp2 (Float.ofNat ((s % 40).toNat) - 10.0)
    s := xorshift s; let r := unitF s * Float.exp2 (Float.ofNat ((s % 12).toNat) - 9.0)
    let X : Interval64 := ⟨c - r, c + r⟩
    let S := Interval64.sin X
    let C := Interval64.cos X
    if S.lo.toBits != minusOne.toBits && S.hi.toBits != plusOne.toBits then nSharp := nSharp + 1
    for i in [0:9] do
      let t := X.lo + (X.hi - X.lo) * (Float.ofNat i / 8.0)
      if !(decide (t ≥ X.lo) && decide (t ≤ X.hi)) then continue
      nIv := nIv + 1
      if !(decide (S.lo ≤ sinDown t) && decide (sinUp t ≤ S.hi)) then ivF := ivF + 1
      if !(decide (C.lo ≤ cosDown t) && decide (cosUp t ≤ C.hi)) then ivF := ivF + 1
  IO.println s!"sin/cos random intervals: {nIv} sample points checked ({nSharp}/3000 sin results not clamped to ±1)"
  IO.println s!"exp/log/sin/cos interval policy failures: {ivF}"
  return e.fails.size + l.fails.size + sn.fails.size + cs.fails.size + e.fallbacks + l.fallbacks +
    sn.fallbacks + cs.fallbacks + ivF

def main : IO UInt32 := do
  IO.println "Interval64 tests (Lean 4.36, compiled exe)"
  IO.println s!"C backend: {backendName}"
  IO.println s!"AVX-512F available: {avx512fAvailable}"
  if !backendOk () then
    IO.println "ERROR: compiled backend needs AVX-512F, which is not available at runtime"
    return 1

  -- C self-test report (AVX vs FE vs software oracles)
  IO.println "----- C self-test -----"
  let cFails := selftestReport ()
  IO.println s!"C selftest recorded failures (includes soft-oracle mismatches): {cFails}"

  -- Lean-side AVX vs fesetround over specials
  let mut fails : Array Fail := #[]
  for ha in specials do
    for hb in specials do
      let a := Float.ofBits ha
      let b := Float.ofBits hb
      fails := check2 "add.down" a b (avxAddDown a b) (feAddDown a b) fails
      fails := check2 "add.up"   a b (avxAddUp a b)   (feAddUp a b)   fails
      fails := check2 "sub.down" a b (avxSubDown a b) (feSubDown a b) fails
      fails := check2 "sub.up"   a b (avxSubUp a b)   (feSubUp a b)   fails
      fails := check2 "mul.down" a b (avxMulDown a b) (feMulDown a b) fails
      fails := check2 "mul.up"   a b (avxMulUp a b)   (feMulUp a b)   fails
      fails := check2 "div.down" a b (avxDivDown a b) (feDivDown a b) fails
      fails := check2 "div.up"   a b (avxDivUp a b)   (feDivUp a b)   fails
    let a := Float.ofBits ha
    fails := check2 "sqrt.down" a 0 (avxSqrtDown a) (feSqrtDown a) fails
    fails := check2 "sqrt.up"   a 0 (avxSqrtUp a)   (feSqrtUp a)   fails

  -- Classic cases
  let one := 1.0
  let halfUlp := Float.ofBits 0x3ca0000000000000 -- 2^-53
  fails := check2 "add.down 1+2^-53" one halfUlp (avxAddDown one halfUlp) (feAddDown one halfUlp) fails
  fails := check2 "add.up 1+2^-53"   one halfUlp (avxAddUp one halfUlp)   (feAddUp one halfUlp)   fails
  fails := check2 "div.down 1/3" one 3.0 (avxDivDown one 3.0) (feDivDown one 3.0) fails
  fails := check2 "div.up 1/3"   one 3.0 (avxDivUp one 3.0)   (feDivUp one 3.0)   fails
  fails := check2 "sqrt.down 2" 2.0 0 (avxSqrtDown 2.0) (feSqrtDown 2.0) fails
  fails := check2 "sqrt.up 2"   2.0 0 (avxSqrtUp 2.0)   (feSqrtUp 2.0)   fails
  -- signed zero of exact cancellation
  let zDown := avxAddDown 1.0 (-1.0)
  let zUp   := avxAddUp   1.0 (-1.0)
  if zDown.toBits != 0x8000000000000000 then
    fails := fails.push { op := "1+(-1) down should be -0", a := 1.0, b := -1.0, left := zDown, right := feAddDown 1.0 (-1.0) }
  if zUp.toBits != 0 then
    fails := fails.push { op := "1+(-1) up should be +0", a := 1.0, b := -1.0, left := zUp, right := feAddUp 1.0 (-1.0) }
  let sm := avxSqrtDown (Float.ofBits 0x8000000000000000)
  if sm.toBits != 0x8000000000000000 then
    fails := fails.push { op := "sqrt(-0) should be -0", a := Float.ofBits 0x8000000000000000, b := 0, left := sm, right := feSqrtDown (Float.ofBits 0x8000000000000000) }

  IO.println s!"Lean backend vs FE specials: {fails.size} mismatches"
  for f in fails[:12] do
    IO.println (failToString f)

  -- Interval policies
  let mut ivFails : Nat := 0
  let d01 : Interval64 := ⟨1.0, 2.0⟩
  let dZ  : Interval64 := ⟨-1.0, 1.0⟩
  let q := Interval64.div d01 dZ
  if !isWhole q then
    IO.println s!"FAIL: [1,2]/[-1,1] should be whole, got {repr q}"
    ivFails := ivFails + 1
  let bad := Interval64.sqrt ⟨-2.0, -1.0⟩
  if !isInvalid bad then
    IO.println s!"FAIL: sqrt[-2,-1] should be invalid, got {repr bad}"
    ivFails := ivFails + 1
  let s := Interval64.sqrt ⟨-1.0, 4.0⟩
  if !(s.lo == 0.0 && s.lo.toBits == 0 && s.hi == 2.0) then
    IO.println s!"FAIL: sqrt[-1,4] expected [+0, 2], got lo={showF s.lo} hi={showF s.hi}"
    ivFails := ivFails + 1
  let ziv := Interval64.sqrt ⟨Float.ofBits 0x8000000000000000, 0.0⟩
  if !(ziv.lo == 0.0 && ziv.hi == 0.0 && ziv.lo.toBits == 0x8000000000000000 && ziv.hi.toBits == 0) then
    IO.println s!"note: sqrt[-0,+0] = lo={showF ziv.lo} hi={showF ziv.hi} (expected -0, +0)"
    if !(ziv.lo == 0.0 && ziv.hi == 0.0) then ivFails := ivFails + 1

  -- Lean interval vs FE interval on a handful of finite intervals
  let samples : Array (Interval64 × Interval64) := #[
    (⟨1.0, 2.0⟩, ⟨3.0, 4.0⟩),
    (⟨-2.0, -1.0⟩, ⟨-4.0, -3.0⟩),
    (⟨-1.0, 2.0⟩, ⟨-3.0, 4.0⟩),
    (⟨0.0, 1.0⟩, ⟨-0.5, 2.0⟩),
    (⟨1.0, 1.0⟩, ⟨3.0, 3.0⟩)
  ]
  for (a, b) in samples do
    let xa := a + b
    let xf := Interval64.feAdd a b
    if xa != xf then
      IO.println s!"FAIL add {repr a}+{repr b}: avx={repr xa} fe={repr xf}"
      ivFails := ivFails + 1
    let ya := a * b
    let yf := Interval64.feMul a b
    if ya != yf then
      IO.println s!"FAIL mul {repr a}*{repr b}: avx={repr ya} fe={repr yf}"
      ivFails := ivFails + 1

  -- Directed 1/3 bounds
  let lo := avxDivDown 1.0 3.0
  let hi := avxDivUp 1.0 3.0
  IO.println s!"1/3 down={showF lo} up={showF hi}"
  if lo.toBits == hi.toBits then
    IO.println "FAIL: 1/3 down and up should differ"
    ivFails := ivFails + 1
  if !decide (lo < hi) then
    IO.println "FAIL: 1/3 down should be < up"
    ivFails := ivFails + 1

  -------------------------------------------------------------------------
  -- Differential: compiled C runtime (`addDown`, etc.) vs Lean software spec
  -------------------------------------------------------------------------
  IO.println "----- C runtime vs Lean Spec -----"
  let mut specFails : Array Fail := #[]
  for ha in specials do
    for hb in specials do
      let a := Float.ofBits ha
      let b := Float.ofBits hb
      specFails := check2 "spec add.down" a b (addDown a b) (addDownSpec a b) specFails
      specFails := check2 "spec add.up"   a b (addUp a b)   (addUpSpec a b)   specFails
      specFails := check2 "spec sub.down" a b (subDown a b) (subDownSpec a b) specFails
      specFails := check2 "spec sub.up"   a b (subUp a b)   (subUpSpec a b)   specFails
      specFails := check2 "spec mul.down" a b (mulDown a b) (mulDownSpec a b) specFails
      specFails := check2 "spec mul.up"   a b (mulUp a b)   (mulUpSpec a b)   specFails
      specFails := check2 "spec div.down" a b (divDown a b) (divDownSpec a b) specFails
      specFails := check2 "spec div.up"   a b (divUp a b)   (divUpSpec a b)   specFails
    let a := Float.ofBits ha
    specFails := check2 "spec sqrt.down" a 0 (sqrtDown a) (sqrtDownSpec a) specFails
    specFails := check2 "spec sqrt.up"   a 0 (sqrtUp a)   (sqrtUpSpec a)   specFails

  -- Random bit patterns (including NaN / Inf / subnormals).
  -- 100000 independent pairs per binary op (and 100000 sqrt inputs), not a Cartesian product.
  let nRand : Nat := 100000
  IO.println s!"C vs Lean spec: {nRand} random cases per op ..."
  let mut s := (0xC0FFEE : UInt64)
  let mut nAdd := 0; let mut nSub := 0; let mut nMul := 0; let mut nDiv := 0; let mut nSqrt := 0
  for _ in [0:nRand] do
    s := xorshift s; let a := Float.ofBits s
    s := xorshift s; let b := Float.ofBits s
    specFails := check2 "specR add.down" a b (addDown a b) (addDownSpec a b) specFails
    specFails := check2 "specR add.up"   a b (addUp a b)   (addUpSpec a b)   specFails
    nAdd := nAdd + 2
    specFails := check2 "specR sub.down" a b (subDown a b) (subDownSpec a b) specFails
    specFails := check2 "specR sub.up"   a b (subUp a b)   (subUpSpec a b)   specFails
    nSub := nSub + 2
    specFails := check2 "specR mul.down" a b (mulDown a b) (mulDownSpec a b) specFails
    specFails := check2 "specR mul.up"   a b (mulUp a b)   (mulUpSpec a b)   specFails
    nMul := nMul + 2
    specFails := check2 "specR div.down" a b (divDown a b) (divDownSpec a b) specFails
    specFails := check2 "specR div.up"   a b (divUp a b)   (divUpSpec a b)   specFails
    nDiv := nDiv + 2
    specFails := check2 "specR sqrt.down" a 0 (sqrtDown a) (sqrtDownSpec a) specFails
    specFails := check2 "specR sqrt.up"   a 0 (sqrtUp a)   (sqrtUpSpec a)   specFails
    nSqrt := nSqrt + 2
  IO.println s!"  random cases: add={nAdd} sub={nSub} mul={nMul} div={nDiv} sqrt={nSqrt}"

  -- ofRat consistency: directed ops agree (by value) with ofRatDown/ofRatUp of the
  -- exact rational result, and every finite float is representable.
  let mut ratFails := 0
  let mut nRat := 0
  let mut r := (0xBADC0DE : UInt64)
  for _ in [0:400] do
    r := xorshift r; let a := Float.ofBits r
    r := xorshift r; let b := Float.ofBits r
    match Spec.bitsToRat? a.toBits, Spec.bitsToRat? b.toBits with
    | some qa, some qb =>
      nRat := nRat + 1
      let v := fun (f : Float) => Spec.bitsToRat? f.toBits
      let vb := fun (u : UInt64) => Spec.bitsToRat? u
      if !(Spec.isRepresentable qa) then ratFails := ratFails + 1
      if v (addDown a b) != vb (Spec.ofRatDown (qa + qb)) then ratFails := ratFails + 1
      if v (addUp a b) != vb (Spec.ofRatUp (qa + qb)) then ratFails := ratFails + 1
      if v (subDown a b) != vb (Spec.ofRatDown (qa - qb)) then ratFails := ratFails + 1
      if v (subUp a b) != vb (Spec.ofRatUp (qa - qb)) then ratFails := ratFails + 1
      if v (mulDown a b) != vb (Spec.ofRatDown (qa * qb)) then ratFails := ratFails + 1
      if v (mulUp a b) != vb (Spec.ofRatUp (qa * qb)) then ratFails := ratFails + 1
      if qb != 0 then
        if v (divDown a b) != vb (Spec.ofRatDown (qa / qb)) then ratFails := ratFails + 1
        if v (divUp a b) != vb (Spec.ofRatUp (qa / qb)) then ratFails := ratFails + 1
    | _, _ => pure ()
  if Spec.isRepresentable (1/10 : Rat) then ratFails := ratFails + 1
  if !(Spec.isRepresentable (3/4 : Rat)) then ratFails := ratFails + 1
  IO.println s!"ofRat vs directed ops (value level): {nRat} finite pairs, {ratFails} mismatches"

  IO.println s!"C runtime vs Lean spec: {specFails.size} mismatches"
  for f in specFails[:16] do
    IO.println (failToString f)

  IO.println "----- exp / log / sin / cos -----"
  let transcFails ← transcTests
  let leanFails := fails.size + ivFails + specFails.size + ratFails + transcFails
  if leanFails == 0 then
    IO.println "ALL LEAN DIFFERENTIAL / POLICY TESTS PASSED"
    IO.println "  (backend vs fesetround, and C runtime vs Lean Spec, bit-identical on specials+randoms)"
    return 0
  else
    IO.println s!"FAILED leanFails={leanFails} avxVsFe={fails.size} policy={ivFails} vsSpec={specFails.size} transc={transcFails}"
    return 1
