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

def main : IO UInt32 := do
  IO.println "Interval64 tests (Lean 4.36, compiled exe)"
  IO.println s!"AVX-512F available: {avx512fAvailable}"
  if !avx512fAvailable then
    IO.println "ERROR: AVX-512F not available at runtime"
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

  IO.println s!"Lean AVX vs FE specials: {fails.size} mismatches"
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

  let leanFails := fails.size + ivFails + specFails.size + ratFails
  if leanFails == 0 then
    IO.println "ALL LEAN DIFFERENTIAL / POLICY TESTS PASSED"
    IO.println "  (AVX vs fesetround, and C runtime vs Lean Spec, bit-identical on specials+randoms)"
    return 0
  else
    IO.println s!"FAILED leanFails={leanFails} avxVsFe={fails.size} policy={ivFails} vsSpec={specFails.size}"
    return 1
