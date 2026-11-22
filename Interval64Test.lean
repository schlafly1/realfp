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

/-! ## More functions (atan, atan2, ...): C vs Lean spec vs mpmath oracle -/

def checkT2 (name : String) (impl : Float → Float → Float)
    (specD : UInt64 → UInt64 → UInt64 × Nat × Bool) (y x : Float) (st : ZivStats) : ZivStats :=
  let (b, k, ok) := specD y.toBits x.toBits
  let sp := Float.ofBits b
  let c := impl y x
  let st := { st with n := st.n + 1 }
  let st := if ok then { st with steps := st.steps.modify k (· + 1) }
    else { st with fallbacks := st.fallbacks + 1 }
  if sameBitsOrNaN c sp then st
  else { st with fails := st.fails.push s!"{name} y={showF y} x={showF x} C={showF c} spec={showF sp}" }

def checkAtan (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT "atan.down" atanDown (fun b => InvTrig.atanBitsD b false) x st
  checkT "atan.up" atanUp (fun b => InvTrig.atanBitsD b true) x st

def checkAtan2 (y x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT2 "atan2.down" atan2Down (fun a b => InvTrig.atan2BitsD a b false) y x st
  checkT2 "atan2.up" atan2Up (fun a b => InvTrig.atan2BitsD a b true) y x st

def oracleSame (got : Float) (want : String) : Bool :=
  if want == "nan" then got.isNaN else got.toBits == hexVal want

def funcTests : IO Nat := do
  let t0 ← IO.monoMsNow
  let mut at1 : ZivStats := {}
  let mut at2 : ZivStats := {}
  let mut orc := 0
  let mut orcBad : Array String := #[]
  -- mpmath oracle: C must match the oracle, and the spec must match C (checkT)
  let lines ← (do let c ← IO.FS.readFile "tests/func_oracle.txt"; pure (c.splitOn "\n"))
  for line in lines do
    match line.splitOn " " with
    | ["atan", hx, d, u] =>
      let x := Float.ofBits (hexVal hx)
      at1 := checkAtan x at1; orc := orc + 1
      if !(oracleSame (atanDown x) d && oracleSame (atanUp x) u) then orcBad := orcBad.push line
    | ["atan2", hy, hx, d, u] =>
      let y := Float.ofBits (hexVal hy); let x := Float.ofBits (hexVal hx)
      at2 := checkAtan2 y x at2; orc := orc + 1
      if !(oracleSame (atan2Down y x) d && oracleSame (atan2Up y x) u) then orcBad := orcBad.push line
    | _ => pure ()
  let mut s : UInt64 := 0xA7A2
  for hb in specials do
    at1 := checkAtan (Float.ofBits hb) at1
    for hb2 in specials do at2 := checkAtan2 (Float.ofBits hb) (Float.ofBits hb2) at2
  for _ in [0:1000] do
    s := xorshift s; let x := Float.ofBits s
    at1 := checkAtan x at1
    s := xorshift s; let w := unitF s * 20.0 - 10.0
    at1 := checkAtan w at1
    s := xorshift s; let y := Float.ofBits s
    at2 := checkAtan2 y x at2
    s := xorshift s; let v := unitF s * 20.0 - 10.0
    at2 := checkAtan2 v w at2; at2 := checkAtan2 (-v) (-w) at2
  let t1 ← IO.monoMsNow
  IO.println s!"atan: {at1.n} checks (down+up); Ziv converged at step k: {at1.steps}; fallback hits: {at1.fallbacks}; mismatches: {at1.fails.size}"
  IO.println s!"atan2: {at2.n} checks (down+up); Ziv converged at step k: {at2.steps}; fallback hits: {at2.fallbacks}; mismatches: {at2.fails.size}"
  IO.println s!"  mpmath oracle (tests/func_oracle.txt): {orc} inputs, C mismatches: {orcBad.size}; {t1 - t0} ms"
  for f in (at1.fails ++ at2.fails ++ orcBad)[:16] do IO.println s!"  {f}"
  -- constants and interval policies
  let mut ivF := 0
  if !(Interval64.pi.lo.toBits == 0x400921FB54442D18 && Interval64.pi.hi.toBits == 0x400921FB54442D19) then
    ivF := ivF + 1
  if !(halfPi.lo.toBits == 0x3FF921FB54442D18 && halfPi.hi.toBits == 0x3FF921FB54442D19) then ivF := ivF + 1
  if !(argHull.lo.toBits == 0xC00921FB54442D19 && argHull.hi.toBits == 0x400921FB54442D19) then ivF := ivF + 1
  if !(isInvalid (Interval64.atan ⟨Float.nan, 1.0⟩)) then ivF := ivF + 1
  if !(isInvalid (Interval64.atan2 ⟨0.0, 1.0⟩ ⟨Float.nan, 1.0⟩)) then ivF := ivF + 1
  -- boxes meeting the branch cut / origin give the hull
  if !(Interval64.atan2 ⟨-1.0, 1.0⟩ ⟨-2.0, -1.0⟩ == argHull) then ivF := ivF + 1
  if !(Interval64.atan2 ⟨0.0, 1.0⟩ ⟨-2.0, -1.0⟩ == argHull) then ivF := ivF + 1
  if !(Interval64.atan2 ⟨-1.0, 1.0⟩ ⟨0.0, 1.0⟩ == argHull) then ivF := ivF + 1
  -- random boxes: pointwise directed atan2 at sample points must lie inside
  let mut nIv := 0
  for _ in [0:3000] do
    s := xorshift s; let cy := unitF s * 8.0 - 4.0
    s := xorshift s; let cx := unitF s * 8.0 - 4.0
    s := xorshift s; let r := unitF s * Float.exp2 (Float.ofNat ((s % 12).toNat) - 9.0)
    let Y : Interval64 := ⟨cy - r, cy + r⟩
    let X : Interval64 := ⟨cx - r / 2.0, cx + r⟩
    let A := Interval64.atan2 Y X
    let T := Interval64.atan X
    for i in [0:5] do
      for j in [0:5] do
        let y := Y.lo + (Y.hi - Y.lo) * (Float.ofNat i / 4.0)
        let x := X.lo + (X.hi - X.lo) * (Float.ofNat j / 4.0)
        if !(decide (y ≥ Y.lo) && decide (y ≤ Y.hi) && decide (x ≥ X.lo) && decide (x ≤ X.hi)) then continue
        if y == 0.0 && decide (x ≤ 0.0) then continue  -- IEEE signed-zero convention differs from arg
        nIv := nIv + 1
        if !(decide (A.lo ≤ atan2Down y x) && decide (atan2Up y x ≤ A.hi)) then ivF := ivF + 1
        if !(decide (T.lo ≤ atanDown x) && decide (atanUp x ≤ T.hi)) then ivF := ivF + 1
  IO.println s!"atan/atan2 random boxes: {nIv} sample points checked; interval policy failures: {ivF}"
  return at1.fails.size + at2.fails.size + at1.fallbacks + at2.fallbacks + orcBad.size + ivF

/-! ## One-argument functions: generic C vs spec vs oracle -/

structure Fn1 where
  name : String
  down : Float → Float
  up : Float → Float
  spec : UInt64 → Bool → UInt64 × Nat × Bool

def fns1 : Array Fn1 := #[
  ⟨"sinh", sinhDown, sinhUp, Hyp.sinhBitsD⟩,
  ⟨"cosh", coshDown, coshUp, Hyp.coshBitsD⟩,
  ⟨"tanh", tanhDown, tanhUp, Hyp.tanhBitsD⟩,
  ⟨"log2", log2Down, log2Up, Hyp.logBBitsD false⟩,
  ⟨"log10", log10Down, log10Up, Hyp.logBBitsD true⟩,
  ⟨"tan", tanDown, tanUp, Tan.tanBitsD⟩,
  ⟨"asin", asinDown, asinUp, Asin.asinBitsD⟩,
  ⟨"acos", acosDown, acosUp, Asin.acosBitsD⟩]

def checkFn1 (f : Fn1) (x : Float) (st : ZivStats) : ZivStats :=
  let st := checkT (f.name ++ ".down") f.down (fun b => f.spec b false) x st
  checkT (f.name ++ ".up") f.up (fun b => f.spec b true) x st

/-- The exact-rational `tan` spec needs a full-width `π` reduction per Ziv step for huge
    arguments (seconds each); spec-check those on a sample only (the C result is still
    compared with the mpmath oracle for every input). -/
def specSample (f : Fn1) (x : Float) (k : Nat) : Bool :=
  f.name != "tan" || x.abs < 1.0e6 || k % 64 == 0

def fn1Tests : IO Nat := do
  let t0 ← IO.monoMsNow
  let lines ← (do let c ← IO.FS.readFile "tests/func_oracle.txt"; pure (c.splitOn "\n"))
  let mut total := 0
  for f in fns1 do
    let mut st : ZivStats := {}
    let mut orc := 0
    let mut bad : Array String := #[]
    for line in lines do
      match line.splitOn " " with
      | [fn, hx, d, u] =>
        if fn == f.name then
          let x := Float.ofBits (hexVal hx)
          if specSample f x orc then st := checkFn1 f x st
          orc := orc + 1
          if !(oracleSame (f.down x) d && oracleSame (f.up x) u) then bad := bad.push line
      | _ => pure ()
    for hb in specials do st := checkFn1 f (Float.ofBits hb) st
    let mut s : UInt64 := 0xF00D
    for k in [0:500] do
      s := xorshift s
      if specSample f (Float.ofBits s) k then st := checkFn1 f (Float.ofBits s) st
      s := xorshift s; st := checkFn1 f (unitF s * 40.0 - 20.0) st
      s := xorshift s
      st := checkFn1 f ((unitF s * 2.0 - 1.0) * Float.exp2 (Float.ofNat ((s % 80).toNat) - 70.0)) st
    IO.println s!"{f.name}: {st.n} checks; Ziv converged at step k: {st.steps}; fallback hits: {st.fallbacks}; mismatches: {st.fails.size}; oracle {orc} inputs, C mismatches {bad.size}"
    for x in (st.fails ++ bad)[:6] do IO.println s!"  {x}"
    total := total + st.fails.size + st.fallbacks + bad.size
  -- intervals: sample points inside
  let mut ivF := 0
  let mut nIv := 0
  let mut s : UInt64 := 0xBEEF
  for _ in [0:2000] do
    s := xorshift s; let c := (unitF s * 2.0 - 1.0) * Float.exp2 (Float.ofNat ((s % 16).toNat) - 8.0)
    s := xorshift s; let r := unitF s * Float.exp2 (Float.ofNat ((s % 12).toNat) - 9.0)
    let X : Interval64 := ⟨c - r, c + r⟩
    let P : Interval64 := ⟨c.abs, c.abs + r⟩
    let (S, C, T, L2, L10) := (Interval64.sinh X, Interval64.cosh X, Interval64.tanh X,
      Interval64.log2 P, Interval64.log10 P)
    for i in [0:9] do
      let t := X.lo + (X.hi - X.lo) * (Float.ofNat i / 8.0)
      let u := P.lo + (P.hi - P.lo) * (Float.ofNat i / 8.0)
      if !(decide (t ≥ X.lo) && decide (t ≤ X.hi) && decide (u ≥ P.lo) && decide (u ≤ P.hi)) then continue
      nIv := nIv + 1
      if !(decide (S.lo ≤ sinhDown t) && decide (sinhUp t ≤ S.hi)) then ivF := ivF + 1
      if !(decide (C.lo ≤ coshDown t) && decide (coshUp t ≤ C.hi)) then ivF := ivF + 1
      if !(decide (T.lo ≤ tanhDown t) && decide (tanhUp t ≤ T.hi)) then ivF := ivF + 1
      if !(decide (L2.lo ≤ log2Down u) && decide (log2Up u ≤ L2.hi)) then ivF := ivF + 1
      if !(decide (L10.lo ≤ log10Down u) && decide (log10Up u ≤ L10.hi)) then ivF := ivF + 1
  let t1 ← IO.monoMsNow
  IO.println s!"sinh/cosh/tanh/log2/log10 random intervals: {nIv} sample points; failures: {ivF}; {t1 - t0} ms"
  return total + ivF

/-- Does `I` enclose the rational `q` (endpoints compared exactly)? -/
def enclQ (I : Interval64) (q : Rat) : Bool :=
  let loOk := match Spec.bitsToRat? I.lo.toBits with
    | some l => decide (l ≤ q)
    | none => I.lo.isInf && decide (I.lo < 0)
  let hiOk := match Spec.bitsToRat? I.hi.toBits with
    | some h => decide (q ≤ h)
    | none => I.hi.isInf && decide (I.hi > 0)
  loOk && hiOk

/-- Extended division: case table and random sampling (exact rational quotients). -/
def splitTests : IO Nat := do
  let mut bad := 0
  let r (x : Float) : Option Rat := Spec.bitsToRat? x.toBits
  -- 5 / [-2, 3] = [-inf, -5/2] ∪ [5/3, +inf]
  match divSplit 5 (ofRatInterval (-2) 3) with
  | .two u l => if !(r u == some (-5/2) && l.toBits == (divDown 5.0 3.0).toBits) then bad := bad + 1
  | _ => bad := bad + 1
  match divSplit 5 (ofRatInterval 0 3) with
  | .one I => if !(I.lo.toBits == (divDown 5.0 3.0).toBits && I.hi.isInf) then bad := bad + 1
  | _ => bad := bad + 1
  match divSplit 5 (ofRatInterval (-2) 0) with
  | .one I => if !(r I.hi == some (-5/2) && I.lo.isInf) then bad := bad + 1
  | _ => bad := bad + 1
  match divSplit (ofRatInterval (-1) 1) (ofRatInterval (-2) 3) with
  | .one I => if !(I.lo.isInf && I.hi.isInf && decide (I.lo < 0)) then bad := bad + 1
  | _ => bad := bad + 1
  match divSplit 5 0 with
  | .empty => pure ()
  | _ => bad := bad + 1
  match divSplit 5 (ofRatInterval 2 3) with
  | .one I => if !(I == (5 : Interval64) / ofRatInterval 2 3) then bad := bad + 1
  | _ => bad := bad + 1
  match divSplit ⟨Float.nan, 1.0⟩ (ofRatInterval (-2) 3) with
  | .one I => if !(isInvalid I) then bad := bad + 1
  | _ => bad := bad + 1
  -- random: A, B with 0 sometimes inside / on an endpoint; points x ∈ A, y ∈ B \ {0}
  let mut s : UInt64 := 0x5EED5EED
  let mut pts := 0
  for _ in [0:4000] do
    s := xorshift s; let a0 := (unitF s * 2.0 - 1.0) * 10.0
    s := xorshift s; let a1 := a0 + unitF s * 5.0
    s := xorshift s; let k := s % 4
    s := xorshift s; let b0 := if k == 0 then 0.0 else -(unitF s * 4.0)
    s := xorshift s; let b1 := if k == 1 then 0.0 else unitF s * 4.0
    let A : Interval64 := ⟨a0, a1⟩
    let B : Interval64 := if k == 3 then ⟨b0 - 5.0, b0 - 1.0⟩ else ⟨b0, b1⟩
    let P := divSplit A B
    for i in [0:5] do
      for j in [0:5] do
        let x := A.lo + (A.hi - A.lo) * (Float.ofNat i / 4.0)
        let y := B.lo + (B.hi - B.lo) * (Float.ofNat j / 4.0)
        if !(decide (A.lo ≤ x) && decide (x ≤ A.hi) && decide (B.lo ≤ y) && decide (y ≤ B.hi)) then continue
        match r x, r y with
        | some qx, some qy =>
          if qy == 0 then continue
          pts := pts + 1
          if !(P.toList.any (fun I => enclQ I (qx / qy))) then bad := bad + 1
          if !(enclQ (P : Interval64) (qx / qy)) then bad := bad + 1
        | _, _ => pure ()
  IO.println s!"divSplit: case table + {pts} random quotient points (exact rationals) checked; failures: {bad}"
  return bad

/-- `q ≤ f` (exact; `f = +∞` always, NaN never). -/
def leQF (q : Rat) (f : Float) : Bool :=
  match Spec.bitsToRat? f.toBits with
  | some r => decide (q ≤ r)
  | none => f.isInf && decide (f > 0)

/-- `f ≤ q` (exact; `f = -∞` always, NaN never). -/
def leFQ (f : Float) (q : Rat) : Bool :=
  match Spec.bitsToRat? f.toBits with
  | some r => decide (r ≤ q)
  | none => f.isInf && decide (f < 0)

def ratAbs (q : Rat) : Rat := if q < 0 then -q else q

/-- Unbounded `mul` / `div` / `divSplit` / `sqrt` (half-lines, `whole`, `0`) and the
    `Interval64.Ops` operations, all checked against exact rationals at sample points. -/
def opsTests : IO Nat := do
  let mut bad := 0
  let mut n := 0
  let inf := Float.inf
  let r (x : Float) : Option Rat := Spec.bitsToRat? x.toBits
  -- regression: ∞/∞ corners used to make `div` return `invalid`
  let one_inf : Interval64 := ⟨1.0, inf⟩
  for (nm, q) in [("div", Interval64.div one_inf one_inf), ("feDiv", Interval64.feDiv one_inf one_inf)] do
    if !(q.lo.toBits == (0.0 : Float).toBits && q.hi == inf) then
      IO.println s!"FAIL: {nm} [1,inf]/[1,inf] = {repr q}, expected [0, inf]"; bad := bad + 1
  for (nm, q) in [("div", Interval64.div whole one_inf), ("feDiv", Interval64.feDiv whole one_inf)] do
    if !isWhole q then
      IO.println s!"FAIL: {nm} whole/[1,inf] = {repr q}, expected whole"; bad := bad + 1
  let q := Interval64.div ⟨-inf, -1.0⟩ ⟨-inf, -2.0⟩
  if !(q.lo.toBits == (0.0 : Float).toBits && q.hi == inf) then
    IO.println s!"FAIL: div [-inf,-1]/[-inf,-2] = {repr q}"; bad := bad + 1
  -- square tightening
  let sq := square ⟨-1.0, 2.0⟩
  if !(r sq.lo == some 0 && r sq.hi == some 4) then
    IO.println s!"FAIL: square [-1,2] = {repr sq}"; bad := bad + 1
  -- random intervals with infinite / zero / finite endpoints
  let ends (k : UInt64) (u : Float) : Float :=
    match k % 8 with
    | 0 => -inf | 1 => inf | 2 => 0.0 | 3 => -0.0
    | 4 => (u - 0.5) * 1.0e-3 | _ => (u - 0.5) * 20.0
  let mut s : UInt64 := 0x0B5E55ED
  for _ in [0:6000] do
    s := xorshift s; let k1 := s; s := xorshift s; let e1 := ends k1 (unitF s)
    s := xorshift s; let k2 := s; s := xorshift s; let e2 := ends k2 (unitF s)
    s := xorshift s; let k3 := s; s := xorshift s; let e3 := ends k3 (unitF s)
    s := xorshift s; let k4 := s; s := xorshift s; let e4 := ends k4 (unitF s)
    -- nonempty intervals only (`[+∞, +∞]` and `[-∞, -∞]` contain no real)
    let fix (I : Interval64) : Interval64 :=
      if I.lo == inf then ⟨0.0, inf⟩ else if I.hi == -inf then ⟨-inf, 0.0⟩ else I
    let A : Interval64 := fix (if decide (e2 < e1) then ⟨e2, e1⟩ else ⟨e1, e2⟩)
    let B : Interval64 := fix (if decide (e4 < e3) then ⟨e4, e3⟩ else ⟨e3, e4⟩)
    let pick (I : Interval64) (u : Float) : Float :=
      let lo := if I.lo.isInf then (if decide (I.hi < -1.0e6) then I.hi - 1.0e6 else -1.0e6) else I.lo
      let hi := if I.hi.isInf then (if decide (I.lo > 1.0e6) then I.lo + 1.0e6 else 1.0e6) else I.hi
      let x := lo + (hi - lo) * u
      if decide (x < lo) then lo else if decide (x > hi) then hi else x
    let M := A * B; let D := A / B; let DF := Interval64.feDiv A B; let MF := Interval64.feMul A B
    let SQ := square A; let SR := Interval64.sqrt A; let IV := inv A
    let MN := Interval64.min A B; let MX := Interval64.max A B
    let IS := intersect A B; let HU := hull A B; let NG := -A; let AB := Interval64.abs A
    let P := divSplit A B
    let md := mid A; let bs := bisect A; let wd := width A; let mg := mag A; let mi := mig A
    let pw := (List.range 8).map (pown A)
    -- mid / width / bisect sanity (A is nonempty)
    if !(contains A md && (r md).isSome) then
      if bad < 20 then IO.println s!"FAIL: mid {repr A} = {md}"
      bad := bad + 1
    match r A.lo, r A.hi with
    | some l, some h => if !leQF (h - l) wd then bad := bad + 1
    | _, _ => if !(wd.isInf && decide (wd > 0)) then bad := bad + 1
    if !(subset bs.1 A && subset bs.2 A) then bad := bad + 1
    for _i in [0:6] do
      s := xorshift s; let x := pick A (unitF s)
      s := xorshift s; let y := pick B (unitF s)
      match r x, r y with
      | some qx, some qy =>
        n := n + 1
        let chk (idx : Nat) (ok : Bool) (msg : String) : StateT Nat IO Unit := do
          if !ok then
            modify (· + 1)
            if (← get) ≤ 20 then IO.println s!"FAIL[{idx}] {msg}: A={repr A} B={repr B} x={x} y={y}"
        let ((), b) ← (do
          chk 0 (enclQ M (qx * qy)) "mul"
          chk 1 (enclQ MF (qx * qy)) "feMul"
          if qy != 0 then
            chk 2 (enclQ D (qx / qy)) "div"
            chk 3 (enclQ DF (qx / qy)) "feDiv"
            chk 4 (P.toList.any (fun I => enclQ I (qx / qy))) "divSplit"
          if qx ≥ 0 then
            -- sqrt: lo² ≤ x ≤ hi² (lo ≤ 0 or lo finite; hi = +∞ or finite)
            let loOk := match r SR.lo with
              | some l => decide (l ≤ 0) || decide (l * l ≤ qx) | none => false
            let hiOk := match r SR.hi with
              | some h => decide (h ≥ 0) && decide (qx ≤ h * h) | none => SR.hi == inf
            chk 5 (loOk && hiOk) "sqrt"
          chk 6 (enclQ SQ (qx * qx)) "square"
          chk 7 (enclQ NG (-qx)) "neg"
          chk 8 (enclQ AB (ratAbs qx)) "abs"
          chk 9 (enclQ MN (min qx qy)) "min"
          chk 10 (enclQ MX (max qx qy)) "max"
          chk 11 (if qx == 0 then isWhole IV else enclQ IV (1 / qx)) "inv"
          chk 12 (enclQ HU qx && enclQ HU qy) "hull"
          chk 13 (if enclQ B qx then enclQ IS qx else true) "intersect"
          chk 14 (leQF (ratAbs qx) mg && leFQ mi (ratAbs qx)) "mag/mig"
          chk 15 (enclQ bs.1 qx || enclQ bs.2 qx) "bisect"
          chk 16 (contains A x && subset ⟨x, x⟩ A) "contains/subset"
          for k in [0:8] do
            chk (100 + k) (enclQ (pw.getD k invalid) (qx ^ k)) s!"pown {k}"
          ).run 0
        bad := bad + b
      | _, _ => pure ()
    -- intersect is exact: if invalid, no common point at the endpoints
    if isInvalid IS then
      if enclQ B 0 && enclQ A 0 then bad := bad + 1
  IO.println s!"unbounded mul/div/divSplit/sqrt + Ops (neg abs square pown0-7 min max inv intersect hull mid width mag mig bisect subset contains): {n} random point pairs (exact rationals), failures: {bad}"
  return bad

/-! ## Navier–Stokes features: PD certificates, polynomials, quadrature -/

/-- `q ∈ I`, checked with exact rationals (infinite endpoints are unbounded). -/
def ivContains (I : Interval64) (q : Rat) : Bool :=
  let okLo := match Spec.bitsToRat? I.lo.toBits with
    | some a => decide (a ≤ q)
    | none => I.lo == -Float.inf
  let okHi := match Spec.bitsToRat? I.hi.toBits with
    | some b => decide (q ≤ b)
    | none => I.hi == Float.inf
  okLo && okHi

def randFloat (s : UInt64) (special : Bool) : Float :=
  if special && s % 13 == 0 then Float.ofBits specials[(s >>> 8).toNat % specials.size]!
  else Float.ofInt (Int.ofNat ((s >>> 11).toNat % 2001) - 1000) / 256.0

def nsTests : IO Nat := do
  let mut fails := 0
  -- 1. pdMargins: C vs Lean spec, bit-exact.
  let mut s : UInt64 := 0xFEEDFACE
  let mut nCases := 0
  for n in [0, 1, 2, 3, 4, 5, 7, 8, 13, 31] do
    for rep in [0:6] do
      let special := rep % 2 == 1
      let mut lo : Array Float := #[]
      let mut hi : Array Float := #[]
      for _ in [0:n*n] do
        s := xorshift s; let a := randFloat s special
        s := xorshift s; let b := randFloat s special
        lo := lo.push (min a b); hi := hi.push (max a b)
      let M : IMat := ⟨n, ⟨lo⟩, ⟨hi⟩⟩
      let mut xs : Array Float := #[]
      for _ in [0:n*n] do
        s := xorshift s; xs := xs.push (randFloat s special)
      for X in [FloatArray.mk xs, Mat.approxX M] do
        let c := Mat.pdMargins M X
        let r := Mat.pdMarginsSpec M X
        nCases := nCases + 1
        if c.size != r.size then fails := fails + 1
        else
          for k in [0:c.size] do
            if !sameBitsOrNaN c[k]! r[k]! then fails := fails + 1
  IO.println s!"pdMargins C vs spec: {nCases} matrices, {fails} mismatches"
  -- 2. PD decisions.
  let hilb := fun n => IMat.ofFn n fun i j => ofRat (1 / (i + j + 1 : Rat))
  let mut pdFails := 0
  for n in [1:13] do
    if !Mat.isPD (hilb n) then pdFails := pdFails + 1
  let bad := IMat.ofFn 2 fun i j => if i = j then ofRat 1 else ofRat 2
  let sing := IMat.ofFn 2 fun _ _ => ofRat 1
  if Mat.isPD bad then pdFails := pdFails + 1
  if Mat.isPD sing then pdFails := pdFails + 1
  if !Mat.lamMinGt (hilb 5) 3.2e-6 then pdFails := pdFails + 1
  if Mat.lamMinGt (hilb 5) 3.3e-6 then pdFails := pdFails + 1
  if !Mat.isGt (hilb 3) (IMat.ofFn 3 fun i j => if i = j then ofRat (1/1000) else ofRat 0) then
    pdFails := pdFails + 1
  IO.println s!"PD certificates (Hilbert 1..12, indefinite, singular, λ_min, Loewner): {pdFails} failures"
  fails := fails + pdFails
  -- 3. Polynomials vs exact rationals.
  let mut polyFails := 0
  let mut r : UInt64 := 0xABCDEF
  let qeval := fun (c : Array Rat) (x : Rat) => c.foldr (fun a acc => a + x * acc) 0
  let qmul := fun (a b : Array Rat) => Id.run do
    let mut out := Array.replicate (a.size + b.size - 1) (0 : Rat)
    for i in [0:a.size] do
      for j in [0:b.size] do
        out := out.set! (i+j) (out[i+j]! + a[i]! * b[j]!)
    return out
  let qder := fun (a : Array Rat) => (Array.range (a.size - 1)).map fun (k : Nat) => ((k : Rat) + 1) * a[k+1]!
  let qint := fun (a : Array Rat) => #[(0 : Rat)] ++ (Array.range a.size).map fun (k : Nat) => a[k]! / ((k : Rat) + 1)
  for _ in [0:300] do
    r := xorshift r; let d1 := (r % 6).toNat + 1
    r := xorshift r; let d2 := (r % 5).toNat + 1
    let mut a : Array Rat := #[]
    for _ in [0:d1] do
      r := xorshift r; a := a.push ((((r % 2001).toNat : Int) - 1000 : Rat) / 7)
    let mut b : Array Rat := #[]
    for _ in [0:d2] do
      r := xorshift r; b := b.push ((((r % 2001).toNat : Int) - 1000 : Rat) / 3)
    r := xorshift r; let x : Rat := (((r % 2001).toNat : Int) - 1000 : Rat) / 333
    r := xorshift r; let t : Rat := (((r % 201).toNat : Int) - 100 : Rat) / 17
    let A : IPoly := a.map ofRat
    let B : IPoly := b.map ofRat
    let X := ofRat x
    let checks : List (IPoly × Rat) := [
      (A, qeval a x), (A.add B, qeval a x + qeval b x), (A.sub B, qeval a x - qeval b x),
      (A.mul B, qeval (qmul a b) x), (A.deriv, qeval (qder a) x), (A.integ, qeval (qint a) x),
      (A.comp B, qeval a (qeval b x)), (A.shift (ofRat t), qeval a (x + t))]
    for (P, v) in checks do
      if !ivContains (P.eval X) v then polyFails := polyFails + 1
      if !ivContains (P.evalMV P.deriv X) v then polyFails := polyFails + 1
    -- range enclosure on [x, x + 1] contains the value at the midpoint rational
    if !ivContains (A.range (ofRatInterval x (x + 1)) 4) (qeval a (x + 1/2)) then
      polyFails := polyFails + 1
    -- exact integral ∫_x^{x+t} a
    let ex := qeval (qint a) (x + t) - qeval (qint a) x
    if !ivContains (Quad.polyIntegral A X (ofRat (x + t))) ex then polyFails := polyFails + 1
  -- sign certificates
  let e4 : IPoly := #[ofRat 1, ofRat (-1), ofRat (1/2), ofRat (-1/6), ofRat (1/24)]
  if !e4.checkGt 0 (ofRatInterval 0 4) 20 then polyFails := polyFails + 1
  let sq : IPoly := #[ofRat 0, ofRat 0, ofRat 1]   -- x² ≥ 0 but not > 0 on [-1, 1]
  if !sq.checkGe 0 (ofRatInterval (-1) 1) 20 then polyFails := polyFails + 1
  if sq.checkGt 0 (ofRatInterval (-1) 1) 20 then polyFails := polyFails + 1
  IO.println s!"polynomials vs exact rationals (300 random × 18 checks + sign certs): {polyFails} failures"
  fails := fails + polyFails
  -- 4. Quadrature.
  let mut qFails := 0
  let g : KF.IExpr := .exp (.neg (.mul (.var 0) (.var 0)))
  -- ∫₀¹ e^{-x²} = 0.74682413281242702539946743613185300535449968681...
  let gv : Rat := 74682413281242702539946743613185 / 100000000000000000000000000000000
  let gLo : Rat := gv - 1 / 10^30
  let gHi : Rat := gv + 1 / 10^30
  let R0 := Quad.integrateE0 g 0 1 1e-4 16
  let R1 := Quad.integrateE1 g 0 1 1e-10 12
  for R in [R0, R1] do
    if !(ivContains R gLo && ivContains R gHi) then qFails := qFails + 1
  if !(R1.hi - R1.lo < 1e-7) then qFails := qFails + 1
  let x2 : KF.IExpr := .mul (.var 0) (.var 0)
  if !ivContains (Quad.integrateE1 x2 0 1 1e-8 12) (1/3) then qFails := qFails + 1
  -- ∫_0^2 x³ = 4, exact interval polynomial
  if !ivContains (Quad.polyIntegral (#[(0 : Rat), 0, 0, 1].map ofRat) (ofRat 0) (ofRat 2)) 4 then
    qFails := qFails + 1
  if (Quad.integrate (fun _ _ => ofRat 0) 1 0 1e-3 3).lo != -Float.inf then qFails := qFails + 1
  IO.println s!"quadrature: ∫₀¹e^(-x²) ∈ [{R1.lo}, {R1.hi}] (width {R1.hi - R1.lo}); {qFails} failures"
  fails := fails + qFails
  -- 5. Kernel fast path (KF/KI bit patterns): PD certificates and Taylor quadrature.
  let mut kFails := 0
  let hq := fun (i j : Nat) => (1 / ((i : Rat) + j + 1) : Rat)
  for n in [1:14] do
    let A := KF.KM.ofRatFn n hq
    let l := KF.KM.pdCheckL n A (KF.KM.mkCert n A)
    if l != Mat.isPD (hilb n) then kFails := kFails + 1
    if l != KF.KM.pdCheckK n A (KF.KM.approxXK n A) then kFails := kFails + 1
    if !KF.KM.ratMatOK n A hq then kFails := kFails + 1
  for n in [1:11] do
    if !KF.KM.pdCheckL n (KF.KM.ofRatFn n hq) (KF.KM.mkCert n (KF.KM.ofRatFn n hq)) then
      kFails := kFails + 1
  let badK := KF.KM.ofRatFn 2 fun i j => if i = j then 1 else 2
  let singK := KF.KM.ofRatFn 2 fun _ _ => 1
  if KF.KM.pdCheckL 2 badK (KF.KM.mkCert 2 badK) then kFails := kFails + 1
  if KF.KM.pdCheckL 2 singK (KF.KM.mkCert 2 singK) then kFails := kFails + 1
  if KF.KM.ratMatOK 2 badK fun _ _ => 3 then kFails := kFails + 1
  let toIv := fun (R : KF.KI) => (⟨KF.KQ.toFl R.lo, KF.KQ.toFl R.hi⟩ : Interval64)
  let b0 := KF.KQ.bitsOf 0
  let b1 := KF.KQ.bitsOf 1
  for (K, N) in [(2, 32), (4, 8), (6, 8), (8, 4), (8, 16)] do
    match KF.KQ.quadK g K b0 b1 (KF.KQ.uniformCells 0 1 N) with
    | some R => if !(ivContains (toIv R) gLo && ivContains (toIv R) gHi) then kFails := kFails + 1
    | none => kFails := kFails + 1
  for K in [0, 3] do
    if (KF.KQ.quadK g K b0 b1 (KF.KQ.uniformCells 0 1 4)).isSome then kFails := kFails + 1
  -- broken chain: cells for [0, 1] but claimed [0, 2]
  if (KF.KQ.quadK g 4 b0 (KF.KQ.bitsOf 2) (KF.KQ.uniformCells 0 1 4)).isSome then kFails := kFails + 1
  match KF.KQ.quadK x2 2 b0 b1 (KF.KQ.uniformCells 0 1 3) with
  | some R => if !ivContains (toIv R) (1/3) then kFails := kFails + 1
  | none => kFails := kFails + 1
  let cs4 := KF.KQ.uniformCells 0 1 4
  if !KF.KQ.quadBound g 4 b0 b1 cs4 0 1 (7468/10000) (7469/10000) then kFails := kFails + 1
  if KF.KQ.quadBound g 4 b0 b1 cs4 0 1 (7469/10000) (7470/10000) then kFails := kFails + 1
  if KF.KQ.quadBound g 4 b0 b1 cs4 0 (1/2) (7468/10000) (7469/10000) then kFails := kFails + 1
  let w8 := match KF.KQ.quadK g 8 b0 b1 (KF.KQ.uniformCells 0 1 16) with
    | some R => KF.KQ.toFl R.hi - KF.KQ.toFl R.lo
    | none => Float.inf
  IO.println s!"kernel fast path (pdCheckL/pdCheckK vs isPD, Hilbert 1..13; Taylor quadrature K=2..8): {kFails} failures; K=8, 16 cells width {w8}"
  fails := fails + kFails
  -- 6. Bernstein enclosures (1D and 2D) vs exact rationals.
  let mut bFails := 0
  let mut rb : UInt64 := 0x5EED
  for _ in [0:200] do
    rb := xorshift rb; let d := (rb % 7).toNat + 1
    let mut a : Array Rat := #[]
    for _ in [0:d] do
      rb := xorshift rb; a := a.push ((((rb % 2001).toNat : Int) - 1000 : Rat) / 7)
    rb := xorshift rb; let lo : Rat := (((rb % 2001).toNat : Int) - 1000 : Rat) / 500
    rb := xorshift rb; let w : Rat := ((rb % 1000).toNat : Rat) / 300
    let X := ofRatInterval lo (lo + w)
    let A : IPoly := a.map ofRat
    for (n, fuel) in [(0, 0), (d + 3, 0), (d, 2)] do
      let R := A.bernRange n fuel X
      for k in [0:5] do
        let x := lo + w * (k : Rat) / 4
        if !ivContains R (qeval a x) then bFails := bFails + 1
  -- 2D: p(x, y) = Σ_j a_j(x) y^j
  for _ in [0:100] do
    let mut P2 : Array (Array Rat) := #[]
    for _ in [0:3] do
      let mut row : Array Rat := #[]
      for _ in [0:3] do
        rb := xorshift rb; row := row.push ((((rb % 201).toNat : Int) - 100 : Rat) / 9)
      P2 := P2.push row
    rb := xorshift rb; let x0 : Rat := (((rb % 201).toNat : Int) - 100 : Rat) / 50
    rb := xorshift rb; let y0 : Rat := (((rb % 201).toNat : Int) - 100 : Rat) / 50
    let X := ofRatInterval x0 (x0 + 1/2)
    let Y := ofRatInterval y0 (y0 + 1/3)
    let R := IPoly2.bern2On (P2.map fun r => r.map ofRat) X Y 3 3
    for (i, j) in [(0, 0), (1, 2), (2, 1), (2, 2)] do
      let x := x0 + (i : Rat) / 4
      let y := y0 + (j : Rat) / 6
      let v := (List.range 3).foldl (fun acc jj => acc + qeval (P2[jj]!) x * y ^ jj) 0
      if !ivContains R v then bFails := bFails + 1
  if !e4.checkGtB 0 (ofRatInterval 0 4) 6 4 then bFails := bFails + 1
  if sq.checkGtB 0 (ofRatInterval (-1) 1) 4 6 then bFails := bFails + 1
  let Rb := e4.bernOn (ofRatInterval 0 4) 12
  let Rh := e4.eval (ofRatInterval 0 4)
  IO.println s!"Bernstein (200 random 1D × 15 points, 100 random 2D × 4 points, sign certs): {bFails} failures; e4 on [0,4]: Bernstein deg 12 [{Rb.lo}, {Rb.hi}] vs Horner [{Rh.lo}, {Rh.hi}]"
  fails := fails + bFails
  -- 7. 2D quadrature over rectangles.
  let mut q2Fails := 0
  let g2 : KF.IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
  -- (∫₀¹ e^{-x²})² = 0.557746285351033...
  let g2v : Rat := 557746285351033 / 1000000000000000
  let S0 := Quad.integrate2E0 g2 0 1 0 1 1e-3 6
  let S1 := Quad.integrate2E1 g2 0 1 0 1 1e-4 7
  for S in [S0, S1] do
    if !(ivContains S (g2v - 1/10^14) && ivContains S (g2v + 1/10^14)) then q2Fails := q2Fails + 1
  let xyE : KF.IExpr := .mul (.var 0) (.var 1)
  if !ivContains (Quad.integrate2E0 xyE 0 2 (-1) 3 1e-3 6) 8 then q2Fails := q2Fails + 1
  if !ivContains (Quad.integrate2E1 xyE 0 2 (-1) 3 1e-3 6) 8 then q2Fails := q2Fails + 1
  IO.println s!"2D quadrature (∫∫ e^(-x²-y²) on [0,1]², ∫∫ xy): {q2Fails} failures; E0 [{S0.lo}, {S0.hi}], E1 [{S1.lo}, {S1.hi}]"
  fails := fails + q2Fails
  return fails


/-! ### C kernels (poly / Bernstein / quadrature) vs the Lean specifications

The `…S` functions below are literal copies of the specification bodies of the definitions
that carry `@[implemented_by]` (with every nested attached call replaced by its copy), so they
run in Lean only; the C results must agree bit for bit (`sameIv`). -/

namespace CSpec
open Interval64.IPoly Interval64.KF

def evalS (P : IPoly) (X : Interval64) : Interval64 := hornerAux P.coeff X 0 P.size
def evalMVS (P dP : IPoly) (X : Interval64) : Interval64 :=
  let m := mid X
  let H := evalS P X
  if m.isInf then H else intersect H (evalS P (point m) + evalS dP X * (X - point m))
def rangeAuxS (P dP : IPoly) : Nat → Interval64 → Interval64
  | 0, X => evalMVS P dP X
  | fuel + 1, X => hull (rangeAuxS P dP fuel (bisect X).1) (rangeAuxS P dP fuel (bisect X).2)
def checkAuxS (P dP : IPoly) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (evalMVS P dP X)
  | fuel + 1, X => g (evalMVS P dP X) || (checkAuxS P dP g fuel (bisect X).1 && checkAuxS P dP g fuel (bisect X).2)
def goal (mode : Nat) (c : Float) (R : Interval64) : Bool :=
  match mode with
  | 0 => decide (c ≤ R.lo) | 1 => decide (c < R.lo) | 2 => decide (R.hi ≤ c) | _ => decide (R.hi < c)
def checkS (mode : Nat) (P : IPoly) (c : Float) (X : Interval64) (fuel : Nat) : Bool :=
  !c.isNaN && !c.isInf && checkAuxS P (deriv P) (goal mode c) fuel X
def eval2S (P : IPoly2) (X Y : Interval64) : Interval64 :=
  hornerAux (fun j => evalS (P.coeff j) X) Y 0 P.size
def checkAux2S (P : IPoly2) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (eval2S P X Y)
  | fuel + 1, X, Y => g (eval2S P X Y) ||
      (if decide (width Y ≤ width X) then checkAux2S P g fuel (bisect X).1 Y && checkAux2S P g fuel (bisect X).2 Y
       else checkAux2S P g fuel X (bisect Y).1 && checkAux2S P g fuel X (bisect Y).2)
def bernOnS (P : IPoly) (X : Interval64) (n : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then bern01 (P.comp #[point X.lo, point X.hi - point X.lo]) n
  else evalS P X
def bernRangeS (P : IPoly) (n : Nat) : Nat → Interval64 → Interval64
  | 0, X => bernOnS P X n
  | fuel + 1, X => hull (bernRangeS P n fuel (bisect X).1) (bernRangeS P n fuel (bisect X).2)
def checkAuxBS (P : IPoly) (n : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Bool
  | 0, X => g (bernOnS P X n)
  | fuel + 1, X => g (bernOnS P X n) || (checkAuxBS P n g fuel (bisect X).1 && checkAuxBS P n g fuel (bisect X).2)
def bern2OnS (P : IPoly2) (X Y : Interval64) (n m : Nat) : Interval64 :=
  if Quad.finite X.lo && Quad.finite X.hi then
    let Q : IPoly2 := P.map fun Pj => Pj.comp #[point X.lo, point X.hi - point X.lo]
    let N := max n (IPoly2.maxSize Q - 1)
    hullUpTo (fun k => bernOnS (ofFn Q.size fun j => bernCoeffF (Q.coeff j).coeff N k) Y m) N
  else eval2S P X Y
def checkAux2BS (P : IPoly2) (n m : Nat) (g : Interval64 → Bool) : Nat → Interval64 → Interval64 → Bool
  | 0, X, Y => g (bern2OnS P X Y n m)
  | fuel + 1, X, Y => g (bern2OnS P X Y n m) ||
      (checkAux2BS P n m g fuel (bisect X).1 (bisect Y).1 && checkAux2BS P n m g fuel (bisect X).1 (bisect Y).2 &&
       checkAux2BS P n m g fuel (bisect X).2 (bisect Y).1 && checkAux2BS P n m g fuel (bisect X).2 (bisect Y).2)
def integrateE0S (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell0 fun X => evalI [X] e) a b tol fuel
def integrateE1S (e : IExpr) (a b tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell1 (fun X => evalI [X] e) (fun X => evalI [X] (e.diff 0))) a b tol fuel
def integrate2E0S (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate2 (fun X Y => evalI [X, Y] e) a b c d tol fuel
def integrate2E1S (e : IExpr) (a b c d tol : Float) (fuel : Nat) : Interval64 :=
  Quad.integrate (Quad.cell0 fun X =>
    Quad.integrate (Quad.cell1 (fun Y => evalI [X, Y] e) (fun Y => evalI [X, Y] (e.diff 1))) c d tol fuel) a b tol fuel

/-- Random expression in variables `0 .. nv-1`. -/
partial def randExpr (nv : Nat) (s : UInt64) : Nat → IExpr × UInt64
  | 0 =>
    let s := xorshift s
    if s % 3 == 0 then (.rat ((((xorshift s) % 41).toNat : Rat) / 8 - 2), xorshift s)
    else (.var ((s / 3 % nv.toUInt64).toNat), s)
  | d + 1 =>
    let s := xorshift s
    let k := (s % 22).toNat
    let (a, s) := randExpr nv s d
    let (b, s) := randExpr nv s (d / 2)
    let e : IExpr := match k with
      | 0 => .add a b | 1 => .sub a b | 2 => .mul a b | 3 => .div a b | 4 => .neg a
      | 5 => .inv a | 6 => .sqrt a | 7 => .abs a | 8 => .pow a ((s % 5).toNat) | 9 => .exp a
      | 10 => .log a | 11 => .sin a | 12 => .cos a | 13 => .atan a | 14 => .sinh a
      | 15 => .tanh a | 16 => .tan a | 17 => .asin a | 18 => .atan2 a b | 19 => .add a .pi
      | 20 => .mul a a | _ => .cosh a
    (e, s)
end CSpec

def sameIv (a b : Interval64) : Bool := a == b

def cTests : IO Nat := do
  let mut fails := 0
  let mut r : UInt64 := 0xC0FFEE
  let rnd := fun (s : UInt64) (den : Nat) => (((s % 2001).toNat : Int) - 1000 : Rat) / den
  -- polynomials
  for _ in [0:400] do
    r := xorshift r; let d := (r % 9).toNat
    let mut a : IPoly := #[]
    for _ in [0:d] do
      r := xorshift r; a := a.push (ofRatInterval (rnd r 7) (rnd r 7 + 1/1000))
    r := xorshift r; let lo := rnd r 300
    r := xorshift r; let w := ((r % 1000).toNat : Rat) / 400
    let X := ofRatInterval lo (lo + w)
    let specialX := [X, whole, ⟨-Float.inf, 1⟩, ⟨0, Float.inf⟩, invalid, ⟨1, 1⟩]
    for Y in specialX do
      if !sameIv (a.eval Y) (CSpec.evalS a Y) then fails := fails + 1
      if !sameIv (a.evalMV a.deriv Y) (CSpec.evalMVS a a.deriv Y) then fails := fails + 1
    if !sameIv (a.range X 3) (CSpec.rangeAuxS a a.deriv 3 X) then fails := fails + 1
    r := xorshift r; let c := Float.ofScientific ((r % 2000).toNat) true 2 - 10
    if a.checkGe c X 5 != CSpec.checkS 0 a c X 5 then fails := fails + 1
    if a.checkGt c X 5 != CSpec.checkS 1 a c X 5 then fails := fails + 1
    if a.checkLe c X 5 != CSpec.checkS 2 a c X 5 then fails := fails + 1
    if a.checkLt c X 5 != CSpec.checkS 3 a c X 5 then fails := fails + 1
    -- Bernstein
    for (n, fuel) in [(0, 0), (d + 3, 0), (d, 2), (12, 1)] do
      if !sameIv (a.bernOn X n) (CSpec.bernOnS a X n) then fails := fails + 1
      if !sameIv (a.bernRange n fuel X) (CSpec.bernRangeS a n fuel X) then fails := fails + 1
      if a.checkGtB c X n fuel != (!c.isNaN && !c.isInf && CSpec.checkAuxBS a n (CSpec.goal 1 c) fuel X) then
        fails := fails + 1
      if a.checkGeB c X n fuel != (!c.isNaN && !c.isInf && CSpec.checkAuxBS a n (CSpec.goal 0 c) fuel X) then
        fails := fails + 1
    for Y in specialX do
      if !sameIv (a.bernOn Y 4) (CSpec.bernOnS a Y 4) then fails := fails + 1
  -- bivariate
  for _ in [0:150] do
    r := xorshift r; let ny := (r % 4).toNat
    let mut P : IPoly2 := #[]
    for _ in [0:ny] do
      r := xorshift r; let nx := (r % 4).toNat
      let mut row : IPoly := #[]
      for _ in [0:nx] do
        r := xorshift r; row := row.push (ofRat (rnd r 9))
      P := P.push row
    r := xorshift r; let x0 := rnd r 400
    r := xorshift r; let y0 := rnd r 400
    let X := ofRatInterval x0 (x0 + 1/2)
    let Y := ofRatInterval y0 (y0 + 1/3)
    r := xorshift r; let c := Float.ofScientific ((r % 2000).toNat) true 2 - 10
    for (X', Y') in [(X, Y), (whole, Y), (X, whole), (invalid, Y)] do
      if !sameIv (P.eval2 X' Y') (CSpec.eval2S P X' Y') then fails := fails + 1
      if !sameIv (P.bern2On X' Y' 3 2) (CSpec.bern2OnS P X' Y' 3 2) then fails := fails + 1
    if P.checkGe2 c X Y 4 != (!c.isNaN && !c.isInf && CSpec.checkAux2S P (CSpec.goal 0 c) 4 X Y) then fails := fails + 1
    if P.checkGt2 c X Y 4 != (!c.isNaN && !c.isInf && CSpec.checkAux2S P (CSpec.goal 1 c) 4 X Y) then fails := fails + 1
    if P.checkGt2B c X Y 2 2 2 != (!c.isNaN && !c.isInf && CSpec.checkAux2BS P 2 2 (CSpec.goal 1 c) 2 X Y) then
      fails := fails + 1
  let polyFails := fails
  IO.println s!"C poly/Bernstein kernels vs Lean spec (400 random 1D, 150 random 2D, specials): {polyFails} mismatches"
  -- tapes: random expressions, evalI vs C tape evaluator
  let mut tFails := 0
  let mut rt : UInt64 := 0x7A9E
  for _ in [0:600] do
    rt := xorshift rt
    let (e, s) := CSpec.randExpr 2 rt ((rt % 6).toNat + 1)
    rt := s
    rt := xorshift rt; let x0 := rnd rt 400
    rt := xorshift rt; let y0 := rnd rt 400
    rt := xorshift rt; let w := ((rt % 100).toNat : Rat) / 64
    for env in [[ofRatInterval x0 (x0 + w), ofRatInterval y0 (y0 + w)], [ofRat x0, ofRat y0], [whole, ofRat y0],
        [ofRat x0]] do
      if !sameIv (KF.Tape.evalTape env e) (KF.evalI env e) then tFails := tFails + 1
  IO.println s!"C tape evaluator vs evalI (600 random expressions × 4 boxes): {tFails} mismatches"
  fails := fails + tFails
  -- quadrature
  let mut qFails := 0
  let g : KF.IExpr := .exp (.neg (.mul (.var 0) (.var 0)))
  let exprs : List KF.IExpr := [g, .mul (.var 0) (.var 0), .sin (.mul (.rat 3) (.var 0)), .inv (.add (.var 0) (.rat 1)),
    .sqrt (.var 0), .div (.rat 1) (.var 0), .atan2 (.var 0) (.rat 1)]
  for e in exprs do
    for (a, b, tol, fuel) in [((0 : Float), (1 : Float), (1e-3 : Float), 6), (0.5, 2, 1e-6, 8), (1, 0, 1e-3, 3),
        (0, Float.inf, 1e-3, 3), (-1, 1, 1e-2, 5)] do
      if !sameIv (Quad.integrateE0 e a b tol fuel) (CSpec.integrateE0S e a b tol fuel) then qFails := qFails + 1
      if !sameIv (Quad.integrateE1 e a b tol fuel) (CSpec.integrateE1S e a b tol fuel) then qFails := qFails + 1
  let g2 : KF.IExpr := .exp (.neg (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
  for e in [g2, .mul (.var 0) (.var 1), .sin (.add (.var 0) (.mul (.rat 2) (.var 1)))] do
    for (a, b, c, d) in [((0 : Float), (1 : Float), (0 : Float), (1 : Float)), (0, 2, -1, 3), (1, 0, 0, 1)] do
      if !sameIv (Quad.integrate2E0 e a b c d 1e-2 4) (CSpec.integrate2E0S e a b c d 1e-2 4) then qFails := qFails + 1
      if !sameIv (Quad.integrate2E1 e a b c d 1e-2 4) (CSpec.integrate2E1S e a b c d 1e-2 4) then qFails := qFails + 1
  -- Taylor cells: C (quadF) vs Lean (quadFSpec) vs kernel bit patterns (quadK)
  let toIv := fun (R : KF.KI) => (⟨KF.KQ.toFl R.lo, KF.KQ.toFl R.hi⟩ : Interval64)
  for e in exprs.take 6 do
    for (K, N) in [(2, 3), (4, 8), (6, 4), (8, 2)] do
      let a : Float := if e matches .sqrt _ || e matches .div .. then 0.5 else 0
      let csB := KF.KQ.uniformCells a 2 N
      let cs := csB.map fun c => (KF.KQ.toFl c.1, KF.KQ.toFl c.2.1, KF.KQ.toFl c.2.2)
      let F := KF.KQ.quadF e K cs
      if !sameIv F (KF.KQ.quadFSpec e K cs) then qFails := qFails + 1
      match KF.KQ.quadK e K (KF.KQ.bitsOf a) (KF.KQ.bitsOf 2) csB with
      | some R => if !sameIv F (toIv R) then qFails := qFails + 1
      | none => qFails := qFails + 1
  IO.println s!"C quadrature vs Lean spec (integrateE0/E1, integrate2E0/E1, Taylor quadF vs quadFSpec vs quadK): {qFails} mismatches"
  fails := fails + qFails
  return fails


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
  let funcFails ← funcTests
  let fn1Fails ← fn1Tests
  let splitFails ← splitTests
  let opsFails ← opsTests
  IO.println "----- PD / polynomials / quadrature -----"
  let nsFails ← nsTests
  IO.println "----- C poly / Bernstein / quadrature kernels -----"
  let cFails2 ← cTests
  let leanFails := fails.size + ivFails + specFails.size + ratFails + transcFails + funcFails + fn1Fails + splitFails + opsFails + nsFails + cFails2
  if leanFails == 0 then
    IO.println "ALL LEAN DIFFERENTIAL / POLICY TESTS PASSED"
    IO.println "  (backend vs fesetround, and C runtime vs Lean Spec, bit-identical on specials+randoms)"
    return 0
  else
    IO.println s!"FAILED leanFails={leanFails} avxVsFe={fails.size} policy={ivFails} vsSpec={specFails.size} transc={transcFails} func={funcFails} fn1={fn1Fails} split={splitFails} ops={opsFails} ns={nsFails} ckern={cFails2}"
    return 1
