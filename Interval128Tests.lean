/-
Interval128 tests (compiled):
1. `fmaDown` / `fmaUp`: C runtime vs the Lean bit-level spec.
2. Each interval operation: C kernel (`add` = `addImpl`) vs the Lean
   definition (`addSpec`), bit-exact (all NaNs equal, signed zeros distinct),
   on random double-double intervals, wide-exponent, tiny/subnormal,
   near-overflow and special (±0, ±∞, NaN) inputs, and reversed intervals.
3. Enclosure against exact rationals: for every finite case, 9 rational points
   `x ∈ X`, `y ∈ Y` (endpoints and midpoint) satisfy `lo ≤ x op y ≤ hi`
   (for sqrt: `lo² ≤ x ≤ hi²`).
4. Tightness: point inputs, width / |result| in units of 2^-106.
-/
import Interval128

namespace Interval128Tests

open Interval64 Interval64.Directed Interval128

def sameF (a b : Float) : Bool := (a.isNaN && b.isNaN) || a.toBits == b.toBits

def sameI (a b : Interval128) : Bool :=
  sameF a.lh b.lh && sameF a.ll b.ll && sameF a.uh b.uh && sameF a.ul b.ul

def hex64 (x : Float) : String :=
  let n := x.toBits.toNat
  let rec go (v : Nat) (k : Nat) (acc : String) : String :=
    if k = 0 then acc
    else
      let d := v % 16
      let ch := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
      go (v / 16) (k-1) (String.singleton ch ++ acc)
  "0x" ++ go n 16 ""

def showI (a : Interval128) : String :=
  s!"[{hex64 a.lh} {hex64 a.ll} , {hex64 a.uh} {hex64 a.ul}]"

def mix (s : UInt64) : UInt64 :=
  let z0 := s + 0x9e3779b97f4a7c15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  z2 ^^^ (z2 >>> 31)

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng := let s := mix g.s; (s, ⟨s⟩)

/-- Float with sign bit `sg`, unbiased exponent `e` (clamped to normal range), mantissa bits `m`. -/
def mkF (sg : Bool) (e : Int) (m : UInt64) : Float :=
  let be : Int := max 1 (min 2046 (e + 1023))
  Float.ofBits ((if sg then (1 : UInt64) <<< 63 else 0) ||| (UInt64.ofNat be.toNat <<< 52) |||
    (m &&& 0xFFFFFFFFFFFFF))

def specialBits : Array UInt64 := #[
  0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001,
  0x000fffffffffffff, 0x0010000000000000, 0x8010000000000000, 0x3ff0000000000000,
  0xbff0000000000000, 0x3ff0000000000001, 0x7fefffffffffffff, 0xffefffffffffffff,
  0x7fe0000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000,
  0x3ca0000000000000, 0x0350000000000000, 0x4000000000000000, 0x3fd5555555555555]

/-- Random double-double: `hi` with exponent in `[elo, ehi]`, `lo` about `ulp(hi)/2^k` or 0. -/
def randDD (g : Rng) (elo ehi : Int) : Float × Float × Rng :=
  let (a, g) := g.next
  let (b, g) := g.next
  let (c, g) := g.next
  let span := (ehi - elo + 1).toNat
  let e : Int := elo + ((a >>> 8).toNat % span : Nat)
  let h := mkF (a &&& 1 == 1) e b
  let mode := (c >>> 60).toNat
  let l :=
    if mode == 0 then 0.0
    else if mode == 1 then mkF (c &&& 1 == 1) (e - 60 - ((c >>> 3).toNat % 40 : Nat)) (c >>> 7)
    else mkF (c &&& 1 == 1) (e - 53 - ((c >>> 3).toNat % 3 : Nat)) (c >>> 7)
  (h, (if e - 60 < -1020 then 0.0 else l), g)

def ratOf? (f : Float) : Option Rat := Interval64.Spec.bitsToRat? f.toBits

def ddVal? (h l : Float) : Option Rat :=
  match ratOf? h, ratOf? l with
  | some a, some b => some (a + b)
  | _, _ => none

/-- Build an interval from two random double-doubles, ordered (`rev` keeps the given order). -/
def mkI (h1 l1 h2 l2 : Float) (rev : Bool) : Interval128 :=
  match ddVal? h1 l1, ddVal? h2 l2 with
  | some a, some b => if (b < a) != rev then ⟨h2, l2, h1, l1⟩ else ⟨h1, l1, h2, l2⟩
  | _, _ => ⟨h1, l1, h2, l2⟩

def randI (g : Rng) (elo ehi : Int) : Interval128 × Rng :=
  let (h1, l1, g) := randDD g elo ehi
  let (k, g) := g.next
  -- narrow (same exponent region) or wide
  let (h2, l2, g) :=
    if k % 3 == 0 then
      let (d, g) := g.next
      let (h2, l2, g') := randDD g (elo - 20) (ehi - 20)
      let _ := d
      (h1 + h2, l2, g')
    else randDD g elo ehi
  (mkI h1 l1 h2 l2 (k % 97 == 5), g)

def specialI (g : Rng) : Interval128 × Rng :=
  let (a, g) := g.next
  let pickS (x : UInt64) : Float := Float.ofBits (specialBits[(x.toNat % specialBits.size)]!)
  let (h1, l1, g) := randDD g (-30) 30
  let (h2, l2, g) := randDD g (-30) 30
  let k := (a >>> 4).toNat % 6
  let x : Interval128 :=
    if k == 0 then ⟨pickS a, 0, pickS (a >>> 20), 0⟩
    else if k == 1 then ⟨pickS a, pickS (a >>> 12), pickS (a >>> 20), pickS (a >>> 28)⟩
    else if k == 2 then ⟨h1, l1, pickS (a >>> 20), 0⟩
    else if k == 3 then ⟨pickS a, 0, h2, l2⟩
    else if k == 4 then ⟨h1, pickS (a >>> 12), h2, l2⟩
    else mkI h1 l1 h2 l2 false
  (x, g)

/-! ### Exact checks -/

def loOK (h l : Float) (x : Rat) : Bool :=
  match ddVal? h l with
  | some v => decide (v ≤ x)
  | none => h == -Float.inf && !l.isNaN && !(l == Float.inf)   -- -∞ lower end
def hiOK (h l : Float) (x : Rat) : Bool :=
  match ddVal? h l with
  | some v => decide (x ≤ v)
  | none => h == Float.inf && !l.isNaN && !(l == -Float.inf)

/-- Rational sample points of a finite-endpoint interval. -/
def points (X : Interval128) : Array Rat :=
  match ddVal? X.lh X.ll, ddVal? X.uh X.ul with
  | some a, some b => if a ≤ b then #[a, b, (a + b) / 2] else #[]
  | _, _ => #[]

structure Stats where
  diff : Nat := 0
  encl : Nat := 0
  checked : Nat := 0
  points : Nat := 0
  firstDiff : String := ""
  firstEncl : String := ""

def bin (name : String) (impl spec : Interval128 → Interval128 → Interval128)
    (exact : Rat → Rat → Option Rat) (X Y : Interval128) (st : Stats) : Stats := Id.run do
  let r := impl X Y
  let s := spec X Y
  let mut st := { st with checked := st.checked + 1 }
  if !sameI r s then
    st := { st with diff := st.diff + 1,
                    firstDiff := if st.firstDiff == "" then
                      s!"{name} X={showI X} Y={showI Y} C={showI r} spec={showI s}" else st.firstDiff }
  for x in points X do
    for y in points Y do
      match exact x y with
      | none => pure ()
      | some z =>
        st := { st with points := st.points + 1 }
        if !(loOK r.lh r.ll z && hiOK r.uh r.ul z) then
          st := { st with encl := st.encl + 1,
                          firstEncl := if st.firstEncl == "" then
                            s!"{name} X={showI X} Y={showI Y} R={showI r}" else st.firstEncl }
  return st

def unSqrt (X : Interval128) (st : Stats) : Stats := Id.run do
  let r := Interval128.sqrt X
  let s := sqrtSpec X
  let mut st := { st with checked := st.checked + 1 }
  if !sameI r s then
    st := { st with diff := st.diff + 1,
                    firstDiff := if st.firstDiff == "" then
                      s!"sqrt X={showI X} C={showI r} spec={showI s}" else st.firstDiff }
  for x in points X do
    if 0 ≤ x then
      st := { st with points := st.points + 1 }
      let okLo := match ddVal? r.lh r.ll with
        | some v => decide (v ≤ 0) || decide (v * v ≤ x)
        | none => r.lh == -Float.inf
      let okHi := match ddVal? r.uh r.ul with
        | some v => decide (0 ≤ v) && decide (x ≤ v * v)
        | none => r.uh == Float.inf
      if !(okLo && okHi) then
        st := { st with encl := st.encl + 1,
                        firstEncl := if st.firstEncl == "" then
                          s!"sqrt X={showI X} R={showI r}" else st.firstEncl }
  return st

/-! ### Tightness on point inputs -/

structure Tight where
  n : Nat := 0
  sum : Float := 0
  max : Float := 0

def relWidth (r : Interval128) (z : Rat) : Option Float :=
  match ddVal? r.lh r.ll, ddVal? r.uh r.ul with
  | some a, some b =>
    if z == 0 then none
    else
      let w := (b - a) / (if z < 0 then -z else z) * (2 : Rat) ^ 106
      some (Float.ofScientific w.num.natAbs true 0 / Float.ofNat w.den)
  | _, _ => none

def Tight.add (t : Tight) (w : Option Float) : Tight :=
  match w with
  | some v => { n := t.n + 1, sum := t.sum + v, max := if v > t.max then v else t.max }
  | none => t

def fmaCheck (g : Rng) (n : Nat) : Nat × Rng := Id.run do
  let mut g := g
  let mut bad := 0
  for i in [0:n] do
    let (a, g1) := g.next
    let (b, g2) := g1.next
    let (c, g3) := g2.next
    g := g3
    let pick (x : UInt64) (j : Nat) : Float :=
      if j % 7 == 0 then Float.ofBits (specialBits[(x.toNat % specialBits.size)]!)
      else mkF (x &&& 1 == 1) (((x >>> 8).toNat % 120 : Nat) - 60 : Int) (x >>> 11)
    let x := pick a i
    let y := pick b (i / 3)
    -- third operand: random, special, or the exact-error patterns -RN(x*y)
    let z := if i % 4 == 0 then -(x * y) else if i % 4 == 1 then pick c (i / 5)
      else mkF (c &&& 1 == 1) (((c >>> 8).toNat % 240 : Nat) - 120 : Int) (c >>> 11)
    if !sameF (fmaDown x y z) (fmaDownSpec x y z) then bad := bad + 1
    if !sameF (fmaUp x y z) (fmaUpSpec x y z) then bad := bad + 1
  return (bad, g)

def report (name : String) (st : Stats) : IO Unit := do
  IO.println s!"  {name}: {st.checked} cases, C-vs-spec mismatches {st.diff}; {st.points} exact points, enclosure failures {st.encl}"
  if st.firstDiff != "" then IO.println s!"    first mismatch: {st.firstDiff}"
  if st.firstEncl != "" then IO.println s!"    first enclosure failure: {st.firstEncl}"

def run (nRand : Nat := 20000) : IO Nat := do
  IO.println "----- Interval128 (double-double) -----"
  IO.println s!"Interval128 C backend: {if Interval128.backendId () == 0 then "avx512 (embedded rounding)" else "rn+err"}"
  let mut g : Rng := ⟨0x1234567887654321⟩
  let (fbad, g') := fmaCheck g 200000
  g := g'
  IO.println s!"  fmaDown/fmaUp C vs spec: 400000 checks, mismatches {fbad}"
  let qadd := fun (x y : Rat) => some (x + y)
  let qsub := fun (x y : Rat) => some (x - y)
  let qmul := fun (x y : Rat) => some (x * y)
  let qdiv := fun (x y : Rat) => if y == 0 then none else some (x / y)
  let mut sa : Stats := {}
  let mut ss : Stats := {}
  let mut sm : Stats := {}
  let mut sd : Stats := {}
  let mut sq : Stats := {}
  -- exponent regimes: ordinary, wide, tiny (error terms underflow), huge (overflow)
  let regimes : Array (Int × Int) := #[(-30, 30), (-30, 30), (-300, 300), (-1022, -900), (900, 1023)]
  for i in [0:nRand] do
    let (elo, ehi) := regimes[i % regimes.size]!
    let (X, g1) := if i % 11 == 7 then specialI g else randI g elo ehi
    let (Y, g2) := if i % 13 == 5 then specialI g1 else randI g1 elo ehi
    g := g2
    sa := bin "add" (· + ·) addSpec qadd X Y sa
    ss := bin "sub" (· - ·) subSpec qsub X Y ss
    sm := bin "mul" (· * ·) mulSpec qmul X Y sm
    sd := bin "div" (· / ·) divSpec qdiv X Y sd
    sq := unSqrt X sq
  report "add" sa; report "sub" ss; report "mul" sm; report "div" sd; report "sqrt" sq
  -- tightness on point inputs (normalized random double-doubles, exponents in [-30, 30])
  let mut ta : Tight := {}
  let mut tm : Tight := {}
  let mut td : Tight := {}
  let mut tq : Tight := {}
  for _ in [0:5000] do
    let (h1, l1, g1) := randDD g (-30) 30
    let (h2, l2, g2) := randDD g1 (-30) 30
    g := g2
    let a1 := h1 + l1
    let b1 := h2 + l2
    let x1 := (h1 - a1) + l1
    let y1 := (h2 - b1) + l2
    let X : Interval128 := ⟨a1, x1, a1, x1⟩
    let Y : Interval128 := ⟨b1, y1, b1, y1⟩
    match ddVal? a1 x1, ddVal? b1 y1 with
    | some x, some y =>
      -- same-sign addition (no cancellation) for the add statistic
      let Ya : Interval128 := if (x < 0) == (y < 0) then Y else Interval128.neg Y
      let ya := if (x < 0) == (y < 0) then y else -y
      ta := ta.add (relWidth (X + Ya) (x + ya))
      tm := tm.add (relWidth (X * Y) (x * y))
      if y != 0 then td := td.add (relWidth (X / Y) (x / y))
      if x > 0 then
        let r := Interval128.sqrt X
        match ddVal? r.uh r.ul with
        | some v => tq := tq.add (relWidth r v)
        | none => pure ()
    | _, _ => pure ()
  let showT (n : String) (t : Tight) : String :=
    s!"{n}: max {t.max}, mean {if t.n == 0 then 0 else t.sum / t.n.toFloat} ({t.n} cases)"
  IO.println s!"  tightness, point inputs, width/|result| in units of 2^-106:"
  IO.println s!"    {showT "add" ta}; {showT "mul" tm}"
  IO.println s!"    {showT "div" td}; {showT "sqrt" tq}"
  let total := fbad + sa.diff + sa.encl + ss.diff + ss.encl + sm.diff + sm.encl + sd.diff + sd.encl +
    sq.diff + sq.encl
  IO.println s!"Interval128 failures: {total}"
  return total

end Interval128Tests
