import RealFPGridNative

/-! CPU-only tests of the C checker (`c/grid_tape.c`) against its Lean specification
(`checkGridSpec`, compiled Lean): every comparison must agree, true or false. The build fails
(`#eval` throws) on any disagreement. No GPU, no tool, no Mathlib. -/

open Interval64 Interval64.KF RealFP.Grid

namespace RealFP.Grid.Tests

def sh (i : Nat) : IExpr := .add (.rat 2) (.var i)
def eNES : IExpr :=
  .add (.add (.div (sh 0) (.add (sh 1) (sh 2))) (.div (sh 1) (.add (sh 2) (sh 0)))) (.div (sh 2) (.add (sh 0) (sh 1)))
def ePM : IExpr :=
  .sub (.add (.add (.sqrt (sh 0)) (.sqrt (sh 1))) (.sqrt (sh 2)))
    (.sqrt (.mul (.rat 3) (.add (.add (sh 0) (sh 1)) (sh 2))))
/-- a polynomial with powers and negation on a non-dyadic box -/
def ePoly : IExpr :=
  .sub (.add (.pow (.var 0) 4) (.mul (.rat (7/3)) (.mul (.var 0) (.var 1)))) (.neg (.pow (.var 1) 3))

def env (bs : List (Rat × Rat)) : List Interval64 := (boxes bs).map toIC

/-- Flip bit `i` of a hex string. -/
def flipBit (s : String) (i : Nat) : String :=
  let b := s.toUTF8
  let j := i / 4
  if j ≥ b.size then s else
  let v := hexValC (b.get! j)
  let v' := v ^^^ (2 ^ (3 - i % 4))
  String.fromUTF8! (b.set! j (hexChar v'))

def agree (fe : FExpr) (upper : Bool) (c d l0 : Nat) (hex : String) (e : List Interval64) : Bool :=
  checkGrid fe upper c d l0 hex e == checkGridSpec fe upper c d l0 hex e

/-- Certificate from the built-in search, then all single-bit mutations of its first `nb` bits. -/
def mutationTest (name : String) (e : IExpr) (upper : Bool) (c : Rat) (bs : List (Rat × Rat))
    (nb : Nat) : IO Unit := do
  let fe := compile e
  let cb := if upper then (KI.ofRat c).lo else (KI.ofRat c).hi
  let E := env bs
  match searchGrid fe upper cb bs.length E 200 10000000 with
  | .error n => throw <| .userError s!"{name}: no certificate ({n} boxes)"
  | .ok (hex, n) =>
    unless checkGrid fe upper cb bs.length 0 hex E && checkGridSpec fe upper cb bs.length 0 hex E do
      throw <| .userError s!"{name}: certificate rejected"
    let mut bad := 0
    let mut falses := 0
    for i in [0:min nb (4 * hex.length)] do
      let h := flipBit hex i
      unless agree fe upper cb bs.length 0 h E do bad := bad + 1
      unless checkGridSpec fe upper cb bs.length 0 h E do falses := falses + 1
    if bad > 0 then throw <| .userError s!"{name}: {bad} disagreements"
    IO.println s!"{name}: {n} boxes, {hex.length} hex digits; {min nb (4 * hex.length)} mutations agree ({falses} rejected)"

/-- Deterministic pseudo-random numbers. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

partial def randExpr (s : Nat) (depth d : Nat) : IExpr × Nat :=
  let s := lcg s
  let k := (s >>> 33) % (if depth == 0 then 2 else 9)
  match k with
  | 0 => (.var ((s >>> 40) % d), s)
  | 1 =>
    let num : Int := ((s >>> 20) % 2001 : Nat) - 1000
    let den := (s >>> 45) % 97 + 1
    let ex := (s >>> 12) % 5
    (.rat ((num : Rat) / den * (if ex == 0 then ((10 ^ 150 : Nat) : Rat) else if ex == 1 then 1 / ((10 ^ 150 : Nat) : Rat) else 1)), s)
  | 2 => let (a, s) := randExpr s (depth - 1) d; let (b, s) := randExpr s (depth - 1) d; (.add a b, s)
  | 3 => let (a, s) := randExpr s (depth - 1) d; let (b, s) := randExpr s (depth - 1) d; (.sub a b, s)
  | 4 => let (a, s) := randExpr s (depth - 1) d; let (b, s) := randExpr s (depth - 1) d; (.mul a b, s)
  | 5 => let (a, s) := randExpr s (depth - 1) d; let (b, s) := randExpr s (depth - 1) d; (.div a b, s)
  | 6 => let (a, s) := randExpr s (depth - 1) d; (.neg a, s)
  | 7 => let (a, s) := randExpr s (depth - 1) d; (.pow a ((s >>> 50) % 7), s)
  | _ => let (a, s) := randExpr s (depth - 1) d; (.sqrt a, s)

def randHex (s : Nat) (len : Nat) : String × Nat := Id.run do
  let mut s := s
  let mut out := ByteArray.empty
  for _ in [0:len] do
    s := lcg s
    out := out.push (hexChar ((s >>> 37) % 16))
  return (String.fromUTF8! out, s)

def randomTest (n : Nat) : IO Unit := do
  let mut s := 12345
  let mut bad := 0
  let mut trues := 0
  for _ in [0:n] do
    s := lcg s
    let d := (s >>> 40) % 3 + 1
    let (e, s1) := randExpr s 4 d
    s := s1
    let mut bs : List (Rat × Rat) := []
    for _ in [0:d] do
      s := lcg s
      let a : Int := ((s >>> 20) % 201 : Nat) - 100
      let w := (s >>> 45) % 50 + 1
      let sc : Rat := if (s >>> 10) % 3 == 0 then ((10 ^ 100 : Nat) : Rat) else 1 / 7
      bs := bs ++ [((a : Rat) * sc, ((a + w : Int) : Rat) * sc)]
    s := lcg s
    let upper := (s >>> 30) % 2 == 0
    let c : Rat := (((s >>> 35) % 2001 : Nat) : Int) - 1000
    let cb := if upper then (KI.ofRat c).lo else (KI.ofRat c).hi
    let (hex, s2) := randHex s ((s >>> 50) % 12 + 1)
    s := s2
    let fe := compile e
    let E := env bs
    unless agree fe upper cb d 0 hex E do bad := bad + 1
    if checkGridSpec fe upper cb d 0 hex E then trues := trues + 1
    -- also a subtree start depth l0 > 0
    unless agree fe upper cb d 3 hex E do bad := bad + 1
  if bad > 0 then throw <| .userError s!"random: {bad} disagreements"
  IO.println s!"random: {n} expressions × 2 start depths agree ({trues} accepted at depth 0)"

end RealFP.Grid.Tests

open RealFP.Grid.Tests in
#eval do
  mutationTest "Nesbitt (div)" eNES false (3/2 - 1/16) [(-1,1),(-1,1),(-1,1)] 400
  mutationTest "power means (sqrt)" ePM true (1/16) [(-1,1),(-1,1),(-1,1)] 400
  mutationTest "polynomial, box [1/3,7/5]x[-2/7,5/11]" ePoly false (-1/3) [(1/3, 7/5), (-2/7, 5/11)] 400
  -- a larger certificate: the multithreaded path of the C checker
  mutationTest "Nesbitt 1/64 (threaded)" eNES false (3/2 - 1/64) [(-1,1),(-1,1),(-1,1)] 64
  randomTest 3000
