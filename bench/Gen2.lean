import Interval64
open Interval64 Interval64.Spec
def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13); let s := s ^^^ (s >>> 7); s ^^^ (s <<< 17)
/-- random float bits with exponent in [1023-40, 1023+40], random sign -/
def rnd (s : UInt64) : UInt64 :=
  let e : UInt64 := (983 : UInt64) + (s >>> 20) % 81
  ((s >>> 63) <<< 63) ||| (e <<< 52) ||| (s &&& 0xFFFFFFFFFFFFF)
def ops : List (String × (UInt64 → UInt64 → UInt64) × Bool) :=
  [("addDown", addDown, true), ("subUp", subUp, true), ("mulUp", mulUp, true), ("mulDown", mulDown, true),
   ("divDown", divDown, true), ("divUp", divUp, true), ("sqrtUp", fun a _ => sqrtUp (a &&& 0x7FFFFFFFFFFFFFFF), false),
   ("sqrtDown", fun a _ => sqrtDown (a &&& 0x7FFFFFFFFFFFFFFF), false)]
def main : IO Unit := do
  for (nm, f, bin) in ops do
    let h ← IO.FS.Handle.mk s!"bench/R_{nm}.lean" .write
    h.putStrLn "import Interval64\nopen Interval64 Interval64.Spec"
    let mut s : UInt64 := 0x1234567 + nm.length.toUInt64
    for _ in [0:100] do
      s := xorshift s; let a := rnd s
      s := xorshift s; let b := rnd s
      let a := if bin then a else a &&& 0x7FFFFFFFFFFFFFFF
      let call := if bin then s!"Spec.{nm} {a} {b}" else s!"Spec.{nm} {a}"
      h.putStrLn s!"example : ({call}).toNat = {(f a b).toNat} := by decide +kernel"
