import Interval64
import Interval64.Kernel.Nat
open Interval64
def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13); let s := s ^^^ (s >>> 7); s ^^^ (s <<< 17)
def specials : Array UInt64 := #[0, 0x8000000000000000, 1, 0x8000000000000001, 0x000FFFFFFFFFFFFF,
  0x0010000000000000, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000, 0xFFF0000000000000,
  0x7FF8000000000000, 0x7FF0000000000001, 0x3FF0000000000000, 0xBFF0000000000000, 0x4000000000000000,
  0x3CA0000000000000, 0x7FE0000000000000, 0x0000000000000002, 0x3FF0000000000001, 0x43E0000000000000]
def gen (s : UInt64) : UInt64 :=
  match (s >>> 3) % 6 with
  | 0 => specials[((s >>> 8) % specials.size.toUInt64).toNat]!
  | 1 => s  -- anything
  | 2 => (s &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (((s >>> 20) % 3) <<< 52) -- subnormal-ish
  | 3 => (s &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (((2046 : UInt64) - (s >>> 20) % 4) <<< 52) -- huge
  | _ => (s &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (((993 : UInt64) + (s >>> 20) % 60) <<< 52)
def main (args : List String) : IO Unit := do
  let n := args.head!.toNat!
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  let mut bad := 0
  for _ in [0:n] do
    s := xorshift s; let a := gen s
    s := xorshift s; let b := if s % 7 == 0 then a else gen s
    s := xorshift s; let b := if s % 11 == 0 then b ^^^ 0x8000000000000000 else b
    for up in [false, true] do
      let chk (nm : String) (x y : Nat) : IO Nat := do
        if x != y then IO.println s!"MISMATCH {nm} up={up} a={a.toNat} b={b.toNat} spec={x} kf={y}"; return 1
        return 0
      bad := bad + (← chk "add" (Spec.add a b up).toNat (KF.add a.toNat b.toNat up))
      bad := bad + (← chk "sub" (Spec.sub a b up).toNat (KF.sub a.toNat b.toNat up))
      bad := bad + (← chk "mul" (Spec.mul a b up).toNat (KF.mul a.toNat b.toNat up))
      bad := bad + (← chk "div" (Spec.div a b up).toNat (KF.div a.toNat b.toNat up))
      bad := bad + (← chk "sqrt" (Spec.sqrt a up).toNat (KF.sqrt a.toNat up))
    let fa := Float.ofBits a; let fb := Float.ofBits b
    let c := KF.cmp a.toNat b.toNat
    let ok := (KF.lt a.toNat b.toNat == decide (fa < fb)) && (KF.le a.toNat b.toNat == decide (fa ≤ fb))
      && (KF.beq a.toNat b.toNat == (fa == fb))
    if !ok then IO.println s!"CMP MISMATCH {a} {b} {c}"; bad := bad + 1
  IO.println s!"done n={n} bad={bad}"
