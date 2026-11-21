import Interval64
open Interval64 Interval64.Spec
def xs : List UInt64 := [0x3FB999999999999A, 0x400921FB54442D18, 0xC00AAAAAAAAAAAAB, 0x3F50624DD2F1A9FC, 0x41D0000000400000, 0xBFE5555555555555, 0x0000000000000003, 0x7FEFFFFFFFFFFFFF]
#eval do
  let mut out := ""
  for a in xs do
    for b in xs.take 3 do
      out := out ++ s!"{a} {b} {(addDown a b).toNat} {(mulUp a b).toNat} {(divDown a b).toNat} {(sqrtUp a).toNat} {(subUp a b).toNat}\n"
  IO.println out
