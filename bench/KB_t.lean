import Interval64
import Lean
open Lean Elab Command Meta
/-- `#kbench n "label" t₁ = v₁` : time `Kernel.isDefEq t₁ v₁` (n repetitions), print µs/rep. -/
elab "#kbench " n:num lbl:str t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some (_, lhs, rhs) := e.eq? | throwError "need equation"
  let env ← getEnv
  let t0 ← IO.monoNanosNow
  let mut ok := true
  for _ in [0:n.getNat] do
    match Kernel.isDefEq env {} lhs rhs with
    | .ok b => ok := ok && b
    | .error _ => ok := false
  let t1 ← IO.monoNanosNow
  logInfo m!"{lbl.getString}: {(t1 - t0) / 1000 / n.getNat} µs  ok={ok}"
open Float.Model Float.Model.UnpackedFloat Interval64.Spec
namespace X
def fshift (m : Nat) (acc : Accuracy) (n : Nat) : ExtendedMantissa :=
  if n = 0 then ExtendedMantissa.ofMantissaAndAccuracy m acc else
  let r := m % 2 ^ n
  { mantissa := m >>> n, roundBit := decide (2 ^ (n-1) ≤ r),
    stickyBit := (r % 2 ^ (n-1) != 0) || (match acc with | .exact => false | _ => true) }
def tgt (m : Nat) (e : Int) : Int := max (m.log2 + 1 + e - 53) (-1074)
def shiftT (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) : ExtendedMantissa × Int :=
  let n := (tgt mantissa exponent - exponent).toNat
  (fshift mantissa accuracy n, exponent + n)
def roundD (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (up : Bool) : UnpackedFloat :=
  let (mantissa, exponent) :=
    match accuracy with
    | .exact =>
      let k := (exponent - tgt mantissa exponent).toNat
      (mantissa <<< k, exponent - k)
    | .inexact _ => (mantissa, exponent)
  let (em₁, e₁) := shiftT mantissa exponent accuracy
  let rounded := roundMantissaDirected em₁.mantissa up sign em₁.accuracy
  let (finalEM, finalE) := shiftT rounded e₁ Accuracy.exact
  let finalM := finalEM.mantissa
  if h : finalM = 0 then .zero sign else .finite sign finalM finalE (Nat.pos_of_ne_zero h)
def unpackN (b : Nat) : UnpackedFloat :=
  let m := b % 2 ^ 52
  let E := (b >>> 52) % 2048
  let s : Sign := if b >>> 63 % 2 = 0 then .positive else .negative
  if E = 2047 then (if m = 0 then .infinity s else .notANumber)
  else if E = 0 then (if h : m = 0 then .zero s else .finite s m (-1074) (Nat.pos_of_ne_zero h))
  else .finite s (m + 2 ^ 52) ((E : Int) - 1075) (by omega)
def sbit : Sign → Nat | .negative => 2 ^ 63 | .positive => 0
def packN : UnpackedFloat → Nat
  | .notANumber => 0x7FF8000000000000
  | .infinity s => sbit s + 0x7FF0000000000000
  | .zero s => sbit s
  | .finite s m e _ =>
    let biased := (e + 1075).toNat
    if 2048 ≤ biased + 1 then sbit s + 0x7FF0000000000000
    else if m.log2 = 52 then sbit s + biased * 2 ^ 52 + m % 2 ^ 52
    else sbit s + m % 2 ^ 52
def packDirN (up : Bool) (u : UnpackedFloat) : Nat :=
  match u with
  | .finite s _m e _ =>
    if 2048 ≤ (e + 1075).toNat + 1 then
      if awayFromZero up s then sbit s + 0x7FF0000000000000 else sbit s + 0x7FEFFFFFFFFFFFFF
    else packN u
  | _ => packN u
def mulU (x y : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x, y with
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ => roundD (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) Accuracy.exact up
  | x, y => Interval64.Spec.mulU x y up
def mulUp (a b : Nat) : Nat := packDirN true (mulU (unpackN a) (unpackN b) true)
end X

open X Interval64
#kbench 20 "Spec.mulUp" (Spec.mulUp 4591870180066957722 4614256656552045848).toNat = 4596373779694328218
#kbench 20 "X.mulUp" X.mulUp 4591870180066957722 4614256656552045848 = 0
#kbench 20 "unpackN" packN (unpackN 4591870180066957722) = 4591870180066957722
#kbench 20 "spec pack/unpack" (packBits (unpackBits 4591870180066957722)).toNat = 4591870180066957722
#kbench 20 "log2" Nat.log2 (4591870180066957722*4614256656552045848) = 0
#kbench 20 "tgt" tgt (4591870180066957722*4614256656552045848) (-1075) = 0
#kbench 20 "lit" (3:Nat) = 3
