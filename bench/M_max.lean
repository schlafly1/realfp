import Interval64
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

open X
example : tgt 4505897082957579473 (-1075) = -1066 := by decide +kernel
example : tgt 4498846036807243939 (-1075) = -1066 := by decide +kernel
example : tgt 4645102323371722262 (-1075) = -1065 := by decide +kernel
example : tgt 4481336958544784514 (-1075) = -1066 := by decide +kernel
example : tgt 4650113706917946669 (-1075) = -1065 := by decide +kernel
example : tgt 4557918350709297555 (-1075) = -1066 := by decide +kernel
example : tgt 4436128545333969438 (-1075) = -1066 := by decide +kernel
example : tgt 4645162169006909433 (-1075) = -1065 := by decide +kernel
example : tgt 4670494388798978528 (-1075) = -1065 := by decide +kernel
example : tgt 4731893400900168761 (-1075) = -1065 := by decide +kernel
example : tgt 4559613429815833149 (-1075) = -1066 := by decide +kernel
example : tgt 4690857336527801079 (-1075) = -1065 := by decide +kernel
example : tgt 4437720125174029887 (-1075) = -1066 := by decide +kernel
example : tgt 4789996051885290685 (-1075) = -1065 := by decide +kernel
example : tgt 4497589081529572362 (-1075) = -1066 := by decide +kernel
example : tgt 4716978823899981130 (-1075) = -1065 := by decide +kernel
example : tgt 4598486200317187144 (-1075) = -1066 := by decide +kernel
example : tgt 4705399515306438488 (-1075) = -1065 := by decide +kernel
example : tgt 4667287525435154863 (-1075) = -1065 := by decide +kernel
example : tgt 4634982846068197775 (-1075) = -1065 := by decide +kernel
example : tgt 4682782140399030398 (-1075) = -1065 := by decide +kernel
example : tgt 4642934873455212934 (-1075) = -1065 := by decide +kernel
example : tgt 4453101663540172301 (-1075) = -1066 := by decide +kernel
example : tgt 4523705282171234552 (-1075) = -1066 := by decide +kernel
example : tgt 4659818924551342633 (-1075) = -1065 := by decide +kernel
example : tgt 4759936698885876986 (-1075) = -1065 := by decide +kernel
example : tgt 4580212243517012095 (-1075) = -1066 := by decide +kernel
example : tgt 4648878991281998568 (-1075) = -1065 := by decide +kernel
example : tgt 4728113889690693264 (-1075) = -1065 := by decide +kernel
example : tgt 4460363624206908566 (-1075) = -1066 := by decide +kernel
example : tgt 4719636625868756445 (-1075) = -1065 := by decide +kernel
example : tgt 4632817611490965935 (-1075) = -1065 := by decide +kernel
example : tgt 4430021054899531598 (-1075) = -1066 := by decide +kernel
example : tgt 4688499187515399172 (-1075) = -1065 := by decide +kernel
example : tgt 4559238998683790879 (-1075) = -1066 := by decide +kernel
example : tgt 4743918765377272401 (-1075) = -1065 := by decide +kernel
example : tgt 4476870393421558593 (-1075) = -1066 := by decide +kernel
example : tgt 4471651079419188822 (-1075) = -1066 := by decide +kernel
example : tgt 4433789861509235050 (-1075) = -1066 := by decide +kernel
example : tgt 4581823641782781839 (-1075) = -1066 := by decide +kernel
example : tgt 4625822956068541148 (-1075) = -1065 := by decide +kernel
example : tgt 4523912804731533291 (-1075) = -1066 := by decide +kernel
example : tgt 4730294125670399794 (-1075) = -1065 := by decide +kernel
example : tgt 4584256408624816367 (-1075) = -1066 := by decide +kernel
example : tgt 4615953366921131358 (-1075) = -1065 := by decide +kernel
example : tgt 4492899115885980259 (-1075) = -1066 := by decide +kernel
example : tgt 4651506113402194636 (-1075) = -1065 := by decide +kernel
example : tgt 4536104460667575841 (-1075) = -1066 := by decide +kernel
example : tgt 4575041630642096662 (-1075) = -1066 := by decide +kernel
example : tgt 4436206540582689941 (-1075) = -1066 := by decide +kernel
example : tgt 4652536604059927636 (-1075) = -1065 := by decide +kernel
example : tgt 4519097414842187927 (-1075) = -1066 := by decide +kernel
example : tgt 4791387254742310311 (-1075) = -1065 := by decide +kernel
example : tgt 4556696147814250788 (-1075) = -1066 := by decide +kernel
example : tgt 4758694733716040771 (-1075) = -1065 := by decide +kernel
example : tgt 4787855893588997325 (-1075) = -1065 := by decide +kernel
example : tgt 4600934903740434947 (-1075) = -1066 := by decide +kernel
example : tgt 4468259398900750768 (-1075) = -1066 := by decide +kernel
example : tgt 4606427364228876176 (-1075) = -1066 := by decide +kernel
example : tgt 4752472066766834296 (-1075) = -1065 := by decide +kernel
example : tgt 4431883555605061015 (-1075) = -1066 := by decide +kernel
example : tgt 4766768288753852294 (-1075) = -1065 := by decide +kernel
example : tgt 4752842495706688984 (-1075) = -1065 := by decide +kernel
example : tgt 4783159884076387528 (-1075) = -1065 := by decide +kernel
example : tgt 4646336088855406397 (-1075) = -1065 := by decide +kernel
example : tgt 4485516329829384830 (-1075) = -1066 := by decide +kernel
example : tgt 4488252014385103356 (-1075) = -1066 := by decide +kernel
example : tgt 4715423735768867649 (-1075) = -1065 := by decide +kernel
example : tgt 4611848983579896449 (-1075) = -1065 := by decide +kernel
example : tgt 4518327687770475846 (-1075) = -1066 := by decide +kernel
example : tgt 4622612017640026939 (-1075) = -1065 := by decide +kernel
example : tgt 4581029163240593017 (-1075) = -1066 := by decide +kernel
example : tgt 4643799588691600713 (-1075) = -1065 := by decide +kernel
example : tgt 4450754539102771869 (-1075) = -1066 := by decide +kernel
example : tgt 4523532272255110221 (-1075) = -1066 := by decide +kernel
example : tgt 4583153316989857845 (-1075) = -1066 := by decide +kernel
example : tgt 4772627626745054208 (-1075) = -1065 := by decide +kernel
example : tgt 4621719252470918894 (-1075) = -1065 := by decide +kernel
example : tgt 4594890709829519059 (-1075) = -1066 := by decide +kernel
example : tgt 4763193648826401839 (-1075) = -1065 := by decide +kernel
example : tgt 4450215698183413254 (-1075) = -1066 := by decide +kernel
example : tgt 4644538235249360879 (-1075) = -1065 := by decide +kernel
example : tgt 4500129059036270181 (-1075) = -1066 := by decide +kernel
example : tgt 4781724284460019107 (-1075) = -1065 := by decide +kernel
example : tgt 4470857482205921328 (-1075) = -1066 := by decide +kernel
example : tgt 4594701290760647774 (-1075) = -1066 := by decide +kernel
example : tgt 4690743854663599731 (-1075) = -1065 := by decide +kernel
example : tgt 4485997325763332870 (-1075) = -1066 := by decide +kernel
example : tgt 4593802657954535658 (-1075) = -1066 := by decide +kernel
example : tgt 4477614780653069459 (-1075) = -1066 := by decide +kernel
example : tgt 4451714855578872200 (-1075) = -1066 := by decide +kernel
example : tgt 4766267751554059253 (-1075) = -1065 := by decide +kernel
example : tgt 4491596484205002577 (-1075) = -1066 := by decide +kernel
example : tgt 4563072670212761782 (-1075) = -1066 := by decide +kernel
example : tgt 4677568813047043436 (-1075) = -1065 := by decide +kernel
example : tgt 4481438495134593670 (-1075) = -1066 := by decide +kernel
example : tgt 4443433799610063519 (-1075) = -1066 := by decide +kernel
example : tgt 4686565394774373756 (-1075) = -1065 := by decide +kernel
example : tgt 4657300203468912107 (-1075) = -1065 := by decide +kernel
example : tgt 4611288424585139552 (-1075) = -1066 := by decide +kernel
