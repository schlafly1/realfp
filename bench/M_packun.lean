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
example : packN (unpackN 4505897082957579473) = 4505897082957579473 := by decide +kernel
example : packN (unpackN 4498846036807243939) = 4498846036807243939 := by decide +kernel
example : packN (unpackN 4645102323371722262) = 4645102323371722262 := by decide +kernel
example : packN (unpackN 4481336958544784514) = 4481336958544784514 := by decide +kernel
example : packN (unpackN 4650113706917946669) = 4650113706917946669 := by decide +kernel
example : packN (unpackN 4557918350709297555) = 4557918350709297555 := by decide +kernel
example : packN (unpackN 4436128545333969438) = 4436128545333969438 := by decide +kernel
example : packN (unpackN 4645162169006909433) = 4645162169006909433 := by decide +kernel
example : packN (unpackN 4670494388798978528) = 4670494388798978528 := by decide +kernel
example : packN (unpackN 4731893400900168761) = 4731893400900168761 := by decide +kernel
example : packN (unpackN 4559613429815833149) = 4559613429815833149 := by decide +kernel
example : packN (unpackN 4690857336527801079) = 4690857336527801079 := by decide +kernel
example : packN (unpackN 4437720125174029887) = 4437720125174029887 := by decide +kernel
example : packN (unpackN 4789996051885290685) = 4789996051885290685 := by decide +kernel
example : packN (unpackN 4497589081529572362) = 4497589081529572362 := by decide +kernel
example : packN (unpackN 4716978823899981130) = 4716978823899981130 := by decide +kernel
example : packN (unpackN 4598486200317187144) = 4598486200317187144 := by decide +kernel
example : packN (unpackN 4705399515306438488) = 4705399515306438488 := by decide +kernel
example : packN (unpackN 4667287525435154863) = 4667287525435154863 := by decide +kernel
example : packN (unpackN 4634982846068197775) = 4634982846068197775 := by decide +kernel
example : packN (unpackN 4682782140399030398) = 4682782140399030398 := by decide +kernel
example : packN (unpackN 4642934873455212934) = 4642934873455212934 := by decide +kernel
example : packN (unpackN 4453101663540172301) = 4453101663540172301 := by decide +kernel
example : packN (unpackN 4523705282171234552) = 4523705282171234552 := by decide +kernel
example : packN (unpackN 4659818924551342633) = 4659818924551342633 := by decide +kernel
example : packN (unpackN 4759936698885876986) = 4759936698885876986 := by decide +kernel
example : packN (unpackN 4580212243517012095) = 4580212243517012095 := by decide +kernel
example : packN (unpackN 4648878991281998568) = 4648878991281998568 := by decide +kernel
example : packN (unpackN 4728113889690693264) = 4728113889690693264 := by decide +kernel
example : packN (unpackN 4460363624206908566) = 4460363624206908566 := by decide +kernel
example : packN (unpackN 4719636625868756445) = 4719636625868756445 := by decide +kernel
example : packN (unpackN 4632817611490965935) = 4632817611490965935 := by decide +kernel
example : packN (unpackN 4430021054899531598) = 4430021054899531598 := by decide +kernel
example : packN (unpackN 4688499187515399172) = 4688499187515399172 := by decide +kernel
example : packN (unpackN 4559238998683790879) = 4559238998683790879 := by decide +kernel
example : packN (unpackN 4743918765377272401) = 4743918765377272401 := by decide +kernel
example : packN (unpackN 4476870393421558593) = 4476870393421558593 := by decide +kernel
example : packN (unpackN 4471651079419188822) = 4471651079419188822 := by decide +kernel
example : packN (unpackN 4433789861509235050) = 4433789861509235050 := by decide +kernel
example : packN (unpackN 4581823641782781839) = 4581823641782781839 := by decide +kernel
example : packN (unpackN 4625822956068541148) = 4625822956068541148 := by decide +kernel
example : packN (unpackN 4523912804731533291) = 4523912804731533291 := by decide +kernel
example : packN (unpackN 4730294125670399794) = 4730294125670399794 := by decide +kernel
example : packN (unpackN 4584256408624816367) = 4584256408624816367 := by decide +kernel
example : packN (unpackN 4615953366921131358) = 4615953366921131358 := by decide +kernel
example : packN (unpackN 4492899115885980259) = 4492899115885980259 := by decide +kernel
example : packN (unpackN 4651506113402194636) = 4651506113402194636 := by decide +kernel
example : packN (unpackN 4536104460667575841) = 4536104460667575841 := by decide +kernel
example : packN (unpackN 4575041630642096662) = 4575041630642096662 := by decide +kernel
example : packN (unpackN 4436206540582689941) = 4436206540582689941 := by decide +kernel
example : packN (unpackN 4652536604059927636) = 4652536604059927636 := by decide +kernel
example : packN (unpackN 4519097414842187927) = 4519097414842187927 := by decide +kernel
example : packN (unpackN 4791387254742310311) = 4791387254742310311 := by decide +kernel
example : packN (unpackN 4556696147814250788) = 4556696147814250788 := by decide +kernel
example : packN (unpackN 4758694733716040771) = 4758694733716040771 := by decide +kernel
example : packN (unpackN 4787855893588997325) = 4787855893588997325 := by decide +kernel
example : packN (unpackN 4600934903740434947) = 4600934903740434947 := by decide +kernel
example : packN (unpackN 4468259398900750768) = 4468259398900750768 := by decide +kernel
example : packN (unpackN 4606427364228876176) = 4606427364228876176 := by decide +kernel
example : packN (unpackN 4752472066766834296) = 4752472066766834296 := by decide +kernel
example : packN (unpackN 4431883555605061015) = 4431883555605061015 := by decide +kernel
example : packN (unpackN 4766768288753852294) = 4766768288753852294 := by decide +kernel
example : packN (unpackN 4752842495706688984) = 4752842495706688984 := by decide +kernel
example : packN (unpackN 4783159884076387528) = 4783159884076387528 := by decide +kernel
example : packN (unpackN 4646336088855406397) = 4646336088855406397 := by decide +kernel
example : packN (unpackN 4485516329829384830) = 4485516329829384830 := by decide +kernel
example : packN (unpackN 4488252014385103356) = 4488252014385103356 := by decide +kernel
example : packN (unpackN 4715423735768867649) = 4715423735768867649 := by decide +kernel
example : packN (unpackN 4611848983579896449) = 4611848983579896449 := by decide +kernel
example : packN (unpackN 4518327687770475846) = 4518327687770475846 := by decide +kernel
example : packN (unpackN 4622612017640026939) = 4622612017640026939 := by decide +kernel
example : packN (unpackN 4581029163240593017) = 4581029163240593017 := by decide +kernel
example : packN (unpackN 4643799588691600713) = 4643799588691600713 := by decide +kernel
example : packN (unpackN 4450754539102771869) = 4450754539102771869 := by decide +kernel
example : packN (unpackN 4523532272255110221) = 4523532272255110221 := by decide +kernel
example : packN (unpackN 4583153316989857845) = 4583153316989857845 := by decide +kernel
example : packN (unpackN 4772627626745054208) = 4772627626745054208 := by decide +kernel
example : packN (unpackN 4621719252470918894) = 4621719252470918894 := by decide +kernel
example : packN (unpackN 4594890709829519059) = 4594890709829519059 := by decide +kernel
example : packN (unpackN 4763193648826401839) = 4763193648826401839 := by decide +kernel
example : packN (unpackN 4450215698183413254) = 4450215698183413254 := by decide +kernel
example : packN (unpackN 4644538235249360879) = 4644538235249360879 := by decide +kernel
example : packN (unpackN 4500129059036270181) = 4500129059036270181 := by decide +kernel
example : packN (unpackN 4781724284460019107) = 4781724284460019107 := by decide +kernel
example : packN (unpackN 4470857482205921328) = 4470857482205921328 := by decide +kernel
example : packN (unpackN 4594701290760647774) = 4594701290760647774 := by decide +kernel
example : packN (unpackN 4690743854663599731) = 4690743854663599731 := by decide +kernel
example : packN (unpackN 4485997325763332870) = 4485997325763332870 := by decide +kernel
example : packN (unpackN 4593802657954535658) = 4593802657954535658 := by decide +kernel
example : packN (unpackN 4477614780653069459) = 4477614780653069459 := by decide +kernel
example : packN (unpackN 4451714855578872200) = 4451714855578872200 := by decide +kernel
example : packN (unpackN 4766267751554059253) = 4766267751554059253 := by decide +kernel
example : packN (unpackN 4491596484205002577) = 4491596484205002577 := by decide +kernel
example : packN (unpackN 4563072670212761782) = 4563072670212761782 := by decide +kernel
example : packN (unpackN 4677568813047043436) = 4677568813047043436 := by decide +kernel
example : packN (unpackN 4481438495134593670) = 4481438495134593670 := by decide +kernel
example : packN (unpackN 4443433799610063519) = 4443433799610063519 := by decide +kernel
example : packN (unpackN 4686565394774373756) = 4686565394774373756 := by decide +kernel
example : packN (unpackN 4657300203468912107) = 4657300203468912107 := by decide +kernel
example : packN (unpackN 4611288424585139552) = 4611288424585139552 := by decide +kernel
