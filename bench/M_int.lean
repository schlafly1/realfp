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
example : ((((4505897082957579473 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1000 := by decide +kernel
example : ((((4498846036807243939 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 998 := by decide +kernel
example : ((((4645102323371722262 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1031 := by decide +kernel
example : ((((4481336958544784514 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 995 := by decide +kernel
example : ((((4650113706917946669 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1032 := by decide +kernel
example : ((((4557918350709297555 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1012 := by decide +kernel
example : ((((4436128545333969438 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 985 := by decide +kernel
example : ((((4645162169006909433 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1031 := by decide +kernel
example : ((((4670494388798978528 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1037 := by decide +kernel
example : ((((4731893400900168761 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1050 := by decide +kernel
example : ((((4559613429815833149 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1012 := by decide +kernel
example : ((((4690857336527801079 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1041 := by decide +kernel
example : ((((4437720125174029887 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 985 := by decide +kernel
example : ((((4789996051885290685 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1063 := by decide +kernel
example : ((((4497589081529572362 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 998 := by decide +kernel
example : ((((4716978823899981130 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1047 := by decide +kernel
example : ((((4598486200317187144 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1021 := by decide +kernel
example : ((((4705399515306438488 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1044 := by decide +kernel
example : ((((4667287525435154863 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1036 := by decide +kernel
example : ((((4634982846068197775 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1029 := by decide +kernel
example : ((((4682782140399030398 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1039 := by decide +kernel
example : ((((4642934873455212934 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1030 := by decide +kernel
example : ((((4453101663540172301 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 988 := by decide +kernel
example : ((((4523705282171234552 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1004 := by decide +kernel
example : ((((4659818924551342633 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1034 := by decide +kernel
example : ((((4759936698885876986 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1056 := by decide +kernel
example : ((((4580212243517012095 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1017 := by decide +kernel
example : ((((4648878991281998568 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1032 := by decide +kernel
example : ((((4728113889690693264 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1049 := by decide +kernel
example : ((((4460363624206908566 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 990 := by decide +kernel
example : ((((4719636625868756445 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1047 := by decide +kernel
example : ((((4632817611490965935 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1028 := by decide +kernel
example : ((((4430021054899531598 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 983 := by decide +kernel
example : ((((4688499187515399172 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1041 := by decide +kernel
example : ((((4559238998683790879 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1012 := by decide +kernel
example : ((((4743918765377272401 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1053 := by decide +kernel
example : ((((4476870393421558593 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 994 := by decide +kernel
example : ((((4471651079419188822 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 992 := by decide +kernel
example : ((((4433789861509235050 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 984 := by decide +kernel
example : ((((4581823641782781839 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1017 := by decide +kernel
example : ((((4625822956068541148 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1027 := by decide +kernel
example : ((((4523912804731533291 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1004 := by decide +kernel
example : ((((4730294125670399794 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1050 := by decide +kernel
example : ((((4584256408624816367 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1017 := by decide +kernel
example : ((((4615953366921131358 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1024 := by decide +kernel
example : ((((4492899115885980259 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 997 := by decide +kernel
example : ((((4651506113402194636 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1032 := by decide +kernel
example : ((((4536104460667575841 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1007 := by decide +kernel
example : ((((4575041630642096662 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1015 := by decide +kernel
example : ((((4436206540582689941 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 985 := by decide +kernel
example : ((((4652536604059927636 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1033 := by decide +kernel
example : ((((4519097414842187927 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1003 := by decide +kernel
example : ((((4791387254742310311 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1063 := by decide +kernel
example : ((((4556696147814250788 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1011 := by decide +kernel
example : ((((4758694733716040771 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1056 := by decide +kernel
example : ((((4787855893588997325 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1063 := by decide +kernel
example : ((((4600934903740434947 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1021 := by decide +kernel
example : ((((4468259398900750768 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 992 := by decide +kernel
example : ((((4606427364228876176 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1022 := by decide +kernel
example : ((((4752472066766834296 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1055 := by decide +kernel
example : ((((4431883555605061015 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 984 := by decide +kernel
example : ((((4766768288753852294 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1058 := by decide +kernel
example : ((((4752842495706688984 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1055 := by decide +kernel
example : ((((4783159884076387528 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1062 := by decide +kernel
example : ((((4646336088855406397 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1031 := by decide +kernel
example : ((((4485516329829384830 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 995 := by decide +kernel
example : ((((4488252014385103356 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 996 := by decide +kernel
example : ((((4715423735768867649 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1047 := by decide +kernel
example : ((((4611848983579896449 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1024 := by decide +kernel
example : ((((4518327687770475846 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1003 := by decide +kernel
example : ((((4622612017640026939 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1026 := by decide +kernel
example : ((((4581029163240593017 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1017 := by decide +kernel
example : ((((4643799588691600713 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1031 := by decide +kernel
example : ((((4450754539102771869 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 988 := by decide +kernel
example : ((((4523532272255110221 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1004 := by decide +kernel
example : ((((4583153316989857845 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1017 := by decide +kernel
example : ((((4772627626745054208 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1059 := by decide +kernel
example : ((((4621719252470918894 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1026 := by decide +kernel
example : ((((4594890709829519059 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1020 := by decide +kernel
example : ((((4763193648826401839 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1057 := by decide +kernel
example : ((((4450215698183413254 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 988 := by decide +kernel
example : ((((4644538235249360879 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1031 := by decide +kernel
example : ((((4500129059036270181 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 999 := by decide +kernel
example : ((((4781724284460019107 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1061 := by decide +kernel
example : ((((4470857482205921328 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 992 := by decide +kernel
example : ((((4594701290760647774 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1020 := by decide +kernel
example : ((((4690743854663599731 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1041 := by decide +kernel
example : ((((4485997325763332870 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 996 := by decide +kernel
example : ((((4593802657954535658 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1020 := by decide +kernel
example : ((((4477614780653069459 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 994 := by decide +kernel
example : ((((4451714855578872200 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 988 := by decide +kernel
example : ((((4766267751554059253 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1058 := by decide +kernel
example : ((((4491596484205002577 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 997 := by decide +kernel
example : ((((4563072670212761782 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1013 := by decide +kernel
example : ((((4677568813047043436 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1038 := by decide +kernel
example : ((((4481438495134593670 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 995 := by decide +kernel
example : ((((4443433799610063519 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 986 := by decide +kernel
example : ((((4686565394774373756 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1040 := by decide +kernel
example : ((((4657300203468912107 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1034 := by decide +kernel
example : ((((4611288424585139552 >>> 52) % 2048 : Nat) : Int) - 1075 + 1075).toNat = 1023 := by decide +kernel
