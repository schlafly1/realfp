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
example : Nat.log2 20303108522205623831264554019110957729 = 123 := by decide +kernel
example : Nat.log2 20239615662896245686761994385052235721 = 123 := by decide +kernel
example : Nat.log2 21576975594593372214592206692066396644 = 124 := by decide +kernel
example : Nat.log2 20082380936019419717765326990694216196 = 123 := by decide +kernel
example : Nat.log2 21623557487266167210630516715128195561 = 124 := by decide +kernel
example : Nat.log2 20774619691732563183592371521528978025 = 123 := by decide +kernel
example : Nat.log2 19679236470726879739250351005518035844 = 123 := by decide +kernel
example : Nat.log2 21577531576372975434561728094264381489 = 124 := by decide +kernel
example : Nat.log2 21813517835802744006951368416205046784 = 124 := by decide +kernel
example : Nat.log2 22390815157482565238934458598280275121 = 124 := by decide +kernel
example : Nat.log2 20790074629356905605673099569007256201 = 123 := by decide +kernel
example : Nat.log2 22004142551656696023030305066993564241 = 124 := by decide +kernel
example : Nat.log2 19693359909374607488813038151569232769 = 123 := by decide +kernel
example : Nat.log2 22944062177076672372057909466947769225 = 124 := by decide +kernel
example : Nat.log2 20228307546294022307141605530594259044 = 123 := by decide +kernel
example : Nat.log2 22249889225120849192429186014356076900 = 124 := by decide +kernel
example : Nat.log2 21146075334507601409103433284318876736 = 123 := by decide +kernel
example : Nat.log2 22140784598646066250718971186927726144 = 124 := by decide +kernel
example : Nat.log2 21783572845082611352235327904792548769 = 124 := by decide +kernel
example : Nat.log2 21483065983346450750525386236514950625 = 124 := by decide +kernel
example : Nat.log2 21928448574440124442302208698528038404 = 124 := by decide +kernel
example : Nat.log2 21556844239146574141025713579280888356 = 124 := by decide +kernel
example : Nat.log2 19830114425824249913071059240767634601 = 123 := by decide +kernel
example : Nat.log2 20463909479943928818715928599798640704 = 123 := by decide +kernel
example : Nat.log2 21713912409606831446026752482963372689 = 124 := by decide +kernel
example : Nat.log2 22656997377400579955934842490324444196 = 124 := by decide +kernel
example : Nat.log2 20978344195663141303863459676376289025 = 123 := by decide +kernel
example : Nat.log2 21612075875583132517614092968354050624 = 124 := by decide +kernel
example : Nat.log2 22355060953886057150591344576934973696 = 124 := by decide +kernel
example : Nat.log2 19894843660148188258603617522684176356 = 123 := by decide +kernel
example : Nat.log2 22274969880241820097808334010729038025 = 124 := by decide +kernel
example : Nat.log2 21462999021340858581379210119330424225 = 124 := by decide +kernel
example : Nat.log2 19625086546853158752565685679800433604 = 123 := by decide +kernel
example : Nat.log2 21982024631332558167070582634498285584 = 124 := by decide +kernel
example : Nat.log2 20786660247119176088494568450203592641 = 123 := by decide +kernel
example : Nat.log2 22504765252498624470383343994556304801 = 124 := by decide +kernel
example : Nat.log2 20042368519494500817010585745332139649 = 123 := by decide +kernel
example : Nat.log2 19995663376070796537577797144489747684 = 123 := by decide +kernel
example : Nat.log2 19658492536022081724370976436148502500 = 123 := by decide +kernel
example : Nat.log2 20993107884399633552964059005468221921 = 123 := by decide +kernel
example : Nat.log2 21398238020890696367702684864969157904 = 124 := by decide +kernel
example : Nat.log2 20465787064813928059949456883841290681 = 123 := by decide +kernel
example : Nat.log2 22375682515351892039368256383795242436 = 124 := by decide +kernel
example : Nat.log2 21015406820017699332876454964471078689 = 123 := by decide +kernel
example : Nat.log2 21307025485590528741824985034690924164 = 124 := by decide +kernel
example : Nat.log2 20186142465529023068922102589337707081 = 123 := by decide +kernel
example : Nat.log2 21636509123017990385101380261227172496 = 124 := by decide +kernel
example : Nat.log2 20576243678088279099942359223486857281 = 123 := by decide +kernel
example : Nat.log2 20931005922108294818680366243351542244 = 123 := by decide +kernel
example : Nat.log2 19679928470708637454452355847342583481 = 123 := by decide +kernel
example : Nat.log2 21646096852117483856165967609556548496 = 124 := by decide +kernel
example : Nat.log2 20422241444833345962724722060384557329 = 123 := by decide +kernel
example : Nat.log2 22957391824907052841827376585816916721 = 124 := by decide +kernel
example : Nat.log2 20763479783505232466405632017758620944 = 123 := by decide +kernel
example : Nat.log2 22645175568696780180654632671734274441 = 124 := by decide +kernel
example : Nat.log2 22923564057774896076271890298857155625 = 124 := by decide +kernel
example : Nat.log2 21168601988457005391654754192738892809 = 123 := by decide +kernel
example : Nat.log2 19965342055864898573554787274052589824 = 123 := by decide +kernel
example : Nat.log2 21219173061916591456240544431940382976 = 123 := by decide +kernel
example : Nat.log2 22585990745399025498569585909521815616 = 124 := by decide +kernel
example : Nat.log2 19641591850442557949666315481872830225 = 123 := by decide +kernel
example : Nat.log2 22722079918669329362318798625169062436 = 124 := by decide +kernel
example : Nat.log2 22589511788995387893306559480106952256 = 124 := by decide +kernel
example : Nat.log2 22878618476637640975140888558433950784 = 124 := by decide +kernel
example : Nat.log2 21588439050600154969306029976028521609 = 124 := by decide +kernel
example : Nat.log2 20119856745166074637667657336234128900 = 123 := by decide +kernel
example : Nat.log2 20144406144631938022478622562802462736 = 123 := by decide +kernel
example : Nat.log2 22235221007852423747927655491678787201 = 124 := by decide +kernel
example : Nat.log2 21269151047346923986468202625562809601 = 124 := by decide +kernel
example : Nat.log2 20415285094073294663886729433269415716 = 123 := by decide +kernel
example : Nat.log2 21368541865630000728259886408645709721 = 124 := by decide +kernel
example : Nat.log2 20985828194460807823640194541829162289 = 123 := by decide +kernel
example : Nat.log2 21564874619932279956658124034222108369 = 124 := by decide +kernel
example : Nat.log2 19809215967343927245877088839057753161 = 123 := by decide +kernel
example : Nat.log2 20462344218133480619286185448858668841 = 123 := by decide +kernel
example : Nat.log2 21005294327035136386340546593308044025 = 123 := by decide +kernel
example : Nat.log2 22777974463570128468491806188858507264 = 124 := by decide +kernel
example : Nat.log2 21360288848660349341282459180726183236 = 124 := by decide +kernel
example : Nat.log2 21113020635277621515963147531244245481 = 123 := by decide +kernel
example : Nat.log2 22688013736220171885123577343502581921 = 124 := by decide +kernel
example : Nat.log2 19804419760358084288377763005742868516 = 123 := by decide +kernel
example : Nat.log2 21571735418693247498719597977975652641 = 124 := by decide +kernel
example : Nat.log2 20251161547982666471987894884029772761 = 123 := by decide +kernel
example : Nat.log2 22864887132594681726303406354805077449 = 124 := by decide +kernel
example : Nat.log2 19988566626196670144026755785325283584 = 123 := by decide +kernel
example : Nat.log2 21111279951317562717445441956091155076 = 123 := by decide +kernel
example : Nat.log2 22003077910064326035848971150983272361 = 124 := by decide +kernel
example : Nat.log2 20124172006755774051391822570422436900 = 123 := by decide +kernel
example : Nat.log2 21103022860230156533754424934393492964 = 123 := by decide +kernel
example : Nat.log2 20049034123922835324396507758278552681 = 123 := by decide +kernel
example : Nat.log2 19817765155381618969108155023932840000 = 123 := by decide +kernel
example : Nat.log2 22717308279504187500741081661834918009 = 124 := by decide +kernel
example : Nat.log2 20174438976922739964170304592576640929 = 123 := by decide +kernel
example : Nat.log2 20821632193642623845374663455879815524 = 123 := by decide +kernel
example : Nat.log2 21879650000790326787182136020870686096 = 124 := by decide +kernel
example : Nat.log2 20083290985674211532860768756004068900 = 123 := by decide +kernel
example : Nat.log2 19744103931517126121095134859214663361 = 123 := by decide +kernel
example : Nat.log2 21963895199496681730382454441981547536 = 124 := by decide +kernel
example : Nat.log2 21690445185231570111460394006091179449 = 124 := by decide +kernel
example : Nat.log2 21263980934712898261466680391314760704 = 123 := by decide +kernel
