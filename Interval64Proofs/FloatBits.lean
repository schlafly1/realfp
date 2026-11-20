/-
Bridge between Lean `Float` / `Interval64` and the bits-level value model.

`MemIv` is membership of a rational in a Lean interval. `hi_le_of_native`
turns a compiled `I.hi ≤ c` check (typically via `native_decide`) into a
rational upper bound, provided the constant `c` has a known rational value.
-/
import Interval64Proofs.ExactAdd
import Interval64.Interval

namespace Interval64Proofs.FloatBits

open Interval64
open Interval64.Spec
open Interval64.Directed
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Canonical
open Interval64Proofs.PackFinite
open Interval64Proofs.Pack
open Interval64Proofs.AddBits
open Interval64Proofs.ExactAdd
open Float.Model
open Float.Model.UnpackedFloat

/-! ### `toBits` / `ofBits` -/

theorem unpackBits_toBits (f : Float) :
    unpackBits f.toBits = f.toModel.unpack :=
  rfl

theorem toBits_ofModel (m : Float.Model) :
    (Float.ofModel m).toBits = m.toBits :=
  rfl

theorem toBits_ofBits (b : UInt64) :
    (Float.ofBits b).toBits = packBits (unpackBits b) := by
  simp only [Float.ofBits, toBits_ofModel, packBits, unpackBits,
    Float.Model.ofBits, Float.Model.pack]

theorem float_le_iff (a b : Float) :
    a ≤ b ↔ (unpackBits a.toBits).le (unpackBits b.toBits) = true :=
  Iff.rfl

theorem float_isNaN (f : Float) :
    f.isNaN = (unpackBits f.toBits).isNaN :=
  rfl

theorem bitsToEVal_none_iff_isNaN (f : Float) :
    bitsToEVal f.toBits = none ↔ f.isNaN = true := by
  simp only [bitsToEVal, float_isNaN]
  cases unpackBits f.toBits with
  | notANumber => simp [toEVal, UnpackedFloat.isNaN]
  | infinity s => cases s <;> simp [toEVal, UnpackedFloat.isNaN]
  | zero s => simp [toEVal, UnpackedFloat.isNaN]
  | finite s m e h => simp [toEVal, UnpackedFloat.isNaN]

theorem not_isNaN_of_bitsToEVal {f : Float} {ev : EVal}
    (h : bitsToEVal f.toBits = some ev) : f.isNaN = false := by
  cases hf : f.isNaN with
  | false => rfl
  | true =>
    have : bitsToEVal f.toBits = none := (bitsToEVal_none_iff_isNaN f).mpr hf
    simp [h] at this

theorem bitsToEVal_pack_unpack_of_some {b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    bitsToEVal (packBits (unpackBits b)) = some ev := by
  simp only [bitsToEVal] at h ⊢
  cases hu : unpackBits b with
  | notANumber =>
    simp [hu, toEVal] at h
  | infinity s =>
    rw [hu] at h
    rw [unpackBits_inf]
    exact h
  | zero s =>
    rw [hu] at h
    rw [unpackBits_zero]
    exact h
  | finite s m e hm =>
    have hc : IsCanonicalFinite m e := by
      simp [unpackBits] at hu
      exact unpack_finite_is_canonical hu
    rw [hu] at h
    cases hc with
    | inl hs => rw [unpackBits_pack_subnormal s hm hs]; exact h
    | inr hn => rw [unpackBits_pack_normal s hm hn]; exact h

theorem bitsToEVal_toBits_ofBits {b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    bitsToEVal (Float.ofBits b).toBits = some ev := by
  rw [toBits_ofBits]
  exact bitsToEVal_pack_unpack_of_some h

theorem addDown_toBits (a b : Float) :
    (Directed.addDown a b).toBits =
      packBits (unpackBits (Spec.addDown a.toBits b.toBits)) := by
  simp only [Directed.addDown, addDownSpec, toBits_ofBits]

theorem addUp_toBits (a b : Float) :
    (Directed.addUp a b).toBits =
      packBits (unpackBits (Spec.addUp a.toBits b.toBits)) := by
  simp only [Directed.addUp, addUpSpec, toBits_ofBits]

theorem mulDown_toBits (a b : Float) :
    (Directed.mulDown a b).toBits =
      packBits (unpackBits (Spec.mulDown a.toBits b.toBits)) := by
  simp only [Directed.mulDown, mulDownSpec, toBits_ofBits]

theorem mulUp_toBits (a b : Float) :
    (Directed.mulUp a b).toBits =
      packBits (unpackBits (Spec.mulUp a.toBits b.toBits)) := by
  simp only [Directed.mulUp, mulUpSpec, toBits_ofBits]

theorem divDown_toBits (a b : Float) :
    (Directed.divDown a b).toBits =
      packBits (unpackBits (Spec.divDown a.toBits b.toBits)) := by
  simp only [Directed.divDown, divDownSpec, toBits_ofBits]

theorem divUp_toBits (a b : Float) :
    (Directed.divUp a b).toBits =
      packBits (unpackBits (Spec.divUp a.toBits b.toBits)) := by
  simp only [Directed.divUp, divUpSpec, toBits_ofBits]

theorem sqrtDown_toBits (a : Float) :
    (Directed.sqrtDown a).toBits =
      packBits (unpackBits (Spec.sqrtDown a.toBits)) := by
  simp only [Directed.sqrtDown, sqrtDownSpec, toBits_ofBits]

theorem sqrtUp_toBits (a : Float) :
    (Directed.sqrtUp a).toBits =
      packBits (unpackBits (Spec.sqrtUp a.toBits)) := by
  simp only [Directed.sqrtUp, sqrtUpSpec, toBits_ofBits]

/-! ### Comparing finite floats by rational value -/

theorem mag_pow53_succ (e : Int) :
    mag (2 ^ 53) e = mag (2 ^ 52) (e + 1) := by
  have h : (2 ^ 53 : Nat) = 2 ^ 52 * 2 ^ 1 := by decide
  rw [h, mag_mul_two_pow_add]
  rfl

theorem canonical_isNormal_of_exp_lt {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂)
    (hlt : e₁ < e₂) : IsNormal m₂ e₂ := by
  cases hc₂ with
  | inl hs =>
    have hmin : spec64.minExponent ≤ e₁ := canonical_minExp_le hc₁
    have heq : e₂ = spec64.minExponent := hs.1
    exact (Int.not_le.mpr (heq ▸ hlt) hmin).elim
  | inr hn => exact hn

theorem mag_le_of_exp_lt {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂)
    (hlt : e₁ < e₂) : mag m₁ e₁ ≤ mag m₂ e₂ := by
  have hn : IsNormal m₂ e₂ := canonical_isNormal_of_exp_lt hc₁ hc₂ hlt
  have hm₁ : m₁ < 2 ^ 53 := canonical_mantissa_lt hc₁
  have hm₂ : 2 ^ 52 ≤ m₂ := hn.2.2.1
  have hstep : mag m₁ e₁ < mag (2 ^ 52) (e₁ + 1) := by
    have : mag m₁ e₁ < mag (2 ^ 53) e₁ := mag_lt_mag hm₁
    rwa [mag_pow53_succ] at this
  have hle₁ : mag (2 ^ 52) (e₁ + 1) ≤ mag m₂ (e₁ + 1) := mag_le_mag hm₂
  have hle₂ : mag m₂ (e₁ + 1) ≤ mag m₂ e₂ :=
    mag_mono_exp (Int.add_one_le_of_lt hlt)
  exact Rat.le_trans (Rat.le_of_lt hstep) (Rat.le_trans hle₁ hle₂)

theorem compare_then_isLE_lt {e₁ e₂ : Int} {m₁ m₂ : Nat}
    (h : compare e₁ e₂ = .lt) :
    ((compare e₁ e₂).then (compare m₁ m₂)).isLE = true := by
  simp [h, Ordering.then]

theorem signedVal_le_of_pos {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂)
    (hle : ((compare e₁ e₂).then (compare m₁ m₂)).isLE = true) :
    signedVal .positive m₁ e₁ ≤ signedVal .positive m₂ e₂ := by
  simp only [signedVal]
  cases hc : compare e₁ e₂ with
  | lt =>
    exact mag_le_of_exp_lt hc₁ hc₂ (Int.compare_eq_lt.mp hc)
  | eq =>
    have he : e₁ = e₂ := Int.compare_eq_eq.mp hc
    subst he
    simp only [Ordering.then] at hle
    have hm : m₁ ≤ m₂ := by
      have hne : compare m₁ m₂ ≠ .gt := by
        intro hgt; simp [hgt, Ordering.isLE] at hle
      exact Nat.compare_ne_gt.mp hne
    exact mag_le_mag hm
  | gt =>
    simp [hc, Ordering.then, Ordering.isLE] at hle

theorem signedVal_le_of_neg {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂)
    (hge : ((compare e₁ e₂).then (compare m₁ m₂)).isGE = true) :
    signedVal .negative m₁ e₁ ≤ signedVal .negative m₂ e₂ := by
  simp only [signedVal]
  cases hc : compare e₁ e₂ with
  | gt =>
    have hlt : e₂ < e₁ := Int.compare_eq_gt.mp hc
    have : mag m₂ e₂ ≤ mag m₁ e₁ := mag_le_of_exp_lt hc₂ hc₁ hlt
    exact Rat.neg_le_neg this
  | eq =>
    have he : e₁ = e₂ := Int.compare_eq_eq.mp hc
    subst he
    simp only [Ordering.then] at hge
    have hm : m₂ ≤ m₁ := by
      have hne : compare m₁ m₂ ≠ .lt := by
        intro hlt; simp [hlt, Ordering.isGE] at hge
      exact Nat.compare_ne_lt.mp hne
    exact Rat.neg_le_neg (mag_le_mag hm)
  | lt =>
    simp [hc, Ordering.then, Ordering.isGE] at hge

theorem signedVal_neg_lt_zero {m : Nat} {e : Int} (h : 0 < m) :
    signedVal .negative m e < 0 := by
  simp only [signedVal]
  have : -mag m e < -(0 : Rat) := Rat.neg_lt_neg (mag_pos h)
  rwa [Rat.neg_zero] at this

theorem zero_le_signedVal_pos {m : Nat} {e : Int} :
    (0 : Rat) ≤ signedVal .positive m e :=
  signedVal_nonneg_iff m e

/-- If two floats have rational values and `a ≤ b`, those values compare. -/
theorem float_le_rat {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (hle : a ≤ b) : qa ≤ qb := by
  have hle' : (unpackBits a.toBits).le (unpackBits b.toBits) = true := hle
  simp only [UnpackedFloat.le] at hle'
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨sa, hua, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨sb, hub, rfl⟩
      exact Rat.le_refl
    · rcases hfb with ⟨sb, mb, eb, hb0, hub, rfl, _⟩
      cases sb with
      | positive => exact zero_le_signedVal_pos
      | negative =>
        simp [hua, hub, UnpackedFloat.compare, Option.any] at hle'
  · rcases hfa with ⟨sa, ma, ea, ha0, hua, rfl, hca⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨sb, hub, rfl⟩
      cases sa with
      | negative =>
        exact Rat.le_of_lt (signedVal_neg_lt_zero ha0)
      | positive =>
        simp [hua, hub, UnpackedFloat.compare, Option.any] at hle'
    · rcases hfb with ⟨sb, mb, eb, hb0, hub, rfl, hcb⟩
      cases sa <;> cases sb
      · -- both negative
        simp [hua, hub, UnpackedFloat.compare, Option.any] at hle'
        exact signedVal_le_of_neg hca hcb hle'
      · -- neg ≤ pos
        exact Rat.le_trans (Rat.le_of_lt (signedVal_neg_lt_zero ha0))
          zero_le_signedVal_pos
      · -- pos ≤ neg: impossible
        simp [hua, hub, UnpackedFloat.compare, Option.any] at hle'
      · -- both positive
        simp [hua, hub, UnpackedFloat.compare, Option.any] at hle'
        exact signedVal_le_of_pos hca hcb hle'

/-! ### Membership in a Lean `Interval64` -/

def MemIv (x : Rat) (I : Interval64) : Prop :=
  Mem x I.lo.toBits I.hi.toBits

theorem bitsToEVal_some_of_loEncloses {b : UInt64} {x : Rat}
    (h : loEncloses? (bitsToEVal b) x) : ∃ ev, bitsToEVal b = some ev := by
  cases hb : bitsToEVal b with
  | none => simp [loEncloses?, hb] at h
  | some ev => exact ⟨ev, rfl⟩

theorem bitsToEVal_some_of_hiEncloses {b : UInt64} {x : Rat}
    (h : hiEncloses? (bitsToEVal b) x) : ∃ ev, bitsToEVal b = some ev := by
  cases hb : bitsToEVal b with
  | none => simp [hiEncloses?, hb] at h
  | some ev => exact ⟨ev, rfl⟩

theorem unpackBits_eq_posInf {b : UInt64} (h : bitsToEVal b = some .posInf) :
    unpackBits b = .infinity .positive := by
  rw [bitsToEVal] at h
  cases hu : unpackBits b with
  | notANumber =>
    rw [hu] at h; simp [toEVal] at h
  | infinity s =>
    cases s with
    | positive => rfl
    | negative => rw [hu] at h; simp [toEVal] at h
  | zero s =>
    rw [hu] at h; simp [toEVal] at h
  | finite s m e hm =>
    rw [hu] at h; simp [toEVal] at h

theorem unpackBits_eq_negInf {b : UInt64} (h : bitsToEVal b = some .negInf) :
    unpackBits b = .infinity .negative := by
  rw [bitsToEVal] at h
  cases hu : unpackBits b with
  | notANumber =>
    rw [hu] at h; simp [toEVal] at h
  | infinity s =>
    cases s with
    | positive => rw [hu] at h; simp [toEVal] at h
    | negative => rfl
  | zero s =>
    rw [hu] at h; simp [toEVal] at h
  | finite s m e hm =>
    rw [hu] at h; simp [toEVal] at h

theorem bitsToRat?_of_ratEVal {b : UInt64} {q : Rat}
    (h : bitsToEVal b = some (.rat q)) : bitsToRat? b = some q := by
  rw [bitsToRat?_eq_bitsToEVal, h]

theorem not_posInf_of_le_rat {a b : Float} {q : Rat}
    (hle : a ≤ b) (hb : bitsToRat? b.toBits = some q) :
    bitsToEVal a.toBits ≠ some .posInf := by
  intro ha
  have hua : unpackBits a.toBits = .infinity .positive := unpackBits_eq_posInf ha
  have hle' : (unpackBits a.toBits).le (unpackBits b.toBits) = true := hle
  rw [hua] at hle'
  rcases bitsToRat?_cases hb with hzb | hfb
  · rcases hzb with ⟨sb, hub, _⟩
    simp [hub, UnpackedFloat.le, UnpackedFloat.compare, Option.any] at hle'
  · rcases hfb with ⟨sb, mb, eb, hb0, hub, _, _⟩
    simp [hub, UnpackedFloat.le, UnpackedFloat.compare, Option.any] at hle'

/-- Turn a compiled `I.hi ≤ c` check into a rational bound on every
    member of `I`. The only numeric information is `hle` (typically
    obtained by `native_decide`) together with the rational value of `c`. -/
theorem hi_le_of_native {x : Rat} {I : Interval64} {c : Float} {q : Rat}
    (hx : MemIv x I) (hle : I.hi ≤ c)
    (hc : bitsToRat? c.toBits = some q) : x ≤ q := by
  have hhi : hiEncloses? (bitsToEVal I.hi.toBits) x := hx.2
  rcases bitsToEVal_some_of_hiEncloses hhi with ⟨ev, hev⟩
  have hnotInf : ev ≠ .posInf := by
    intro heq
    exact not_posInf_of_le_rat hle hc (heq ▸ hev)
  have hqI : ∃ r, bitsToEVal I.hi.toBits = some (.rat r) := by
    cases ev with
    | posInf => exact (hnotInf rfl).elim
    | negInf =>
      simp [hiEncloses?, hiEncloses, hev] at hhi
    | rat r => exact ⟨r, hev⟩
  rcases hqI with ⟨r, hr⟩
  have hxle : x ≤ r := by
    simp [hiEncloses?, hiEncloses, hr] at hhi
    exact hhi
  have hr' : bitsToRat? I.hi.toBits = some r := bitsToRat?_of_ratEVal hr
  exact Rat.le_trans hxle (float_le_rat hr' hc hle)

theorem not_isNaN_of_MemIv_lo {x : Rat} {I : Interval64} (hx : MemIv x I) :
    I.lo.isNaN = false := by
  rcases bitsToEVal_some_of_loEncloses hx.1 with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem not_isNaN_of_MemIv_hi {x : Rat} {I : Interval64} (hx : MemIv x I) :
    I.hi.isNaN = false := by
  rcases bitsToEVal_some_of_hiEncloses hx.2 with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem anyNan_eq_false {x y : Rat} {X Y : Interval64}
    (hx : MemIv x X) (hy : MemIv y Y) : anyNan X Y = false := by
  simp only [anyNan, Bool.or_eq_false_iff]
  exact ⟨⟨⟨not_isNaN_of_MemIv_lo hx, not_isNaN_of_MemIv_hi hx⟩,
          not_isNaN_of_MemIv_lo hy⟩, not_isNaN_of_MemIv_hi hy⟩

end Interval64Proofs.FloatBits
