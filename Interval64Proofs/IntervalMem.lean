/-
`Interval64` addition and multiplication respect `MemIv`.

`add_mem_iv` allows infinite endpoints: a `MemIv` lower bound is never `+∞`
and an upper bound is never `-∞`, so directed add cannot produce NaN.
`mul_mem_iv` uses the four-corner min/max implemented by `Interval64.mul`
(finite endpoints).
-/
import Interval64Proofs.FloatBits
import Interval64Proofs.Mul

namespace Interval64Proofs.IntervalMem

open Interval64
open Interval64.Spec
open Interval64.Directed
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.Mul
open Interval64Proofs.FloatBits
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Directed add of possibly infinite `Mem` endpoints -/

theorem loEncloses_not_posInf {b : UInt64} {x : Rat}
    (h : loEncloses? (bitsToEVal b) x) :
    unpackBits b ≠ .notANumber ∧ unpackBits b ≠ .infinity .positive := by
  constructor
  · intro hu
    have : bitsToEVal b = none := by simp [bitsToEVal, hu]
    simp [loEncloses?, this] at h
  · intro hu
    have : bitsToEVal b = some .posInf := by simp [bitsToEVal, hu]
    simp [loEncloses?, loEncloses, this] at h

theorem hiEncloses_not_negInf {b : UInt64} {x : Rat}
    (h : hiEncloses? (bitsToEVal b) x) :
    unpackBits b ≠ .notANumber ∧ unpackBits b ≠ .infinity .negative := by
  constructor
  · intro hu
    have : bitsToEVal b = none := by simp [bitsToEVal, hu]
    simp [hiEncloses?, this] at h
  · intro hu
    have : bitsToEVal b = some .negInf := by simp [bitsToEVal, hu]
    simp [hiEncloses?, hiEncloses, this] at h

theorem addU_negInf_left (y : UnpackedFloat) (up : Bool)
    (h : y ≠ .notANumber ∧ y ≠ .infinity .positive) :
    addU (.infinity .negative) y up = .infinity .negative := by
  cases y with
  | notANumber => exact (h.1 rfl).elim
  | infinity s =>
    cases s with
    | positive => exact (h.2 rfl).elim
    | negative => simp [addU]
  | zero s => simp [addU]
  | finite s m e hm => simp [addU]

theorem addU_negInf_right (x : UnpackedFloat) (up : Bool)
    (h : x ≠ .notANumber ∧ x ≠ .infinity .positive) :
    addU x (.infinity .negative) up = .infinity .negative := by
  cases x with
  | notANumber => exact (h.1 rfl).elim
  | infinity s =>
    cases s with
    | positive => exact (h.2 rfl).elim
    | negative => simp [addU]
  | zero s => simp [addU]
  | finite s m e hm => simp [addU]

theorem addU_posInf_left (y : UnpackedFloat) (up : Bool)
    (h : y ≠ .notANumber ∧ y ≠ .infinity .negative) :
    addU (.infinity .positive) y up = .infinity .positive := by
  cases y with
  | notANumber => exact (h.1 rfl).elim
  | infinity s =>
    cases s with
    | negative => exact (h.2 rfl).elim
    | positive => simp [addU]
  | zero s => simp [addU]
  | finite s m e hm => simp [addU]

theorem addU_posInf_right (x : UnpackedFloat) (up : Bool)
    (h : x ≠ .notANumber ∧ x ≠ .infinity .negative) :
    addU x (.infinity .positive) up = .infinity .positive := by
  cases x with
  | notANumber => exact (h.1 rfl).elim
  | infinity s =>
    cases s with
    | negative => exact (h.2 rfl).elim
    | positive => simp [addU]
  | zero s => simp [addU]
  | finite s m e hm => simp [addU]

theorem bitsToEVal_packDirected_negInf (up : Bool) :
    bitsToEVal (packDirected up (.infinity .negative)) = some .negInf := by
  rw [packDirected_inf, bitsToEVal_pack_inf]

theorem bitsToEVal_packDirected_posInf (up : Bool) :
    bitsToEVal (packDirected up (.infinity .positive)) = some .posInf := by
  rw [packDirected_inf, bitsToEVal_pack_inf]

theorem addDown_loEncloses {x y : Rat} {loX loY : UInt64}
    (hx : loEncloses? (bitsToEVal loX) x)
    (hy : loEncloses? (bitsToEVal loY) y) :
    loEncloses? (bitsToEVal (Spec.addDown loX loY)) (x + y) := by
  rcases bitsToEVal_some_of_loEncloses hx with ⟨evx, hxev⟩
  rcases bitsToEVal_some_of_loEncloses hy with ⟨evy, hyev⟩
  have hxok := loEncloses_not_posInf hx
  have hyok := loEncloses_not_posInf hy
  cases evx with
  | posInf =>
    simp [loEncloses?, loEncloses, hxev] at hx
  | negInf =>
    have hux : unpackBits loX = .infinity .negative := unpackBits_eq_negInf hxev
    have hu :
        addU (unpackBits loX) (unpackBits loY) false = .infinity .negative := by
      rw [hux]
      exact addU_negInf_left _ _ hyok
    simp only [Spec.addDown, Spec.add, hu]
    rw [bitsToEVal_packDirected_negInf]
    simp [loEncloses?, loEncloses]
  | rat qx =>
    cases evy with
    | posInf =>
      simp [loEncloses?, loEncloses, hyev] at hy
    | negInf =>
      have huy : unpackBits loY = .infinity .negative := unpackBits_eq_negInf hyev
      have hu :
          addU (unpackBits loX) (unpackBits loY) false = .infinity .negative := by
        rw [huy]
        exact addU_negInf_right _ _ hxok
      simp only [Spec.addDown, Spec.add, hu]
      rw [bitsToEVal_packDirected_negInf]
      simp [loEncloses?, loEncloses]
    | rat qy =>
      have hqx : bitsToRat? loX = some qx := bitsToRat?_of_ratEVal hxev
      have hqy : bitsToRat? loY = some qy := bitsToRat?_of_ratEVal hyev
      have hsum := add_encloses_lo hqx hqy
      have hlex : qx ≤ x := by
        simp [loEncloses?, loEncloses, hxev] at hx
        exact hx
      have hley : qy ≤ y := by
        simp [loEncloses?, loEncloses, hyev] at hy
        exact hy
      have hle : qx + qy ≤ x + y :=
        Rat.le_trans ((Rat.add_le_add_right (a := qx) (b := x) (c := qy)).mpr hlex)
          ((Rat.add_le_add_left (a := qy) (b := y) (c := x)).mpr hley)
      exact loEncloses_trans hsum hle

theorem addUp_hiEncloses {x y : Rat} {hiX hiY : UInt64}
    (hx : hiEncloses? (bitsToEVal hiX) x)
    (hy : hiEncloses? (bitsToEVal hiY) y) :
    hiEncloses? (bitsToEVal (Spec.addUp hiX hiY)) (x + y) := by
  rcases bitsToEVal_some_of_hiEncloses hx with ⟨evx, hxev⟩
  rcases bitsToEVal_some_of_hiEncloses hy with ⟨evy, hyev⟩
  have hxok := hiEncloses_not_negInf hx
  have hyok := hiEncloses_not_negInf hy
  cases evx with
  | negInf =>
    simp [hiEncloses?, hiEncloses, hxev] at hx
  | posInf =>
    have hux : unpackBits hiX = .infinity .positive := unpackBits_eq_posInf hxev
    have hu :
        addU (unpackBits hiX) (unpackBits hiY) true = .infinity .positive := by
      rw [hux]
      exact addU_posInf_left _ _ hyok
    simp only [Spec.addUp, Spec.add, hu]
    rw [bitsToEVal_packDirected_posInf]
    simp [hiEncloses?, hiEncloses]
  | rat qx =>
    cases evy with
    | negInf =>
      simp [hiEncloses?, hiEncloses, hyev] at hy
    | posInf =>
      have huy : unpackBits hiY = .infinity .positive := unpackBits_eq_posInf hyev
      have hu :
          addU (unpackBits hiX) (unpackBits hiY) true = .infinity .positive := by
        rw [huy]
        exact addU_posInf_right _ _ hxok
      simp only [Spec.addUp, Spec.add, hu]
      rw [bitsToEVal_packDirected_posInf]
      simp [hiEncloses?, hiEncloses]
    | rat qy =>
      have hqx : bitsToRat? hiX = some qx := bitsToRat?_of_ratEVal hxev
      have hqy : bitsToRat? hiY = some qy := bitsToRat?_of_ratEVal hyev
      have hsum := add_encloses_hi hqx hqy
      have hgex : x ≤ qx := by
        simp [hiEncloses?, hiEncloses, hxev] at hx
        exact hx
      have hgey : y ≤ qy := by
        simp [hiEncloses?, hiEncloses, hyev] at hy
        exact hy
      have hge : x + y ≤ qx + qy :=
        Rat.le_trans ((Rat.add_le_add_right (a := x) (b := qx) (c := y)).mpr hgex)
          ((Rat.add_le_add_left (a := y) (b := qy) (c := qx)).mpr hgey)
      exact hiEncloses_trans hsum hge

theorem add_eq_directed {X Y : Interval64} (h : anyNan X Y = false) :
    X + Y = ⟨Directed.addDown X.lo Y.lo, Directed.addUp X.hi Y.hi⟩ := by
  change Interval64.add X Y = _
  unfold Interval64.add
  rw [h]
  rfl

theorem add_mem_iv {x y : Rat} {X Y : Interval64}
    (hx : MemIv x X) (hy : MemIv y Y) : MemIv (x + y) (X + Y) := by
  have hnan : anyNan X Y = false := anyNan_eq_false hx hy
  have hadd := add_eq_directed hnan
  have hlo := addDown_loEncloses hx.1 hy.1
  have hhi := addUp_hiEncloses hx.2 hy.2
  rw [hadd]
  constructor
  · rw [addDown_toBits]
    rcases bitsToEVal_some_of_loEncloses hlo with ⟨evl, hel⟩
    rw [bitsToEVal_pack_unpack_of_some hel, ← hel]
    exact hlo
  · rw [addUp_toBits]
    rcases bitsToEVal_some_of_hiEncloses hhi with ⟨evh, heh⟩
    rw [bitsToEVal_pack_unpack_of_some heh, ← heh]
    exact hhi


/-! ### Four-corner multiplication of finite-endpoint intervals -/

theorem float_isInf (f : Float) :
    f.isInf = (unpackBits f.toBits).isInf :=
  rfl

theorem float_lt_iff (a b : Float) :
    a < b ↔ (unpackBits a.toBits).lt (unpackBits b.toBits) = true :=
  Iff.rfl

theorem float_le_of_lt {a b : Float} (h : a < b) : a ≤ b := by
  have hlt : (unpackBits a.toBits).compare (unpackBits b.toBits) = some .lt := by
    have : (unpackBits a.toBits).lt (unpackBits b.toBits) = true :=
      (float_lt_iff a b).mp h
    simpa [UnpackedFloat.lt, beq_iff_eq] using this
  have hle : (unpackBits a.toBits).le (unpackBits b.toBits) = true := by
    simp [UnpackedFloat.le, hlt, Option.any, Ordering.isLE]
  exact (float_le_iff a b).mpr hle

theorem not_isInf_of_bitsToRat? {f : Float} {q : Rat}
    (h : bitsToRat? f.toBits = some q) : f.isInf = false := by
  rw [float_isInf]
  rcases bitsToRat?_cases h with hz | hf
  · rcases hz with ⟨s, hu, _⟩
    simp [hu, UnpackedFloat.isInf]
  · rcases hf with ⟨s, m, e, hm, hu, _, _⟩
    simp [hu, UnpackedFloat.isInf]

theorem loEncloses_mulDown {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    loEncloses? (bitsToEVal (Directed.mulDown a b).toBits) (qa * qb) := by
  have h := mul_encloses_lo ha hb
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  rw [mulDown_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

theorem hiEncloses_mulUp {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    hiEncloses? (bitsToEVal (Directed.mulUp a b).toBits) (qa * qb) := by
  have h := mul_encloses_hi ha hb
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  rw [mulUp_toBits, bitsToEVal_pack_unpack_of_some hev, ← hev]
  exact h

theorem mulDown_not_nan' {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    (Directed.mulDown a b).isNaN = false := by
  rcases bitsToEVal_some_of_loEncloses (loEncloses_mulDown ha hb) with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem mulUp_not_nan' {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    (Directed.mulUp a b).isNaN = false := by
  rcases bitsToEVal_some_of_hiEncloses (hiEncloses_mulUp ha hb) with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem accCorner_of_finite (x y lo hi : Float) (got : Bool)
    {qx qy : Rat}
    (hx : bitsToRat? x.toBits = some qx)
    (hy : bitsToRat? y.toBits = some qy) :
    accCorner x y lo hi got =
      let d := Directed.mulDown x y
      let u := Directed.mulUp x y
      if !got then (d, u, true)
      else (fmin d lo, fmax u hi, true) := by
  have hskip :
      ((x == 0 && y.isInf) || (y == 0 && x.isInf)) = false := by
    simp [not_isInf_of_bitsToRat? hx, not_isInf_of_bitsToRat? hy]
  have hd : (Directed.mulDown x y).isNaN = false := mulDown_not_nan' hx hy
  have hu : (Directed.mulUp x y).isNaN = false := mulUp_not_nan' hx hy
  unfold accCorner
  simp [hskip, hd, hu, fmin, fmax]

theorem eq_negInf_of_loEncloses_not_rat {f : Float} {z : Rat}
    (h : loEncloses? (bitsToEVal f.toBits) z)
    (hn : bitsToRat? f.toBits = none) :
    bitsToEVal f.toBits = some .negInf := by
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  have := bitsToRat?_eq_bitsToEVal f.toBits
  simp [hn, hev] at this
  cases ev with
  | posInf =>
    simp [loEncloses?, loEncloses, hev] at h
  | negInf => exact hev
  | rat q =>
    simp at this

theorem eq_posInf_of_hiEncloses_not_rat {f : Float} {z : Rat}
    (h : hiEncloses? (bitsToEVal f.toBits) z)
    (hn : bitsToRat? f.toBits = none) :
    bitsToEVal f.toBits = some .posInf := by
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  have := bitsToRat?_eq_bitsToEVal f.toBits
  simp [hn, hev] at this
  cases ev with
  | negInf =>
    simp [hiEncloses?, hiEncloses, hev] at h
  | posInf => exact hev
  | rat q =>
    simp at this

theorem mul_le_mul_of_nonpos_right {a b c : Rat} (ha : a ≤ b) (hc : c ≤ 0) :
    b * c ≤ a * c := by
  have hnc : (0 : Rat) ≤ -c := by
    have := Rat.neg_le_neg hc
    rwa [Rat.neg_zero] at this
  have h := Rat.mul_le_mul_of_nonneg_right ha hnc
  have : -(a * c) ≤ -(b * c) := by
    rwa [← Rat.mul_neg, ← Rat.mul_neg]
  exact Rat.neg_le_neg_iff.mp this


theorem compare_then_swap (e1 e2 : Int) (m1 m2 : Nat) :
    (compare e2 e1).then (compare m2 m1) =
      ((compare e1 e2).then (compare m1 m2)).swap := by
  rw [← Int.compare_swap e1 e2, ← Nat.compare_swap m1 m2]
  cases compare e1 e2 <;> cases compare m1 m2 <;> rfl

theorem le_of_not_lt_of_rats {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (h : ¬ a < b) : b ≤ a := by
  have hlt : (unpackBits a.toBits).lt (unpackBits b.toBits) = false := by
    simpa [float_lt_iff] using h
  have hle : (unpackBits b.toBits).le (unpackBits a.toBits) = true := by
    rcases bitsToRat?_cases ha with hza | hfa
    · rcases hza with ⟨sa, hua, _⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨sb, hub, _⟩
        simp [UnpackedFloat.le, hua, hub, UnpackedFloat.compare, Option.any]
      · rcases hfb with ⟨sb, mb, eb, _, hub, _, _⟩
        cases sb with
        | positive =>
          simp [UnpackedFloat.lt, hua, hub, UnpackedFloat.compare] at hlt
        | negative =>
          simp [UnpackedFloat.le, hua, hub, UnpackedFloat.compare, Option.any]
    · rcases hfa with ⟨sa, ma, ea, _, hua, _, _⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨sb, hub, _⟩
        cases sa with
        | negative =>
          simp [UnpackedFloat.lt, hua, hub, UnpackedFloat.compare] at hlt
        | positive =>
          simp [UnpackedFloat.le, hua, hub, UnpackedFloat.compare, Option.any]
      · rcases hfb with ⟨sb, mb, eb, _, hub, _, _⟩
        cases sa <;> cases sb
        · simp [UnpackedFloat.le, UnpackedFloat.lt, hua, hub, UnpackedFloat.compare,
            Option.any, beq_iff_eq] at hlt ⊢
          rw [compare_then_swap ea eb ma mb]
          cases hc : (compare ea eb).then (compare ma mb) <;>
            simp [hc, Ordering.swap, Ordering.isLE, Ordering.isGE] at hlt ⊢
        · simp [UnpackedFloat.lt, hua, hub, UnpackedFloat.compare] at hlt
        · simp [UnpackedFloat.le, hua, hub, UnpackedFloat.compare, Option.any]
        · simp [UnpackedFloat.le, UnpackedFloat.lt, hua, hub, UnpackedFloat.compare,
            Option.any, beq_iff_eq] at hlt ⊢
          rw [compare_then_swap ea eb ma mb]
          cases hc : (compare ea eb).then (compare ma mb) <;>
            simp [hc, Ordering.swap, Ordering.isLE, Ordering.isGE] at hlt ⊢
  exact (float_le_iff b a).mpr hle

theorem bitsToRat?_fmin {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    ∃ q, bitsToRat? (fmin a b).toBits = some q ∧ q ≤ qa ∧ q ≤ qb := by
  simp only [fmin]
  cases hdec : decide (a < b) with
  | true =>
    have hlt : a < b := of_decide_eq_true hdec
    refine ⟨qa, ?_, Rat.le_refl, float_le_rat ha hb (float_le_of_lt hlt)⟩
    simpa [hdec] using ha
  | false =>
    have hle : b ≤ a :=
      le_of_not_lt_of_rats ha hb (of_decide_eq_false hdec)
    refine ⟨qb, ?_, float_le_rat hb ha hle, Rat.le_refl⟩
    simpa [hdec] using hb

theorem bitsToRat?_fmax {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) :
    ∃ q, bitsToRat? (fmax a b).toBits = some q ∧ qa ≤ q ∧ qb ≤ q := by
  simp only [fmax]
  cases hdec : decide (a > b) with
  | true =>
    have hlt : b < a := of_decide_eq_true hdec
    refine ⟨qa, ?_, Rat.le_refl, float_le_rat hb ha (float_le_of_lt hlt)⟩
    simpa [hdec] using ha
  | false =>
    have hle : a ≤ b :=
      le_of_not_lt_of_rats hb ha (by
        intro hlt; exact (of_decide_eq_false hdec) hlt)
    refine ⟨qb, ?_, float_le_rat ha hb hle, Rat.le_refl⟩
    simpa [hdec] using hb

theorem fmin_negInf {a b : Float}
    (h : bitsToEVal a.toBits = some .negInf ∨ bitsToEVal b.toBits = some .negInf)
    (ha : bitsToEVal a.toBits ≠ none) (hb : bitsToEVal b.toBits ≠ none) :
    bitsToEVal (fmin a b).toBits = some .negInf := by
  simp only [fmin]
  cases hdec : decide (a < b) with
  | true =>
    cases h with
    | inl haI =>
      simp [hdec]; exact haI
    | inr hbI =>
      have hlt : a < b := of_decide_eq_true hdec
      have hub : unpackBits b.toBits = .infinity .negative := unpackBits_eq_negInf hbI
      have hlt' : (unpackBits a.toBits).lt (unpackBits b.toBits) = true :=
        (float_lt_iff a b).mp hlt
      rw [hub] at hlt'
      simp only [UnpackedFloat.lt, beq_iff_eq] at hlt'
      cases hua : unpackBits a.toBits with
      | notANumber => simp [bitsToEVal, hua] at ha
      | infinity s =>
        cases s with
        | positive => simp [hua, UnpackedFloat.compare] at hlt'
        | negative => simp [hdec, bitsToEVal, hua]
      | zero s => simp [hua, UnpackedFloat.compare] at hlt'
      | finite s m e hm => simp [hua, UnpackedFloat.compare] at hlt'
  | false =>
    cases h with
    | inr hbI =>
      simp [hdec]; exact hbI
    | inl haI =>
      have hlt : ¬ a < b := of_decide_eq_false hdec
      have hua : unpackBits a.toBits = .infinity .negative := unpackBits_eq_negInf haI
      have hlt' : (unpackBits a.toBits).lt (unpackBits b.toBits) = false := by
        simpa [float_lt_iff] using hlt
      rw [hua] at hlt'
      cases hub : unpackBits b.toBits with
      | notANumber => simp [bitsToEVal, hub] at hb
      | infinity s =>
        cases s with
        | positive =>
          have hs : compare Sign.negative Sign.positive = .lt := rfl
          simp [UnpackedFloat.lt, hub, UnpackedFloat.compare, hs] at hlt'
        | negative => simp [hdec, bitsToEVal, hub]
      | zero s => simp [UnpackedFloat.lt, hub, UnpackedFloat.compare] at hlt'
      | finite s m e hm => simp [UnpackedFloat.lt, hub, UnpackedFloat.compare] at hlt'

theorem fmax_posInf {a b : Float}
    (h : bitsToEVal a.toBits = some .posInf ∨ bitsToEVal b.toBits = some .posInf)
    (ha : bitsToEVal a.toBits ≠ none) (hb : bitsToEVal b.toBits ≠ none) :
    bitsToEVal (fmax a b).toBits = some .posInf := by
  simp only [fmax]
  cases hdec : decide (a > b) with
  | true =>
    cases h with
    | inl haI =>
      simp [hdec]; exact haI
    | inr hbI =>
      have hlt : b < a := of_decide_eq_true hdec
      have hub : unpackBits b.toBits = .infinity .positive := unpackBits_eq_posInf hbI
      have hlt' : (unpackBits b.toBits).lt (unpackBits a.toBits) = true :=
        (float_lt_iff b a).mp hlt
      rw [hub] at hlt'
      simp only [UnpackedFloat.lt, beq_iff_eq] at hlt'
      cases hua : unpackBits a.toBits with
      | notANumber => simp [bitsToEVal, hua] at ha
      | infinity s =>
        cases s with
        | negative => simp [hua, UnpackedFloat.compare] at hlt'
        | positive => simp [hdec, bitsToEVal, hua]
      | zero s => simp [hua, UnpackedFloat.compare] at hlt'
      | finite s m e hm => simp [hua, UnpackedFloat.compare] at hlt'
  | false =>
    cases h with
    | inr hbI =>
      simp [hdec]; exact hbI
    | inl haI =>
      have hgt : ¬ a > b := of_decide_eq_false hdec
      have hua : unpackBits a.toBits = .infinity .positive := unpackBits_eq_posInf haI
      have hlt' : (unpackBits b.toBits).lt (unpackBits a.toBits) = false := by
        simpa [float_lt_iff] using fun hlt : b < a => hgt hlt
      cases hub : unpackBits b.toBits with
      | notANumber => simp [bitsToEVal, hub] at hb
      | infinity s =>
        cases s with
        | negative =>
          rw [hub, hua] at hlt'
          have hs : compare Sign.negative Sign.positive = .lt := rfl
          simp [UnpackedFloat.lt, UnpackedFloat.compare, hs] at hlt'
        | positive => simp [hdec, bitsToEVal, hub]
      | zero s =>
        rw [hub, hua] at hlt'
        simp [UnpackedFloat.lt, UnpackedFloat.compare] at hlt'
      | finite s m e hm =>
        rw [hub, hua] at hlt'
        simp [UnpackedFloat.lt, UnpackedFloat.compare] at hlt'

def rmin (a b : Rat) : Rat := if a ≤ b then a else b
def rmax (a b : Rat) : Rat := if a ≤ b then b else a

theorem rmin_le_left (a b : Rat) : rmin a b ≤ a := by
  simp only [rmin]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]; exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rmin_le_right (a b : Rat) : rmin a b ≤ b := by
  simp only [rmin]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

theorem le_rmin {a b c : Rat} (ha : c ≤ a) (hb : c ≤ b) : c ≤ rmin a b := by
  simp only [rmin]
  by_cases h : a ≤ b
  · simp [h]; exact ha
  · simp [h]; exact hb

theorem rmin_le_rmin {a b c d : Rat} (hac : a ≤ c) (hbd : b ≤ d) :
    rmin a b ≤ rmin c d :=
  le_rmin (Rat.le_trans (rmin_le_left a b) hac) (Rat.le_trans (rmin_le_right a b) hbd)

theorem le_rmax_left (a b : Rat) : a ≤ rmax a b := by
  simp only [rmax]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

theorem le_rmax_right (a b : Rat) : b ≤ rmax a b := by
  simp only [rmax]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]; exact Rat.le_of_lt (Rat.not_le.mp h)

theorem rmax_le {a b c : Rat} (ha : a ≤ c) (hb : b ≤ c) : rmax a b ≤ c := by
  simp only [rmax]
  by_cases h : a ≤ b
  · simp [h]; exact hb
  · simp [h]; exact ha

theorem rmax_le_rmax {a b c d : Rat} (hac : a ≤ c) (hbd : b ≤ d) :
    rmax a b ≤ rmax c d :=
  rmax_le (Rat.le_trans hac (le_rmax_left c d)) (Rat.le_trans hbd (le_rmax_right c d))

theorem min_le_mul_of_bounds_right {a x b c : Rat}
    (hle : a ≤ x) (hge : x ≤ b) :
    rmin (a * c) (b * c) ≤ x * c := by
  cases (Rat.le_total : c ≤ 0 ∨ 0 ≤ c) with
  | inl hc =>
    have hbc : b * c ≤ x * c := mul_le_mul_of_nonpos_right hge hc
    exact Rat.le_trans (rmin_le_right (a * c) (b * c)) hbc
  | inr hc =>
    have hac : a * c ≤ x * c := Rat.mul_le_mul_of_nonneg_right hle hc
    exact Rat.le_trans (rmin_le_left (a * c) (b * c)) hac

theorem min_le_mul_of_bounds_left {c a x b : Rat}
    (hle : a ≤ x) (hge : x ≤ b) :
    rmin (c * a) (c * b) ≤ c * x := by
  have h := min_le_mul_of_bounds_right (c := c) hle hge
  simpa [Rat.mul_comm] using h

theorem mul_le_max_of_bounds_right {a x b c : Rat}
    (hle : a ≤ x) (hge : x ≤ b) :
    x * c ≤ rmax (a * c) (b * c) := by
  cases (Rat.le_total : c ≤ 0 ∨ 0 ≤ c) with
  | inl hc =>
    have hac : x * c ≤ a * c := mul_le_mul_of_nonpos_right hle hc
    exact Rat.le_trans hac (le_rmax_left (a * c) (b * c))
  | inr hc =>
    have hbc : x * c ≤ b * c := Rat.mul_le_mul_of_nonneg_right hge hc
    exact Rat.le_trans hbc (le_rmax_right (a * c) (b * c))

theorem mul_le_max_of_bounds_left {c a x b : Rat}
    (hle : a ≤ x) (hge : x ≤ b) :
    c * x ≤ rmax (c * a) (c * b) := by
  have h := mul_le_max_of_bounds_right (c := c) hle hge
  simpa [Rat.mul_comm] using h

theorem min_mul_le_of_interval {x y alo ahi blo bhi : Rat}
    (hxl : alo ≤ x) (hxh : x ≤ ahi) (hyl : blo ≤ y) (hyh : y ≤ bhi) :
    rmin (rmin (alo * blo) (alo * bhi)) (rmin (ahi * blo) (ahi * bhi)) ≤ x * y := by
  have h1 : rmin (alo * blo) (alo * bhi) ≤ alo * y :=
    min_le_mul_of_bounds_left (c := alo) hyl hyh
  have h2 : rmin (ahi * blo) (ahi * bhi) ≤ ahi * y :=
    min_le_mul_of_bounds_left (c := ahi) hyl hyh
  have h3 : rmin (alo * y) (ahi * y) ≤ x * y :=
    min_le_mul_of_bounds_right (c := y) hxl hxh
  exact Rat.le_trans (rmin_le_rmin h1 h2) h3

theorem max_mul_ge_of_interval {x y alo ahi blo bhi : Rat}
    (hxl : alo ≤ x) (hxh : x ≤ ahi) (hyl : blo ≤ y) (hyh : y ≤ bhi) :
    x * y ≤ rmax (rmax (alo * blo) (alo * bhi)) (rmax (ahi * blo) (ahi * bhi)) := by
  have h1 : alo * y ≤ rmax (alo * blo) (alo * bhi) :=
    mul_le_max_of_bounds_left (c := alo) hyl hyh
  have h2 : ahi * y ≤ rmax (ahi * blo) (ahi * bhi) :=
    mul_le_max_of_bounds_left (c := ahi) hyl hyh
  have h3 : x * y ≤ rmax (alo * y) (ahi * y) :=
    mul_le_max_of_bounds_right (c := y) hxl hxh
  exact Rat.le_trans h3 (rmax_le_rmax h1 h2)

theorem mulDown_rat_le {a b : Float} {qa qb q : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (hq : bitsToRat? (Directed.mulDown a b).toBits = some q) :
    q ≤ qa * qb := by
  have h := loEncloses_mulDown ha hb
  have hev := bitsToEVal_rat_of_bitsToRat? hq
  simp [loEncloses?, loEncloses, hev] at h
  exact h

theorem mulUp_rat_ge {a b : Float} {qa qb q : Rat}
    (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb)
    (hq : bitsToRat? (Directed.mulUp a b).toBits = some q) :
    qa * qb ≤ q := by
  have h := hiEncloses_mulUp ha hb
  have hev := bitsToEVal_rat_of_bitsToRat? hq
  simp [hiEncloses?, hiEncloses, hev] at h
  exact h

theorem ne_none_of_loEncloses {f : Float} {z : Rat}
    (h : loEncloses? (bitsToEVal f.toBits) z) :
    bitsToEVal f.toBits ≠ none :=
  (bitsToEVal_some_of_loEncloses h).elim (fun _ hev => by simp [hev])

theorem ne_none_of_hiEncloses {f : Float} {z : Rat}
    (h : hiEncloses? (bitsToEVal f.toBits) z) :
    bitsToEVal f.toBits ≠ none :=
  (bitsToEVal_some_of_hiEncloses h).elim (fun _ hev => by simp [hev])


theorem mul_eq_four_corners {X Y : Interval64}
    {alo ahi blo bhi : Rat}
    (hnan : anyNan X Y = false)
    (hAlo : bitsToRat? X.lo.toBits = some alo)
    (hAhi : bitsToRat? X.hi.toBits = some ahi)
    (hBlo : bitsToRat? Y.lo.toBits = some blo)
    (hBhi : bitsToRat? Y.hi.toBits = some bhi) :
    X * Y =
      ⟨fmin (Directed.mulDown X.hi Y.hi)
         (fmin (Directed.mulDown X.hi Y.lo)
           (fmin (Directed.mulDown X.lo Y.hi) (Directed.mulDown X.lo Y.lo))),
       fmax (Directed.mulUp X.hi Y.hi)
         (fmax (Directed.mulUp X.hi Y.lo)
           (fmax (Directed.mulUp X.lo Y.hi) (Directed.mulUp X.lo Y.lo)))⟩ := by
  have h0 := accCorner_of_finite X.lo Y.lo 0 0 false hAlo hBlo
  have h1 := accCorner_of_finite X.lo Y.hi
      (Directed.mulDown X.lo Y.lo) (Directed.mulUp X.lo Y.lo) true hAlo hBhi
  have h2 := accCorner_of_finite X.hi Y.lo
      (fmin (Directed.mulDown X.lo Y.hi) (Directed.mulDown X.lo Y.lo))
      (fmax (Directed.mulUp X.lo Y.hi) (Directed.mulUp X.lo Y.lo)) true hAhi hBlo
  have h3 := accCorner_of_finite X.hi Y.hi
      (fmin (Directed.mulDown X.hi Y.lo)
        (fmin (Directed.mulDown X.lo Y.hi) (Directed.mulDown X.lo Y.lo)))
      (fmax (Directed.mulUp X.hi Y.lo)
        (fmax (Directed.mulUp X.lo Y.hi) (Directed.mulUp X.lo Y.lo))) true hAhi hBhi
  change Interval64.mul X Y = _
  unfold Interval64.mul
  rw [hnan]
  simp [h0, h1, h2, h3]

/-- The four-corner rule implemented by `Interval64.mul`, for finite
    endpoints (including intervals that straddle zero). -/
theorem mul_mem_iv {x y : Rat} {X Y : Interval64}
    (hx : MemIv x X) (hy : MemIv y Y)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q)
    (hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    MemIv (x * y) (X * Y) := by
  rcases hXlo with ⟨alo, hAlo⟩
  rcases hXhi with ⟨ahi, hAhi⟩
  rcases hYlo with ⟨blo, hBlo⟩
  rcases hYhi with ⟨bhi, hBhi⟩
  have hnan : anyNan X Y = false := anyNan_eq_false hx hy
  have hmul := mul_eq_four_corners hnan hAlo hAhi hBlo hBhi
  let d00 := Directed.mulDown X.lo Y.lo
  let d01 := Directed.mulDown X.lo Y.hi
  let d10 := Directed.mulDown X.hi Y.lo
  let d11 := Directed.mulDown X.hi Y.hi
  let u00 := Directed.mulUp X.lo Y.lo
  let u01 := Directed.mulUp X.lo Y.hi
  let u10 := Directed.mulUp X.hi Y.lo
  let u11 := Directed.mulUp X.hi Y.hi
  have hlo00 := loEncloses_mulDown hAlo hBlo
  have hlo01 := loEncloses_mulDown hAlo hBhi
  have hlo10 := loEncloses_mulDown hAhi hBlo
  have hlo11 := loEncloses_mulDown hAhi hBhi
  have hhi00 := hiEncloses_mulUp hAlo hBlo
  have hhi01 := hiEncloses_mulUp hAlo hBhi
  have hhi10 := hiEncloses_mulUp hAhi hBlo
  have hhi11 := hiEncloses_mulUp hAhi hBhi
  have hxl : alo ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hAlo] at this
    exact this
  have hxh : x ≤ ahi := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hAhi] at this
    exact this
  have hyl : blo ≤ y := by
    have := hy.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hBlo] at this
    exact this
  have hyh : y ≤ bhi := by
    have := hy.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hBhi] at this
    exact this
  have hminprod := min_mul_le_of_interval hxl hxh hyl hyh
  have hmaxprod := max_mul_ge_of_interval hxl hxh hyl hyh
  have n00 := ne_none_of_loEncloses hlo00
  have n01 := ne_none_of_loEncloses hlo01
  have n10 := ne_none_of_loEncloses hlo10
  have n11 := ne_none_of_loEncloses hlo11
  have m00 := ne_none_of_hiEncloses hhi00
  have m01 := ne_none_of_hiEncloses hhi01
  have m10 := ne_none_of_hiEncloses hhi10
  have m11 := ne_none_of_hiEncloses hhi11
  rw [hmul]
  constructor
  · -- lo
    cases h00 : bitsToRat? d00.toBits with
    | none =>
      have hI := eq_negInf_of_loEncloses_not_rat hlo00 h00
      have hinner := fmin_negInf (Or.inr hI) n01 n00
      have hmid := fmin_negInf (Or.inr hinner) n10 (by simp [hinner])
      have hmin := fmin_negInf (Or.inr hmid) n11 (by simp [hmid])
      rw [hmin]; simp [loEncloses?, loEncloses]
    | some q00 =>
      cases h01 : bitsToRat? d01.toBits with
      | none =>
        have hI := eq_negInf_of_loEncloses_not_rat hlo01 h01
        have hinner := fmin_negInf (Or.inl hI) n01 n00
        have hmid := fmin_negInf (Or.inr hinner) n10 (by simp [hinner])
        have hmin := fmin_negInf (Or.inr hmid) n11 (by simp [hmid])
        rw [hmin]; simp [loEncloses?, loEncloses]
      | some q01 =>
        cases h10 : bitsToRat? d10.toBits with
        | none =>
          have hI := eq_negInf_of_loEncloses_not_rat hlo10 h10
          have hinnerq := bitsToRat?_fmin (a := d01) (b := d00) h01 h00
          have ninner : bitsToEVal (fmin d01 d00).toBits ≠ none := by
            rcases hinnerq with ⟨q, hq, _, _⟩
            simp [bitsToEVal_rat_of_bitsToRat? hq]
          have hmid := fmin_negInf (Or.inl hI) n10 ninner
          have hmin := fmin_negInf (Or.inr hmid) n11 (by simp [hmid])
          rw [hmin]; simp [loEncloses?, loEncloses]
        | some q10 =>
          cases h11 : bitsToRat? d11.toBits with
          | none =>
            have hI := eq_negInf_of_loEncloses_not_rat hlo11 h11
            rcases bitsToRat?_fmin (a := d01) (b := d00) h01 h00 with ⟨qi, hqi, _, _⟩
            rcases bitsToRat?_fmin (a := d10) (b := fmin d01 d00) h10 hqi with ⟨qm, hqm, _, _⟩
            have nmid : bitsToEVal (fmin d10 (fmin d01 d00)).toBits ≠ none := by
              simp [bitsToEVal_rat_of_bitsToRat? hqm]
            have hmin := fmin_negInf (Or.inl hI) n11 nmid
            rw [hmin]; simp [loEncloses?, loEncloses]
          | some q11 =>
            rcases bitsToRat?_fmin h01 h00 with ⟨qi, hqi, hqi01, hqi00⟩
            rcases bitsToRat?_fmin h10 hqi with ⟨qm, hqm, hqm10, hqmi⟩
            rcases bitsToRat?_fmin h11 hqm with ⟨ql, hql, hql11, hqlm⟩
            have hq00 : ql ≤ q00 := Rat.le_trans hqlm (Rat.le_trans hqmi hqi00)
            have hq01 : ql ≤ q01 := Rat.le_trans hqlm (Rat.le_trans hqmi hqi01)
            have hq10 : ql ≤ q10 := Rat.le_trans hqlm hqm10
            have hq11 : ql ≤ q11 := hql11
            have c00 := mulDown_rat_le hAlo hBlo h00
            have c01 := mulDown_rat_le hAlo hBhi h01
            have c10 := mulDown_rat_le hAhi hBlo h10
            have c11 := mulDown_rat_le hAhi hBhi h11
            have hlemin :
                ql ≤ rmin (rmin (alo * blo) (alo * bhi))
                  (rmin (ahi * blo) (ahi * bhi)) :=
              le_rmin (le_rmin (Rat.le_trans hq00 c00) (Rat.le_trans hq01 c01))
                (le_rmin (Rat.le_trans hq10 c10) (Rat.le_trans hq11 c11))
            have : ql ≤ x * y := Rat.le_trans hlemin hminprod
            rw [bitsToEVal_rat_of_bitsToRat? hql]
            simp [loEncloses?, loEncloses]
            exact this
  · -- hi
    cases h00 : bitsToRat? u00.toBits with
    | none =>
      have hI := eq_posInf_of_hiEncloses_not_rat hhi00 h00
      have hinner := fmax_posInf (Or.inr hI) m01 m00
      have hmid := fmax_posInf (Or.inr hinner) m10 (by simp [hinner])
      have hmax := fmax_posInf (Or.inr hmid) m11 (by simp [hmid])
      rw [hmax]; simp [hiEncloses?, hiEncloses]
    | some q00 =>
      cases h01 : bitsToRat? u01.toBits with
      | none =>
        have hI := eq_posInf_of_hiEncloses_not_rat hhi01 h01
        have hinner := fmax_posInf (Or.inl hI) m01 m00
        have hmid := fmax_posInf (Or.inr hinner) m10 (by simp [hinner])
        have hmax := fmax_posInf (Or.inr hmid) m11 (by simp [hmid])
        rw [hmax]; simp [hiEncloses?, hiEncloses]
      | some q01 =>
        cases h10 : bitsToRat? u10.toBits with
        | none =>
          have hI := eq_posInf_of_hiEncloses_not_rat hhi10 h10
          rcases bitsToRat?_fmax (a := u01) (b := u00) h01 h00 with ⟨q, hq, _, _⟩
          have ninner : bitsToEVal (fmax u01 u00).toBits ≠ none := by
            simp [bitsToEVal_rat_of_bitsToRat? hq]
          have hmid := fmax_posInf (Or.inl hI) m10 ninner
          have hmax := fmax_posInf (Or.inr hmid) m11 (by simp [hmid])
          rw [hmax]; simp [hiEncloses?, hiEncloses]
        | some q10 =>
          cases h11 : bitsToRat? u11.toBits with
          | none =>
            have hI := eq_posInf_of_hiEncloses_not_rat hhi11 h11
            rcases bitsToRat?_fmax (a := u01) (b := u00) h01 h00 with ⟨qi, hqi, _, _⟩
            rcases bitsToRat?_fmax (a := u10) (b := fmax u01 u00) h10 hqi with ⟨qm, hqm, _, _⟩
            have nmid : bitsToEVal (fmax u10 (fmax u01 u00)).toBits ≠ none := by
              simp [bitsToEVal_rat_of_bitsToRat? hqm]
            have hmax := fmax_posInf (Or.inl hI) m11 nmid
            rw [hmax]; simp [hiEncloses?, hiEncloses]
          | some q11 =>
            rcases bitsToRat?_fmax h01 h00 with ⟨qi, hqi, hq01i, hq00i⟩
            rcases bitsToRat?_fmax h10 hqi with ⟨qm, hqm, hq10m, hqim⟩
            rcases bitsToRat?_fmax h11 hqm with ⟨qh, hqh, hq11h, hqmh⟩
            have hq00 : q00 ≤ qh := Rat.le_trans hq00i (Rat.le_trans hqim hqmh)
            have hq01 : q01 ≤ qh := Rat.le_trans hq01i (Rat.le_trans hqim hqmh)
            have hq10 : q10 ≤ qh := Rat.le_trans hq10m hqmh
            have hq11 : q11 ≤ qh := hq11h
            have c00 := mulUp_rat_ge hAlo hBlo h00
            have c01 := mulUp_rat_ge hAlo hBhi h01
            have c10 := mulUp_rat_ge hAhi hBlo h10
            have c11 := mulUp_rat_ge hAhi hBhi h11
            have hgemax :
                rmax (rmax (alo * blo) (alo * bhi))
                  (rmax (ahi * blo) (ahi * bhi)) ≤ qh :=
              rmax_le (rmax_le (Rat.le_trans c00 hq00) (Rat.le_trans c01 hq01))
                (rmax_le (Rat.le_trans c10 hq10) (Rat.le_trans c11 hq11))
            have : x * y ≤ qh := Rat.le_trans hmaxprod hgemax
            rw [bitsToEVal_rat_of_bitsToRat? hqh]
            simp [hiEncloses?, hiEncloses]
            exact this


/-- A finite (non-Inf, non-NaN) lower endpoint of a member interval has a rational value. -/
theorem bitsToRat?_of_memIv_lo {x : Rat} {I : Interval64}
    (hx : MemIv x I) (hinf : I.lo.isInf = false) :
    ∃ q, bitsToRat? I.lo.toBits = some q := by
  rcases bitsToEVal_some_of_loEncloses hx.1 with ⟨ev, hev⟩
  cases ev with
  | rat q =>
    refine ⟨q, ?_⟩
    simpa [bitsToRat?_eq_bitsToEVal, hev]
  | negInf =>
    have hunp := unpackBits_eq_negInf hev
    have : I.lo.isInf = true := by
      rw [float_isInf, hunp]
      simp [UnpackedFloat.isInf]
    simp [this] at hinf
  | posInf =>
    have := hx.1
    simp [loEncloses?, loEncloses, hev] at this

theorem bitsToRat?_of_memIv_hi {x : Rat} {I : Interval64}
    (hx : MemIv x I) (hinf : I.hi.isInf = false) :
    ∃ q, bitsToRat? I.hi.toBits = some q := by
  rcases bitsToEVal_some_of_hiEncloses hx.2 with ⟨ev, hev⟩
  cases ev with
  | rat q =>
    refine ⟨q, ?_⟩
    simpa [bitsToRat?_eq_bitsToEVal, hev]
  | posInf =>
    have hunp := unpackBits_eq_posInf hev
    have : I.hi.isInf = true := by
      rw [float_isInf, hunp]
      simp [UnpackedFloat.isInf]
    simp [this] at hinf
  | negInf =>
    have := hx.2
    simp [hiEncloses?, hiEncloses, hev] at this

/-- `mul_mem_iv` with the finite-endpoint hypotheses phrased as `isInf = false`. -/
theorem mul_mem_iv_of_finite {x y : Rat} {X Y : Interval64}
    (hx : MemIv x X) (hy : MemIv y Y)
    (hXlo : X.lo.isInf = false) (hXhi : X.hi.isInf = false)
    (hYlo : Y.lo.isInf = false) (hYhi : Y.hi.isInf = false) :
    MemIv (x * y) (X * Y) :=
  mul_mem_iv hx hy
    (bitsToRat?_of_memIv_lo hx hXlo) (bitsToRat?_of_memIv_hi hx hXhi)
    (bitsToRat?_of_memIv_lo hy hYlo) (bitsToRat?_of_memIv_hi hy hYhi)

end Interval64Proofs.IntervalMem
