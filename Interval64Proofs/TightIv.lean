/-
Interval-level tightness for finite-endpoint `Interval64` add/sub/mul/div.

For `X = [l₁, h₁]`, `Y = [l₂, h₂]` with finite endpoints, the computed
lower endpoint of `X ∘ Y` is the *greatest representable lower bound* of
the rational range `{x ∘ y : x ∈ X, y ∈ Y}`, and the upper endpoint the
least representable upper bound. (Membership/enclosure is
`add_mem_iv` / `sub_mem_iv` / `mul_mem_iv` / `div_mem_iv`.)

For `div` this needs `containsZero Y = false`; when `Y ∋ 0` the result is
`whole` by policy, which is not tight.
-/
import Interval64Proofs.Tight

namespace Interval64Proofs.TightIv

open Interval64
open Interval64.Spec
open Interval64.Directed
open Interval64Proofs.Value
open Interval64Proofs.AddBits
open Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem
open Interval64Proofs.Sub
open Interval64Proofs.Div
open Interval64Proofs.Grid
open Interval64Proofs.OfRat
open Interval64Proofs.Tight

/-- `I = [l, h]` with finite endpoints and `l ≤ h`. -/
def FinIv (I : Interval64) (l h : Rat) : Prop :=
  bitsToRat? I.lo.toBits = some l ∧ bitsToRat? I.hi.toBits = some h ∧ l ≤ h

theorem memIv_iff {I : Interval64} {l h x : Rat} (hI : FinIv I l h) :
    MemIv x I ↔ l ≤ x ∧ x ≤ h := by
  unfold MemIv Mem
  rw [bitsToEVal_rat_of_bitsToRat? hI.1, bitsToEVal_rat_of_bitsToRat? hI.2.1]
  exact Iff.rfl

theorem memIv_lo {I : Interval64} {l h : Rat} (hI : FinIv I l h) : MemIv l I :=
  (memIv_iff hI).mpr ⟨Rat.le_refl, hI.2.2⟩

theorem memIv_hi {I : Interval64} {l h : Rat} (hI : FinIv I l h) : MemIv h I :=
  (memIv_iff hI).mpr ⟨hI.2.2, Rat.le_refl⟩

theorem anyNan_of_finIv {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) : anyNan X Y = false :=
  anyNan_eq_false (memIv_lo hX) (memIv_lo hY)

/-- Transfer a tight lower rounding through `Float.ofBits`. -/
theorem eval_pack_down {b : UInt64} {x : Rat} (h : IsRoundDown x (bitsToEVal b)) :
    bitsToEVal (packBits (unpackBits b)) = bitsToEVal b := by
  rcases eval_of_isRoundDown h with ⟨ev, hev⟩
  rw [hev]
  exact bitsToEVal_pack_unpack_of_some hev

theorem eval_pack_up {b : UInt64} {x : Rat} (h : IsRoundUp x (bitsToEVal b)) :
    bitsToEVal (packBits (unpackBits b)) = bitsToEVal b := by
  rcases eval_of_isRoundUp h with ⟨ev, hev⟩
  rw [hev]
  exact bitsToEVal_pack_unpack_of_some hev

/-! ### Float-level tight scalar operations -/

theorem addDown_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundDown (qa + qb) (bitsToEVal (Directed.addDown a b).toBits) := by
  rw [addDown_toBits, eval_pack_down (add_isRoundDown ha hb)]
  exact add_isRoundDown ha hb

theorem addUp_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundUp (qa + qb) (bitsToEVal (Directed.addUp a b).toBits) := by
  rw [addUp_toBits, eval_pack_up (add_isRoundUp ha hb)]
  exact add_isRoundUp ha hb

theorem subDown_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundDown (qa - qb) (bitsToEVal (Directed.subDown a b).toBits) := by
  rw [subDown_toBits, eval_pack_down (sub_isRoundDown ha hb)]
  exact sub_isRoundDown ha hb

theorem subUp_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundUp (qa - qb) (bitsToEVal (Directed.subUp a b).toBits) := by
  rw [subUp_toBits, eval_pack_up (sub_isRoundUp ha hb)]
  exact sub_isRoundUp ha hb

theorem mulDown_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundDown (qa * qb) (bitsToEVal (Directed.mulDown a b).toBits) := by
  rw [mulDown_toBits, eval_pack_down (mul_isRoundDown ha hb)]
  exact mul_isRoundDown ha hb

theorem mulUp_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) :
    IsRoundUp (qa * qb) (bitsToEVal (Directed.mulUp a b).toBits) := by
  rw [mulUp_toBits, eval_pack_up (mul_isRoundUp ha hb)]
  exact mul_isRoundUp ha hb

theorem divDown_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) (hqb : qb ≠ 0) :
    IsRoundDown (qa / qb) (bitsToEVal (Directed.divDown a b).toBits) := by
  rw [divDown_toBits, eval_pack_down (div_isRoundDown ha hb hqb)]
  exact div_isRoundDown ha hb hqb

theorem divUp_float_tight {a b : Float} {qa qb : Rat}
    (ha : bitsToRat? a.toBits = some qa) (hb : bitsToRat? b.toBits = some qb) (hqb : qb ≠ 0) :
    IsRoundUp (qa / qb) (bitsToEVal (Directed.divUp a b).toBits) := by
  rw [divUp_toBits, eval_pack_up (div_isRoundUp ha hb hqb)]
  exact div_isRoundUp ha hb hqb

/-! ### Interval add / sub -/

/-- `X + Y` endpoints are the tight roundings of `l₁ + l₂` and `h₁ + h₂`. -/
theorem add_iv_tight {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    IsRoundDown (l₁ + l₂) (bitsToEVal (X + Y).lo.toBits) ∧
      IsRoundUp (h₁ + h₂) (bitsToEVal (X + Y).hi.toBits) := by
  rw [add_eq_directed (anyNan_of_finIv hX hY)]
  exact ⟨addDown_float_tight hX.1 hY.1, addUp_float_tight hX.2.1 hY.2.1⟩

theorem sub_iv_tight {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    IsRoundDown (l₁ - h₂) (bitsToEVal (X - Y).lo.toBits) ∧
      IsRoundUp (h₁ - l₂) (bitsToEVal (X - Y).hi.toBits) := by
  rw [sub_eq_directed (anyNan_of_finIv hX hY)]
  exact ⟨subDown_float_tight hX.1 hY.2.1, subUp_float_tight hX.2.1 hY.1⟩

/-- **Interval add is optimal.** Any representable lower bound of
    `{x + y : x ∈ X, y ∈ Y}` is `≤ (X + Y).lo`; any representable upper
    bound is `≥ (X + Y).hi`. -/
theorem add_iv_optimal {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → f ≤ x + y) →
        hiEncloses? (bitsToEVal (X + Y).lo.toBits) f) ∧
      (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → x + y ≤ f) →
        loEncloses? (bitsToEVal (X + Y).hi.toBits) f) := by
  have ⟨hlo, hhi⟩ := add_iv_tight hX hY
  exact ⟨fun f hf hall => hlo.2 f hf (hall _ _ (memIv_lo hX) (memIv_lo hY)),
    fun f hf hall => hhi.2 f hf (hall _ _ (memIv_hi hX) (memIv_hi hY))⟩

theorem sub_iv_optimal {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → f ≤ x - y) →
        hiEncloses? (bitsToEVal (X - Y).lo.toBits) f) ∧
      (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → x - y ≤ f) →
        loEncloses? (bitsToEVal (X - Y).hi.toBits) f) := by
  have ⟨hlo, hhi⟩ := sub_iv_tight hX hY
  exact ⟨fun f hf hall => hlo.2 f hf (hall _ _ (memIv_lo hX) (memIv_hi hY)),
    fun f hf hall => hhi.2 f hf (hall _ _ (memIv_hi hX) (memIv_lo hY))⟩

/-! ### Interval mul / div: the endpoints are attained at a corner -/

theorem fmin_cases (a b : Float) : fmin a b = a ∨ fmin a b = b := by
  unfold fmin
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fmax_cases (a b : Float) : fmax a b = a ∨ fmax a b = b := by
  unfold fmax
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fmin_pres (P : Float → Prop) {a b : Float} (ha : P a) (hb : P b) : P (fmin a b) := by
  rcases fmin_cases a b with h | h <;> rw [h] <;> assumption

theorem fmax_pres (P : Float → Prop) {a b : Float} (ha : P a) (hb : P b) : P (fmax a b) := by
  rcases fmax_cases a b with h | h <;> rw [h] <;> assumption

/-- **Interval mul is optimal** (finite endpoints). -/
theorem mul_iv_optimal {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → f ≤ x * y) →
        hiEncloses? (bitsToEVal (X * Y).lo.toBits) f) ∧
      (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → x * y ≤ f) →
        loEncloses? (bitsToEVal (X * Y).hi.toBits) f) := by
  rw [mul_eq_four_corners (anyNan_of_finIv hX hY) hX.1 hX.2.1 hY.1 hY.2.1]
  have mXl := memIv_lo hX
  have mXh := memIv_hi hX
  have mYl := memIv_lo hY
  have mYh := memIv_hi hY
  constructor
  · intro f hf hall
    let P : Float → Prop := fun g => hiEncloses? (bitsToEVal g.toBits) f
    have c : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
        bitsToRat? b.toBits = some qb → MemIv qa X → MemIv qb Y → P (Directed.mulDown a b) :=
      fun a b qa qb ha hb hma hmb => (mulDown_float_tight ha hb).2 f hf (hall _ _ hma hmb)
    exact fmin_pres P (c _ _ _ _ hX.2.1 hY.2.1 mXh mYh)
      (fmin_pres P (c _ _ _ _ hX.2.1 hY.1 mXh mYl)
        (fmin_pres P (c _ _ _ _ hX.1 hY.2.1 mXl mYh) (c _ _ _ _ hX.1 hY.1 mXl mYl)))
  · intro f hf hall
    let P : Float → Prop := fun g => loEncloses? (bitsToEVal g.toBits) f
    have c : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
        bitsToRat? b.toBits = some qb → MemIv qa X → MemIv qb Y → P (Directed.mulUp a b) :=
      fun a b qa qb ha hb hma hmb => (mulUp_float_tight ha hb).2 f hf (hall _ _ hma hmb)
    exact fmax_pres P (c _ _ _ _ hX.2.1 hY.2.1 mXh mYh)
      (fmax_pres P (c _ _ _ _ hX.2.1 hY.1 mXh mYl)
        (fmax_pres P (c _ _ _ _ hX.1 hY.2.1 mXl mYh) (c _ _ _ _ hX.1 hY.1 mXl mYl)))

theorem not_nan_of_isRoundDown {g : Float} {x : Rat} (h : IsRoundDown x (bitsToEVal g.toBits)) :
    g.isNaN = false := by
  rcases eval_of_isRoundDown h with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem not_nan_of_isRoundUp {g : Float} {x : Rat} (h : IsRoundUp x (bitsToEVal g.toBits)) :
    g.isNaN = false := by
  rcases eval_of_isRoundUp h with ⟨ev, hev⟩
  exact not_isNaN_of_bitsToEVal hev

theorem divisor_ne_zero {Y : Interval64} {l₂ h₂ : Rat} (hY : FinIv Y l₂ h₂)
    (hz : containsZero Y = false) : l₂ ≠ 0 ∧ h₂ ≠ 0 :=
  ne_zero_of_same_sign hY.2.2 (not_containsZero_same_sign hY.1 hY.2.1 hz)

/-- With `0 ∉ Y` and finite endpoints, `X / Y` is the four-corner min/max. -/
theorem div_eq_corners {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) (hz : containsZero Y = false) :
    X / Y =
      ⟨fmin (Directed.divDown X.lo Y.lo) (fmin (Directed.divDown X.lo Y.hi)
          (fmin (Directed.divDown X.hi Y.lo) (Directed.divDown X.hi Y.hi))),
        fmax (Directed.divUp X.lo Y.lo) (fmax (Directed.divUp X.lo Y.hi)
          (fmax (Directed.divUp X.hi Y.lo) (Directed.divUp X.hi Y.hi)))⟩ := by
  have ⟨hl0, hh0⟩ := divisor_ne_zero hY hz
  let P : Float → Prop := fun g => g.isNaN = false
  have hd : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
      bitsToRat? b.toBits = some qb → qb ≠ 0 → P (Directed.divDown a b) :=
    fun _ _ _ _ ha hb h0 => not_nan_of_isRoundDown (divDown_float_tight ha hb h0)
  have hu : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
      bitsToRat? b.toBits = some qb → qb ≠ 0 → P (Directed.divUp a b) :=
    fun _ _ _ _ ha hb h0 => not_nan_of_isRoundUp (divUp_float_tight ha hb h0)
  have hlo : P (fmin (Directed.divDown X.lo Y.lo) (fmin (Directed.divDown X.lo Y.hi)
      (fmin (Directed.divDown X.hi Y.lo) (Directed.divDown X.hi Y.hi)))) :=
    fmin_pres P (hd _ _ _ _ hX.1 hY.1 hl0) (fmin_pres P (hd _ _ _ _ hX.1 hY.2.1 hh0)
      (fmin_pres P (hd _ _ _ _ hX.2.1 hY.1 hl0) (hd _ _ _ _ hX.2.1 hY.2.1 hh0)))
  have hhi : P (fmax (Directed.divUp X.lo Y.lo) (fmax (Directed.divUp X.lo Y.hi)
      (fmax (Directed.divUp X.hi Y.lo) (Directed.divUp X.hi Y.hi)))) :=
    fmax_pres P (hu _ _ _ _ hX.1 hY.1 hl0) (fmax_pres P (hu _ _ _ _ hX.1 hY.2.1 hh0)
      (fmax_pres P (hu _ _ _ _ hX.2.1 hY.1 hl0) (hu _ _ _ _ hX.2.1 hY.2.1 hh0)))
  change Interval64.div X Y = _
  unfold Interval64.div
  simp only [anyNan_of_finIv hX hY, hz]
  simp only [P] at hlo hhi
  simp [hlo, hhi]

/-- **Interval div is optimal** when `0 ∉ Y` (finite endpoints). -/
theorem div_iv_optimal {X Y : Interval64} {l₁ h₁ l₂ h₂ : Rat}
    (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) (hz : containsZero Y = false) :
    (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → f ≤ x / y) →
        hiEncloses? (bitsToEVal (X / Y).lo.toBits) f) ∧
      (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → x / y ≤ f) →
        loEncloses? (bitsToEVal (X / Y).hi.toBits) f) := by
  have ⟨hl0, hh0⟩ := divisor_ne_zero hY hz
  rw [div_eq_corners hX hY hz]
  have mXl := memIv_lo hX
  have mXh := memIv_hi hX
  have mYl := memIv_lo hY
  have mYh := memIv_hi hY
  constructor
  · intro f hf hall
    let P : Float → Prop := fun g => hiEncloses? (bitsToEVal g.toBits) f
    have c : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
        bitsToRat? b.toBits = some qb → qb ≠ 0 → MemIv qa X → MemIv qb Y →
        P (Directed.divDown a b) :=
      fun a b qa qb ha hb h0 hma hmb => (divDown_float_tight ha hb h0).2 f hf (hall _ _ hma hmb)
    exact fmin_pres P (c _ _ _ _ hX.1 hY.1 hl0 mXl mYl)
      (fmin_pres P (c _ _ _ _ hX.1 hY.2.1 hh0 mXl mYh)
        (fmin_pres P (c _ _ _ _ hX.2.1 hY.1 hl0 mXh mYl) (c _ _ _ _ hX.2.1 hY.2.1 hh0 mXh mYh)))
  · intro f hf hall
    let P : Float → Prop := fun g => loEncloses? (bitsToEVal g.toBits) f
    have c : ∀ (a b : Float) (qa qb : Rat), bitsToRat? a.toBits = some qa →
        bitsToRat? b.toBits = some qb → qb ≠ 0 → MemIv qa X → MemIv qb Y →
        P (Directed.divUp a b) :=
      fun a b qa qb ha hb h0 hma hmb => (divUp_float_tight ha hb h0).2 f hf (hall _ _ hma hmb)
    exact fmax_pres P (c _ _ _ _ hX.1 hY.1 hl0 mXl mYl)
      (fmax_pres P (c _ _ _ _ hX.1 hY.2.1 hh0 mXl mYh)
        (fmax_pres P (c _ _ _ _ hX.2.1 hY.1 hl0 mXh mYl) (c _ _ _ _ hX.2.1 hY.2.1 hh0 mXh mYh)))

end Interval64Proofs.TightIv
