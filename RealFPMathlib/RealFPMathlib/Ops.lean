/-
Real semantics of the extra interval operations (`Interval64.Ops`).

Membership (`x ∈ X → f x ∈ F X`, no finiteness assumptions):
`mem_neg`, `mem_abs`, `mem_square` (`x ^ 2 ∈ square X`), `mem_pown`, `mem_min`,
`mem_max`, `mem_inv` (`x⁻¹`, Lean's `0⁻¹ = 0`).
Sets: `toSet_intersect` (`= X ∩ Y`), `union_subset_toSet_hull`, `toSet_subset_of_subset`,
`mem_of_contains`, `bisect_cover`, `bisect_fst_subset` / `bisect_snd_subset`.
Scalars: `mid_spec` (`lo ≤ mid ≤ hi`), `contains_mid`, `abs_le_mag`, `mig_le_abs`,
`sub_le_width` (`x - y ≤ width X` for `x, y ∈ X`), `width_ge` (`hi - lo ≤ width`).
-/
import RealFPMathlib.Split
import Interval64.Ops

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.FloatBits Interval64Proofs.Pack
open Interval64Proofs.PackFinite Interval64Proofs.Canonical
open Float.Model

noncomputable section

namespace RealFP

/-! ### Negation of a float -/

theorem unpack_neg {f : Float} (hf : f.isNaN = false) :
    unpackBits (-f).toBits = (unpackBits f.toBits).neg := by
  have hb : (-f).toBits = packBits (unpackBits f.toBits).neg := rfl
  rw [hb]
  have hok := uOk_of_float hf
  revert hok
  cases unpackBits f.toBits with
  | notANumber => intro h; exact h.elim
  | infinity s => intro _; exact unpackBits_inf _
  | zero s => intro _; exact unpackBits_zero _
  | finite s m e hm =>
    intro hc
    rcases hc with hs | hn
    · exact unpackBits_pack_subnormal _ hm hs
    · exact unpackBits_pack_normal _ hm hn

theorem isNaN_neg {f : Float} (hf : f.isNaN = false) : (-f).isNaN = false := by
  have h := hf
  rw [float_isNaN] at h ⊢
  rw [unpack_neg hf]
  revert h
  cases unpackBits f.toBits <;> simp [UnpackedFloat.neg, UnpackedFloat.isNaN]

theorem toE_neg {f : Float} (hf : f.isNaN = false) : (-f).toE = -f.toE := by
  unfold Float.toE
  rw [unpack_neg hf]
  cases unpackBits f.toBits with
  | notANumber => simp [UnpackedFloat.neg, uE]
  | infinity s => cases s <;> simp [UnpackedFloat.neg, uE]
  | zero s => simp [UnpackedFloat.neg, uE]
  | finite s m e hm =>
    cases s <;> simp [UnpackedFloat.neg, uE, Interval64Proofs.Pow2.signedVal]

/-! ### Small `EReal` facts -/

theorem ereal_coe_neg (x : ℝ) : ((-x : ℝ) : EReal) = -(x : EReal) := EReal.coe_neg x

theorem ereal_sq_le {a : EReal} {x : ℝ} (h0 : 0 ≤ a) (h : a ≤ x) :
    a * a ≤ ((x * x : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact absurd h0 (by simp)
  | coe r =>
    have h0' : (0 : ℝ) ≤ r := by exact_mod_cast h0
    have h' : r ≤ x := by exact_mod_cast h
    rw [← EReal.coe_mul]; exact_mod_cast mul_le_mul h' h' h0' (le_trans h0' h')
  | top => exact absurd h (by simp)

theorem ereal_le_sq {b : EReal} {x : ℝ} (hx : 0 ≤ x) (h : (x : EReal) ≤ b) :
    ((x * x : ℝ) : EReal) ≤ b * b := by
  induction b using EReal.rec with
  | bot => exact absurd h (by simp)
  | coe r =>
    have h' : x ≤ r := by exact_mod_cast h
    rw [← EReal.coe_mul]; exact_mod_cast mul_le_mul h' h' hx (le_trans hx h')
  | top => simp

theorem ereal_sq_le_neg {b : EReal} {x : ℝ} (h0 : b ≤ 0) (h : (x : EReal) ≤ b) :
    b * b ≤ ((x * x : ℝ) : EReal) := by
  induction b using EReal.rec with
  | bot => exact absurd h (by simp)
  | coe r =>
    have h0' : r ≤ 0 := by exact_mod_cast h0
    have h' : x ≤ r := by exact_mod_cast h
    rw [← EReal.coe_mul]; exact_mod_cast (by nlinarith : r * r ≤ x * x)
  | top => exact absurd h0 (by simp)

theorem ereal_le_sq_neg {a : EReal} {x : ℝ} (hx : x ≤ 0) (h : a ≤ x) :
    ((x * x : ℝ) : EReal) ≤ a * a := by
  induction a using EReal.rec with
  | bot => simp
  | coe r =>
    have h' : r ≤ x := by exact_mod_cast h
    rw [← EReal.coe_mul]; exact_mod_cast (by nlinarith : x * x ≤ r * r)
  | top => exact absurd h (by simp)

theorem not_skip_self (a : EReal) : ¬ SkipMul a a := by
  rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩) <;> rw [h1] at h2 <;> simp at h2

theorem le_float_nan_right {a b : Float} (hb : b.isNaN = true) : ¬ a ≤ b := by
  intro h
  rw [float_le_iff] at h
  rw [float_isNaN] at hb
  revert h hb
  cases unpackBits a.toBits <;> cases unpackBits b.toBits <;>
    simp [UnpackedFloat.isNaN, UnpackedFloat.le, UnpackedFloat.compare]

theorem le_float_nan_left {a b : Float} (ha : a.isNaN = true) : ¬ a ≤ b := by
  intro h
  rw [float_le_iff] at h
  rw [float_isNaN] at ha
  revert h ha
  cases unpackBits a.toBits <;> cases unpackBits b.toBits <;>
    simp [UnpackedFloat.isNaN, UnpackedFloat.le, UnpackedFloat.compare]

theorem notNaN_of_le_right {a b : Float} (h : a ≤ b) : b.isNaN = false := by
  cases hb : b.isNaN
  · rfl
  · exact absurd h (le_float_nan_right hb)

theorem notNaN_of_le_left {a b : Float} (h : a ≤ b) : a.isNaN = false := by
  cases ha : a.isNaN
  · rfl
  · exact absurd h (le_float_nan_left ha)

/-! ### `neg`, `abs` -/

theorem mem_neg {X : Interval64} {x : ℝ} (hx : x ∈ X) : -x ∈ -X := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  refine mem_toSet_of_toE (I := ⟨-X.hi, -X.lo⟩) (isNaN_neg hh) (isNaN_neg hl) ?_ ?_
  · show (-X.hi).toE ≤ _
    rw [toE_neg hh, ereal_coe_neg]; exact EReal.neg_le_neg_iff.2 hh'
  · show _ ≤ (-X.lo).toE
    rw [toE_neg hl, ereal_coe_neg]; exact EReal.neg_le_neg_iff.2 hl'

theorem mem_abs {X : Interval64} {x : ℝ} (hx : x ∈ X) : |x| ∈ Interval64.abs X := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  show |x| ∈ (Interval64.abs X).toSet
  unfold Interval64.abs
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : (0 : Float) ≤ X.lo
  · simp only [h0, decide_true, ↓reduceIte]
    have : 0 ≤ x := by
      have := le_trans ((zero_le_iff_toE hl).1 h0) hl'; exact_mod_cast this
    rw [abs_of_nonneg this]; exact hx
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hlo : X.lo.toE < 0 := by
    rw [zero_le_iff_toE hl] at h0; exact not_le.1 h0
  by_cases h1 : X.hi ≤ (0 : Float)
  · simp only [h1, decide_true, ↓reduceIte]
    have : x ≤ 0 := by
      have := le_trans hh' ((le_zero_iff_toE hh).1 h1); exact_mod_cast this
    rw [abs_of_nonpos this]
    exact mem_neg hx
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine mem_toSet_of_toE (I := ⟨0, fmax (-X.lo) X.hi⟩) isNaN_zero
    (fmax_isNaN (isNaN_neg hl) hh) ?_ ?_
  · show (0 : Float).toE ≤ _
    rw [toE_zero]; exact_mod_cast abs_nonneg x
  · show _ ≤ (fmax (-X.lo) X.hi).toE
    rw [toE_fmax (isNaN_neg hl) hh, toE_neg hl]
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]; exact le_trans hh' (le_max_right _ _)
    · rw [abs_of_nonpos hx0, ereal_coe_neg]
      exact le_trans (EReal.neg_le_neg_iff.2 hl') (le_max_left _ _)

/-- The lower end of `abs X` is `≥ 0`. -/
theorem abs_lo_nonneg {X : Interval64} (hl : X.lo.isNaN = false) (hh : X.hi.isNaN = false) :
    0 ≤ (Interval64.abs X).lo.toE ∧ (Interval64.abs X).lo.isNaN = false := by
  unfold Interval64.abs
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : (0 : Float) ≤ X.lo
  · simp only [h0, decide_true, ↓reduceIte]; exact ⟨(zero_le_iff_toE hl).1 h0, hl⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : X.hi ≤ (0 : Float)
  · simp only [h1, decide_true, ↓reduceIte]
    refine ⟨?_, isNaN_neg hh⟩
    rw [toE_neg hh]; exact EReal.neg_nonneg.2 ((le_zero_iff_toE hh).1 h1)
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by rw [toE_zero], isNaN_zero⟩

/-! ### `square` -/

theorem mulDown_self {a : Float} (ha : a.isNaN = false) :
    (Directed.mulDown a a).isNaN = false ∧ (Directed.mulDown a a).toE ≤ a.toE * a.toE :=
  (corner_mul ha ha (not_skip_self _)).1

theorem mulUp_self {a : Float} (ha : a.isNaN = false) :
    (Directed.mulUp a a).isNaN = false ∧ a.toE * a.toE ≤ (Directed.mulUp a a).toE :=
  (corner_mul ha ha (not_skip_self _)).2

theorem mem_square_mul {X : Interval64} {x : ℝ} (hx : x ∈ X) : x * x ∈ square X := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  show x * x ∈ (square X).toSet
  unfold square
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : (0 : Float) ≤ X.lo
  · simp only [h0, decide_true, ↓reduceIte]
    have hl0 := (zero_le_iff_toE hl).1 h0
    have hx0 : 0 ≤ x := by have := le_trans hl0 hl'; exact_mod_cast this
    obtain ⟨d1, d2⟩ := mulDown_self hl
    obtain ⟨u1, u2⟩ := mulUp_self hh
    exact mem_toSet_of_toE (I := ⟨_, _⟩) d1 u1 (le_trans d2 (ereal_sq_le hl0 hl'))
      (le_trans (ereal_le_sq hx0 hh') u2)
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hlo : X.lo.toE < 0 := by
    rw [zero_le_iff_toE hl] at h0; exact not_le.1 h0
  by_cases h1 : X.hi ≤ (0 : Float)
  · simp only [h1, decide_true, ↓reduceIte]
    have hh0 := (le_zero_iff_toE hh).1 h1
    have hx0 : x ≤ 0 := by have := le_trans hh' hh0; exact_mod_cast this
    obtain ⟨d1, d2⟩ := mulDown_self hh
    obtain ⟨u1, u2⟩ := mulUp_self hl
    exact mem_toSet_of_toE (I := ⟨_, _⟩) d1 u1 (le_trans d2 (ereal_sq_le_neg hh0 hh'))
      (le_trans (ereal_le_sq_neg hx0 hl') u2)
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨u1, u2⟩ := mulUp_self hl
  obtain ⟨v1, v2⟩ := mulUp_self hh
  refine mem_toSet_of_toE (I := ⟨_, _⟩) isNaN_zero (fmax_isNaN u1 v1) ?_ ?_
  · show (0 : Float).toE ≤ _
    rw [toE_zero]; exact_mod_cast mul_self_nonneg x
  · show _ ≤ (fmax _ _).toE
    rw [toE_fmax u1 v1]
    rcases le_total 0 x with hx0 | hx0
    · exact le_trans (le_trans (ereal_le_sq hx0 hh') v2) (le_max_right _ _)
    · exact le_trans (le_trans (ereal_le_sq_neg hx0 hl') u2) (le_max_left _ _)

/-- `x ^ 2 ∈ square X` for every `x ∈ X` (no finiteness assumption). -/
theorem mem_square {X : Interval64} {x : ℝ} (hx : x ∈ X) : x ^ 2 ∈ square X := by
  rw [sq]; exact mem_square_mul hx

/-! ### `min`, `max` -/

theorem mem_min {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    min x y ∈ Interval64.min X Y := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan X Y = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  show min x y ∈ (Interval64.min X Y).toSet
  unfold Interval64.min
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  refine mem_toSet_of_toE (I := ⟨_, _⟩) (fmin_isNaN hXl hYl) (fmin_isNaN hXh hYh) ?_ ?_
  · show (fmin _ _).toE ≤ _
    rw [toE_fmin hXl hYl]
    rcases le_total x y with h | h
    · rw [min_eq_left h]; exact le_trans (min_le_left _ _) hXl'
    · rw [min_eq_right h]; exact le_trans (min_le_right _ _) hYl'
  · show _ ≤ (fmin _ _).toE
    rw [toE_fmin hXh hYh]
    rcases le_total x y with h | h
    · rw [min_eq_left h]
      exact le_min hXh' (le_trans (by exact_mod_cast h) hYh')
    · rw [min_eq_right h]
      exact le_min (le_trans (by exact_mod_cast h) hXh') hYh'

theorem mem_max {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    max x y ∈ Interval64.max X Y := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan X Y = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  show max x y ∈ (Interval64.max X Y).toSet
  unfold Interval64.max
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  refine mem_toSet_of_toE (I := ⟨_, _⟩) (fmax_isNaN hXl hYl) (fmax_isNaN hXh hYh) ?_ ?_
  · show (fmax _ _).toE ≤ _
    rw [toE_fmax hXl hYl]
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      exact max_le (le_trans hXl' (by exact_mod_cast h)) hYl'
    · rw [max_eq_left h]
      exact max_le hXl' (le_trans hYl' (by exact_mod_cast h))
  · show _ ≤ (fmax _ _).toE
    rw [toE_fmax hXh hYh]
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_trans hYh' (le_max_right _ _)
    · rw [max_eq_left h]; exact le_trans hXh' (le_max_left _ _)

/-! ### `inv` -/

theorem real_of_toE {f : Float} (hn : f.isNaN = false) (hb : f.toE ≠ ⊥) (ht : f.toE ≠ ⊤) :
    ∃ r : ℝ, f.toE = (r : EReal) := by
  obtain ⟨q, -, he⟩ := exists_rat_of_toE hn hb ht
  exact ⟨q, he⟩

/-- `x⁻¹ ∈ inv X` for every `x ∈ X` (if `0 ∈ X` the result is `whole`). -/
theorem mem_inv {X : Interval64} {x : ℝ} (hx : x ∈ X) : x⁻¹ ∈ inv X := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  show x⁻¹ ∈ (inv X).toSet
  unfold inv
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  cases hcz : containsZero X with
  | true => exact mem_whole _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsign : 0 < X.lo.toE ∨ X.hi.toE < 0 := by
    by_contra hc
    push Not at hc
    rw [(containsZero_iff_toE hl hh).2 ⟨hc.1, hc.2⟩] at hcz
    exact absurd hcz (by simp)
  rw [inv_eq_one_div]
  have h1 : ((1 : ℝ) : EReal) = (1 : Float).toE := by simp
  rcases hsign with hp | hn
  · have hxp : 0 < x := by have := lt_of_lt_of_le hp hl'; exact_mod_cast this
    obtain ⟨l, hle⟩ := real_of_toE hl (fun h => by rw [h] at hp; simp at hp)
      (fun h => by rw [h] at hl'; simp at hl')
    rw [hle] at hp hl'
    have hl0 : 0 < l := by exact_mod_cast hp
    have hlx : l ≤ x := by exact_mod_cast hl'
    obtain ⟨d1, d2⟩ := divDown_good isNaN_one hh (by
      rw [← h1]; exact goodDLo_pp one_pos le_rfl hxp hh')
    obtain ⟨u1, u2⟩ := divUp_good (p := 1 / x) isNaN_one hl (by
      rw [← h1, hle]
      refine ⟨by simp, by exact_mod_cast hl0.ne', coe_le_div ?_⟩
      exact one_div_le_one_div_of_le hl0 hlx)
    exact mem_toSet_of_toE (I := ⟨_, _⟩) d1 u1 d2 u2
  · have hxn : x < 0 := by have := lt_of_le_of_lt hh' hn; exact_mod_cast this
    obtain ⟨h, hhe⟩ := real_of_toE hh (fun h => by rw [h] at hh'; simp at hh')
      (fun h => by rw [h] at hn; simp at hn)
    rw [hhe] at hn hh'
    have hh0 : h < 0 := by exact_mod_cast hn
    have hxh : x ≤ h := by exact_mod_cast hh'
    obtain ⟨d1, d2⟩ := divDown_good (p := 1 / x) isNaN_one hh (by
      rw [← h1, hhe]
      refine ⟨by simp, by exact_mod_cast hh0.ne, coe_div_le ?_⟩
      exact one_div_le_one_div_of_neg_of_le hh0 hxh)
    obtain ⟨u1, u2⟩ := divUp_good isNaN_one hl (by
      rw [← h1]; exact goodDHi_pn one_pos le_rfl hxn hl')
    exact mem_toSet_of_toE (I := ⟨_, _⟩) d1 u1 d2 u2

/-! ### `intersect`, `hull` -/

/-- `intersect` is exactly the set intersection (empty ↦ `invalid`). -/
theorem toSet_intersect (X Y : Interval64) :
    (intersect X Y).toSet = X.toSet ∩ Y.toSet := by
  ext x
  constructor
  · intro hx
    unfold intersect at hx
    cases hn : anyNan X Y with
    | true => simp only [hn, ↓reduceIte] at hx; exact absurd hx (not_mem_invalid x)
    | false =>
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at hx
    have hn' := hn
    simp only [anyNan, Bool.or_eq_false_iff] at hn'
    obtain ⟨⟨⟨hXl, hXh⟩, hYl⟩, hYh⟩ := hn'
    split at hx
    · obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 hx
      rw [toE_fmax hXl hYl] at h1
      rw [toE_fmin hXh hYh] at h2
      exact ⟨mem_toSet_of_toE hXl hXh (le_trans (le_max_left _ _) h1)
          (le_trans h2 (min_le_left _ _)),
        mem_toSet_of_toE hYl hYh (le_trans (le_max_right _ _) h1)
          (le_trans h2 (min_le_right _ _))⟩
    · exact absurd hx (not_mem_invalid x)
  · rintro ⟨hx, hy⟩
    obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
    obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
    have hnan : anyNan X Y = false := by simp [anyNan, hXl, hXh, hYl, hYh]
    have h1 : (fmax X.lo Y.lo).toE ≤ x := by rw [toE_fmax hXl hYl]; exact max_le hXl' hYl'
    have h2 : (x : EReal) ≤ (fmin X.hi Y.hi).toE := by
      rw [toE_fmin hXh hYh]; exact le_min hXh' hYh'
    have hle : fmax X.lo Y.lo ≤ fmin X.hi Y.hi :=
      (float_le_iff_toE (fmax_isNaN hXl hYl) (fmin_isNaN hXh hYh)).2 (le_trans h1 h2)
    unfold intersect
    simp only [hnan, Bool.false_eq_true, ↓reduceIte, hle, decide_true]
    exact mem_toSet_of_toE (fmax_isNaN hXl hYl) (fmin_isNaN hXh hYh) h1 h2

theorem mem_intersect {X Y : Interval64} {x : ℝ} (hx : x ∈ X) (hy : x ∈ Y) :
    x ∈ intersect X Y := by
  show x ∈ (intersect X Y).toSet; rw [toSet_intersect]; exact ⟨hx, hy⟩

/-- `hull X Y` contains both arguments. -/
theorem union_subset_toSet_hull (X Y : Interval64) :
    X.toSet ∪ Y.toSet ⊆ (hull X Y).toSet := by
  rintro x (hx | hx)
  · obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
    unfold hull
    simp only [hXl, hXh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases hY : (Y.lo.isNaN || Y.hi.isNaN) with
    | true => simpa using hx
    | false =>
    simp only [Bool.or_eq_false_iff] at hY
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine mem_toSet_of_toE (I := ⟨_, _⟩) (fmin_isNaN hXl hY.1) (fmax_isNaN hXh hY.2) ?_ ?_
    · show (fmin _ _).toE ≤ _
      rw [toE_fmin hXl hY.1]; exact le_trans (min_le_left _ _) hXl'
    · show _ ≤ (fmax _ _).toE
      rw [toE_fmax hXh hY.2]; exact le_trans hXh' (le_max_left _ _)
  · obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hx
    unfold hull
    cases hX : (X.lo.isNaN || X.hi.isNaN) with
    | true => simpa using hx
    | false =>
    simp only [Bool.or_eq_false_iff] at hX
    simp only [hYl, hYh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    refine mem_toSet_of_toE (I := ⟨_, _⟩) (fmin_isNaN hX.1 hYl) (fmax_isNaN hX.2 hYh) ?_ ?_
    · show (fmin _ _).toE ≤ _
      rw [toE_fmin hX.1 hYl]; exact le_trans (min_le_right _ _) hYl'
    · show _ ≤ (fmax _ _).toE
      rw [toE_fmax hX.2 hYh]; exact le_trans hYh' (le_max_right _ _)

theorem mem_hull_left {X Y : Interval64} {x : ℝ} (hx : x ∈ X) : x ∈ hull X Y :=
  union_subset_toSet_hull X Y (Or.inl hx)

theorem mem_hull_right {X Y : Interval64} {x : ℝ} (hy : x ∈ Y) : x ∈ hull X Y :=
  union_subset_toSet_hull X Y (Or.inr hy)

/-! ### `subset`, `contains` -/

theorem toSet_subset_of_subset {X Y : Interval64} (h : subset X Y = true) :
    X.toSet ⊆ Y.toSet := by
  simp only [subset, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hn, h1⟩, h2⟩ := h
  simp only [anyNan, Bool.or_eq_false_iff] at hn
  obtain ⟨⟨⟨hXl, hXh⟩, hYl⟩, hYh⟩ := hn
  intro x hx
  obtain ⟨⟨-, hXl'⟩, ⟨-, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  exact mem_toSet_of_toE hYl hYh (le_trans ((float_le_iff_toE hYl hXl).1 h1) hXl')
    (le_trans hXh' ((float_le_iff_toE hXh hYh).1 h2))

/-- `contains X f` (with `f` finite, value `r`) gives `r ∈ X`. -/
theorem mem_of_contains {X : Interval64} {f : Float} {r : ℝ} (h : contains X f = true)
    (hf : f.toReal? = some r) : r ∈ X := by
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hfn := notNaN_of_le_right h1
  have hl := notNaN_of_le_left h1
  have hh := notNaN_of_le_right h2
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hf
  have he := toE_of_bitsToRat? hq
  refine mem_toSet_of_toE hl hh ?_ ?_
  · rw [← he]; exact (float_le_iff_toE hl hfn).1 h1
  · rw [← he]; exact (float_le_iff_toE hfn hh).1 h2

/-! ### `mag`, `mig` -/

theorem abs_le_mag {X : Interval64} {x : ℝ} (hx : x ∈ X) :
    (mag X).isNaN = false ∧ ((|x| : ℝ) : EReal) ≤ (mag X).toE := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  refine ⟨fmax_isNaN (isNaN_neg hl) hh, ?_⟩
  unfold mag
  rw [toE_fmax (isNaN_neg hl) hh, toE_neg hl]
  rcases le_total 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0]; exact le_trans hh' (le_max_right _ _)
  · rw [abs_of_nonpos hx0, ereal_coe_neg]
    exact le_trans (EReal.neg_le_neg_iff.2 hl') (le_max_left _ _)

theorem mig_le_abs {X : Interval64} {x : ℝ} (hx : x ∈ X) :
    (mig X).isNaN = false ∧ (mig X).toE ≤ ((|x| : ℝ) : EReal) := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  unfold mig
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : (0 : Float) ≤ X.lo
  · simp only [h0, decide_true, ↓reduceIte]
    refine ⟨hl, le_trans hl' ?_⟩
    exact_mod_cast le_abs_self x
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : X.hi ≤ (0 : Float)
  · simp only [h1, decide_true, ↓reduceIte]
    refine ⟨isNaN_neg hh, ?_⟩
    rw [toE_neg hh]
    refine le_trans (EReal.neg_le_neg_iff.2 hh') ?_
    rw [← ereal_coe_neg]; exact_mod_cast neg_le_abs x
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact ⟨isNaN_zero, by rw [toE_zero]; exact_mod_cast abs_nonneg x⟩

/-! ### `mid`, `bisect` -/

/-- Clamping into `[lo, hi]` (`lo ≤ hi`, both not NaN) lands in `[lo, hi]`, even for a NaN `m`. -/
theorem clamp_spec {m lo hi : Float} (hl : lo.isNaN = false) (hh : hi.isNaN = false)
    (hle : lo.toE ≤ hi.toE) :
    (fmin (fmax m lo) hi).isNaN = false ∧ lo.toE ≤ (fmin (fmax m lo) hi).toE ∧
      (fmin (fmax m lo) hi).toE ≤ hi.toE := by
  have ht : (fmax m lo).isNaN = false ∧ lo.toE ≤ (fmax m lo).toE := by
    cases hm : m.isNaN
    · exact ⟨fmax_isNaN hm hl, by rw [toE_fmax hm hl]; exact le_max_right _ _⟩
    · have : fmax m lo = lo := by
        unfold fmax
        rw [ite_eq_right (by simpa using float_lt_nan_right (a := lo) hm)]
      rw [this]; exact ⟨hl, le_rfl⟩
  refine ⟨fmin_isNaN ht.1 hh, ?_, ?_⟩
  · rw [toE_fmin ht.1 hh]; exact le_min ht.2 hle
  · rw [toE_fmin ht.1 hh]; exact min_le_right _ _

theorem isNaN_nan : Float.nan.isNaN = true := by decide +kernel

theorem fmin_le_right_of {t hi : Float} (h : (fmin t hi).isNaN = false) :
    hi.isNaN = false ∧ (fmin t hi).toE ≤ hi.toE := by
  have hh := fmin_nan_right h
  refine ⟨hh, ?_⟩
  cases ht : t.isNaN
  · rw [toE_fmin ht hh]; exact min_le_right _ _
  · have : fmin t hi = hi := by
      unfold fmin; rw [ite_eq_right (by simpa using float_lt_nan_left (b := hi) ht)]
    rw [this]

theorem mid_eq {X : Interval64} (hl : X.lo.isNaN = false) (hh : X.hi.isNaN = false) :
    mid X = fmin (fmax (midRaw X) X.lo) X.hi := by
  simp [mid, hl, hh]

/-- If `mid X` is not NaN, neither endpoint is, and `lo ≤ mid ≤ hi` holds whenever
    `lo ≤ hi`; in any case `mid X ≤ hi`. -/
theorem mid_notNaN {X : Interval64} (h : (mid X).isNaN = false) :
    X.lo.isNaN = false ∧ X.hi.isNaN = false := by
  cases h' : (X.lo.isNaN || X.hi.isNaN) with
  | true =>
    have : mid X = Float.nan := by simp [mid, h']
    rw [this, isNaN_nan] at h; exact absurd h (by simp)
  | false => simpa [Bool.or_eq_false_iff] using h'

theorem mid_le_hi {X : Interval64} (h : (mid X).isNaN = false) : (mid X).toE ≤ X.hi.toE := by
  obtain ⟨hl, hh⟩ := mid_notNaN h
  rw [mid_eq hl hh] at h ⊢
  exact (fmin_le_right_of h).2

/-- For a nonempty `X`, `mid X` is not NaN and lies in `[lo, hi]`. -/
theorem mid_spec {X : Interval64} {x : ℝ} (hx : x ∈ X) :
    (mid X).isNaN = false ∧ X.lo.toE ≤ (mid X).toE ∧ (mid X).toE ≤ X.hi.toE := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  rw [mid_eq hl hh]
  exact clamp_spec hl hh (le_trans hl' hh')

/-- `mid X ∈ X` as a float (`contains`). -/
theorem contains_mid {X : Interval64} {x : ℝ} (hx : x ∈ X) : contains X (mid X) = true := by
  obtain ⟨⟨hl, -⟩, ⟨hh, -⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨hm, h1, h2⟩ := mid_spec hx
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨(float_le_iff_toE hl hm).2 h1, (float_le_iff_toE hm hh).2 h2⟩

/-- The two halves of `bisect X` cover `X`. -/
theorem bisect_cover {X : Interval64} {x : ℝ} (hx : x ∈ X) :
    x ∈ (bisect X).1 ∨ x ∈ (bisect X).2 := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨hm, -, -⟩ := mid_spec hx
  rcases le_total (x : EReal) (mid X).toE with h | h
  · exact Or.inl (mem_toSet_of_toE (I := ⟨X.lo, mid X⟩) hl hm hl' h)
  · exact Or.inr (mem_toSet_of_toE (I := ⟨mid X, X.hi⟩) hm hh h hh')

theorem bisect_fst_subset (X : Interval64) : (bisect X).1.toSet ⊆ X.toSet := by
  intro x hx
  obtain ⟨⟨hl, hl'⟩, ⟨hm, hm'⟩⟩ := mem_toSet_iff_toE.1 hx
  change X.lo.isNaN = false at hl; change X.lo.toE ≤ _ at hl'
  change (mid X).isNaN = false at hm; change _ ≤ (mid X).toE at hm'
  exact mem_toSet_of_toE hl (mid_notNaN hm).2 hl' (le_trans hm' (mid_le_hi hm))

/-- The second half lies in `X` (for nonempty `X`; a reversed `[lo, hi]` with `lo > hi`
    is empty but its second half `[hi, hi]` is not). -/
theorem bisect_snd_subset {X : Interval64} {x₀ : ℝ} (h₀ : x₀ ∈ X) :
    (bisect X).2.toSet ⊆ X.toSet := by
  intro x hx
  obtain ⟨⟨-, hm'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  change (mid X).toE ≤ _ at hm'
  change X.hi.isNaN = false at hh; change _ ≤ X.hi.toE at hh'
  obtain ⟨⟨hl, -⟩, -⟩ := mem_toSet_iff_toE.1 h₀
  exact mem_toSet_of_toE hl hh (le_trans (mid_spec h₀).2.1 hm') hh'

/-! ### `width` -/

/-- `x - y ≤ width X` for all `x, y ∈ X` (so `width X` bounds the diameter). -/
theorem sub_le_width {X : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ X) :
    (width X).isNaN = false ∧ ((x - y : ℝ) : EReal) ≤ (width X).toE := by
  obtain ⟨⟨hl, -⟩, ⟨hh, -⟩⟩ := mem_toSet_iff_toE.1 hx
  have hnan : anyNan X X = false := by simp [anyNan, hl, hh]
  have h := sub_mem_toSet hx hy
  have e : X - X = ⟨Directed.subDown X.lo X.hi, width X⟩ := by
    show Interval64.sub X X = _
    simp [Interval64.sub, hnan, width]
  rw [e] at h
  exact (mem_toSet_iff_toE.1 h).2

/-- `hi - lo ≤ width X` for finite endpoints `lo ≤ hi`. -/
theorem width_ge {X : Interval64} {l h : ℝ} (hl : X.lo.toReal? = some l)
    (hh : X.hi.toReal? = some h) (hlh : l ≤ h) : ((h - l : ℝ) : EReal) ≤ (width X).toE := by
  obtain ⟨ql, hql, rfl⟩ := toReal?_eq_some.1 hl
  obtain ⟨qh, hqh, rfl⟩ := toReal?_eq_some.1 hh
  have el := toE_of_bitsToRat? hql
  have eh := toE_of_bitsToRat? hqh
  have nl := isNaN_false_of_bitsToRat? hql
  have nh := isNaN_false_of_bitsToRat? hqh
  have ml : ((ql : ℚ) : ℝ) ∈ X := mem_toSet_of_toE nl nh (by rw [el]) (by rw [eh]; exact_mod_cast hlh)
  have mh : ((qh : ℚ) : ℝ) ∈ X := mem_toSet_of_toE nl nh (by rw [el]; exact_mod_cast hlh) (by rw [eh])
  exact (sub_le_width mh ml).2

/-! ### `pown` -/

theorem mem_one : (1 : ℝ) ∈ (⟨1, 1⟩ : Interval64) :=
  mem_toSet_of_toE (I := ⟨1, 1⟩) isNaN_one isNaN_one (by simp) (by simp)

theorem mem_ipowAux (fuel : ℕ) : ∀ (b acc : Interval64) (e : ℕ) (a y : ℝ), a ∈ acc → y ∈ b →
    a * y ^ e ∈ ipowAux fuel b e acc := by
  induction fuel with
  | zero =>
    intro b acc e a y ha _
    unfold ipowAux
    by_cases he : e = 0
    · subst he; simpa using ha
    · simp only [beq_iff_eq, he, ↓reduceIte]; exact mem_whole _
  | succ n ih =>
    intro b acc e a y ha hy
    unfold ipowAux
    by_cases he : e = 0
    · subst he; simpa using ha
    simp only [beq_iff_eq, he, ↓reduceIte]
    have hsq : y ^ 2 ∈ square b := mem_square hy
    have key : a * y ^ e = (a * y ^ (e % 2)) * (y ^ 2) ^ (e / 2) := by
      rw [mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [key]
    apply ih
    · rcases Nat.mod_two_eq_zero_or_one e with h | h
      · rw [h]; simpa using ha
      · rw [h]; simp only [↓reduceIte, pow_one]
        exact mem_toSet_mul ha hy
    · exact hsq

/-- `y ^ e ∈ ipow B e` for `y ∈ B`. -/
theorem mem_ipow {B : Interval64} {y : ℝ} (hy : y ∈ B) (e : ℕ) : y ^ e ∈ ipow B e := by
  have := mem_ipowAux 64 B ⟨1, 1⟩ e 1 y mem_one hy
  rw [one_mul] at this
  exact this

theorem mem_point {f : Float} {r : ℝ} (hf : f.isNaN = false) (he : f.toE = r) :
    r ∈ (⟨f, f⟩ : Interval64) :=
  mem_toSet_of_toE (I := ⟨f, f⟩) hf hf (le_of_eq he) (ge_of_eq he)

theorem isInf_false_of_real {f : Float} {r : ℝ} (he : f.toE = r) : f.isInf = false := by
  cases h : f.isInf
  · rfl
  · rcases (isInf_iff_toE.1 h).1 with h' | h' <;> rw [h'] at he <;> simp at he

theorem powLo_spec {f : Float} {r : ℝ} (hf : f.isNaN = false) (he : f.toE = r) (n : ℕ) :
    (powLo f n).isNaN = false ∧ (powLo f n).toE ≤ ((r ^ n : ℝ) : EReal) := by
  unfold powLo
  rw [isInf_false_of_real he]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟨h1, h2⟩, -⟩ := mem_toSet_iff_toE.1 (mem_ipow (mem_point hf he) n)
  exact ⟨h1, h2⟩

theorem powHi_spec {f : Float} {r : ℝ} (hf : f.isNaN = false) (he : f.toE = r) (n : ℕ) :
    (powHi f n).isNaN = false ∧ ((r ^ n : ℝ) : EReal) ≤ (powHi f n).toE := by
  unfold powHi
  rw [isInf_false_of_real he]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (mem_toSet_iff_toE.1 (mem_ipow (mem_point hf he) n)).2

theorem powLo_inf {f : Float} (h : f.isInf = true) (n : ℕ) : powLo f n = f := by
  simp [powLo, h]

theorem powHi_inf {f : Float} (h : f.isInf = true) (n : ℕ) : powHi f n = f := by
  simp [powHi, h]

/-- Lower endpoint rule: `lo ≤ z` with `p` monotone on the relevant range. -/
theorem powLo_le {f : Float} {z : ℝ} {n : ℕ} (hf : f.isNaN = false) (hz : f.toE ≤ z)
    (hmono : ∀ r : ℝ, r ≤ z → f.toE = r → r ^ n ≤ z ^ n) :
    (powLo f n).isNaN = false ∧ (powLo f n).toE ≤ ((z ^ n : ℝ) : EReal) := by
  by_cases hb : f.toE = ⊥
  · have hi : f.isInf = true := isInf_iff_toE.2 ⟨Or.inr hb, hf⟩
    rw [powLo_inf hi]; exact ⟨hf, by rw [hb]; exact bot_le⟩
  have ht : f.toE ≠ ⊤ := fun h => by rw [h] at hz; simp at hz
  obtain ⟨r, hr⟩ := real_of_toE hf hb ht
  have hrz : r ≤ z := by rw [hr] at hz; exact_mod_cast hz
  obtain ⟨h1, h2⟩ := powLo_spec hf hr n
  exact ⟨h1, le_trans h2 (by exact_mod_cast hmono r hrz hr)⟩

theorem le_powHi {f : Float} {z : ℝ} {n : ℕ} (hf : f.isNaN = false) (hz : (z : EReal) ≤ f.toE)
    (hmono : ∀ r : ℝ, z ≤ r → f.toE = r → z ^ n ≤ r ^ n) :
    (powHi f n).isNaN = false ∧ ((z ^ n : ℝ) : EReal) ≤ (powHi f n).toE := by
  by_cases ht : f.toE = ⊤
  · have hi : f.isInf = true := isInf_iff_toE.2 ⟨Or.inl ht, hf⟩
    rw [powHi_inf hi]; exact ⟨hf, by rw [ht]; exact le_top⟩
  have hb : f.toE ≠ ⊥ := fun h => by rw [h] at hz; simp at hz
  obtain ⟨r, hr⟩ := real_of_toE hf hb ht
  have hzr : z ≤ r := by rw [hr] at hz; exact_mod_cast hz
  obtain ⟨h1, h2⟩ := powHi_spec hf hr n
  exact ⟨h1, le_trans (by exact_mod_cast hmono r hzr hr) h2⟩

/-- `x ^ n ∈ pown X n` for every `x ∈ X` (no finiteness assumption). -/
theorem mem_pown {X : Interval64} {x : ℝ} (hx : x ∈ X) (n : ℕ) : x ^ n ∈ pown X n := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hx
  show x ^ n ∈ (pown X n).toSet
  unfold pown
  simp only [hl, hh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases hn : n = 0
  · subst hn; simpa using mem_one
  simp only [beq_iff_eq, hn, ↓reduceIte]
  by_cases hodd : n % 2 = 1
  · simp only [hodd, ↓reduceIte]
    have ho : Odd n := Nat.odd_iff.2 hodd
    obtain ⟨a1, a2⟩ := powLo_le (n := n) hl hl' (fun r hr _ => ho.strictMono_pow.monotone hr)
    obtain ⟨b1, b2⟩ := le_powHi (n := n) hh hh' (fun r hr _ => ho.strictMono_pow.monotone hr)
    exact mem_toSet_of_toE (I := ⟨_, _⟩) a1 b1 a2 b2
  · simp only [hodd, ↓reduceIte]
    have hev : Even n := Nat.even_iff.2 (by omega)
    have hax := mem_abs hx
    obtain ⟨⟨bl, bl'⟩, ⟨bh, bh'⟩⟩ := mem_toSet_iff_toE.1 hax
    obtain ⟨b0, -⟩ := abs_lo_nonneg hl hh
    rw [← hev.pow_abs]
    obtain ⟨a1, a2⟩ := powLo_le (n := n) bl bl' (fun r hr he => by
      have : (0 : ℝ) ≤ r := by rw [he] at b0; exact_mod_cast b0
      exact pow_le_pow_left₀ this hr n)
    obtain ⟨c1, c2⟩ := le_powHi (n := n) bh bh' (fun r hr _ =>
      pow_le_pow_left₀ (abs_nonneg x) hr n)
    exact mem_toSet_of_toE (I := ⟨_, _⟩) a1 c1 a2 c2

end RealFP
