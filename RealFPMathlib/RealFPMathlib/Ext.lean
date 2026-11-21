/-
Extended-real reading of binary64 values, used for theorems that allow
infinite interval endpoints.

* `uE u : EReal` / `Float.toE f : EReal`: the value of a non-NaN float in the
  extended reals (`-∞ ↦ ⊥`, `+∞ ↦ ⊤`); NaN has the junk value `0`.
* `ucompare_spec`: on non-NaN canonical floats, IEEE comparison is the
  comparison of the extended-real values. Hence `float_le_iff_toE`,
  `float_lt_iff_toE`.
* `loR_iff_toE` / `hiR_iff_toE`: `toSet` membership in `EReal` terms.
-/
import RealFPMathlib.Basic
import Mathlib.Data.EReal.Inv

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pow2 Interval64Proofs.Canonical Interval64Proofs.Pack
open Float.Model Float.Model.UnpackedFloat

noncomputable section

namespace RealFP

/-- Extended-real value of an unpacked float (NaN ↦ `0`, a junk value). -/
def uE : UnpackedFloat → EReal
  | .notANumber => 0
  | .infinity .negative => ⊥
  | .infinity .positive => ⊤
  | .zero _ => 0
  | .finite s m e _ => ((signedVal s m e : ℚ) : ℝ)

/-- Extended-real value of a float (NaN ↦ `0`). -/
def _root_.Float.toE (f : Float) : EReal := uE (unpackBits f.toBits)

/-- Canonical (as produced by `unpack`) and not NaN. -/
def UOk : UnpackedFloat → Prop
  | .notANumber => False
  | .finite _ m e _ => IsCanonicalFinite m e
  | _ => True

theorem uOk_of_float {f : Float} (h : f.isNaN = false) : UOk (unpackBits f.toBits) := by
  cases hu : unpackBits f.toBits with
  | notANumber => rw [float_isNaN, hu] at h; simp [UnpackedFloat.isNaN] at h
  | infinity s => trivial
  | zero s => trivial
  | finite s m e hm =>
    show IsCanonicalFinite m e
    simp only [unpackBits] at hu
    exact unpack_finite_is_canonical hu

theorem mag_lt_of_exp_lt {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂)
    (hlt : e₁ < e₂) : mag m₁ e₁ < mag m₂ e₂ := by
  have hn : IsNormal m₂ e₂ := canonical_isNormal_of_exp_lt hc₁ hc₂ hlt
  have hm₁ : m₁ < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hc₁
  have hm₂ : 2 ^ 52 ≤ m₂ := hn.2.2.1
  have hstep : mag m₁ e₁ < mag (2 ^ 52) (e₁ + 1) := by
    have : mag m₁ e₁ < mag (2 ^ 53) e₁ := mag_lt_mag hm₁
    rwa [mag_pow53_succ] at this
  have hle₁ : mag (2 ^ 52) (e₁ + 1) ≤ mag m₂ (e₁ + 1) := mag_le_mag hm₂
  have hle₂ : mag m₂ (e₁ + 1) ≤ mag m₂ e₂ := Interval64Proofs.PackFinite.mag_mono_exp (Int.add_one_le_of_lt hlt)
  exact lt_of_lt_of_le hstep (le_trans hle₁ hle₂)

/-- Lexicographic `(exponent, mantissa)` order is the value order on canonical floats. -/
theorem lex_compare_mag {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hc₁ : IsCanonicalFinite m₁ e₁) (hc₂ : IsCanonicalFinite m₂ e₂) :
    (compare e₁ e₂).then (compare m₁ m₂) = compare (mag m₁ e₁) (mag m₂ e₂) := by
  rcases lt_trichotomy e₁ e₂ with h | h | h
  · rw [(compare_lt_iff_lt.2 h)]
    exact (compare_lt_iff_lt.2 (mag_lt_of_exp_lt hc₁ hc₂ h)).symm
  · subst h
    rw [compare_eq_iff_eq.2 rfl]
    simp only [Ordering.eq_then]
    rcases lt_trichotomy m₁ m₂ with hm | hm | hm
    · rw [compare_lt_iff_lt.2 hm, compare_lt_iff_lt.2 (mag_lt_mag hm)]
    · subst hm; rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
    · rw [compare_gt_iff_gt.2 hm, compare_gt_iff_gt.2 (mag_lt_mag hm)]
  · rw [(compare_gt_iff_gt.2 h)]
    exact (compare_gt_iff_gt.2 (mag_lt_of_exp_lt hc₂ hc₁ h)).symm

theorem compare_ratE (a b : ℚ) :
    compare (((a : ℝ) : EReal)) (((b : ℝ) : EReal)) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (by exact_mod_cast h)]
  · subst h; rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
  · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2 (by exact_mod_cast h)]

theorem compare_neg_swap (a b : ℚ) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_gt_iff_gt.2 (neg_lt_neg h)]; rfl
  · subst h; rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]; rfl
  · rw [compare_gt_iff_gt.2 h, compare_lt_iff_lt.2 (neg_lt_neg h)]; rfl

theorem uE_finite_pos_pos (m : Nat) (e : Int) (hm : 0 < m) :
    (0 : EReal) < (((signedVal .positive m e : ℚ) : ℝ) : EReal) := by
  have : (0 : ℚ) < signedVal .positive m e := Interval64Proofs.ExactAdd.mag_pos hm
  exact_mod_cast this

theorem uE_finite_neg_neg (m : Nat) (e : Int) (hm : 0 < m) :
    (((signedVal .negative m e : ℚ) : ℝ) : EReal) < 0 := by
  have : signedVal .negative m e < (0 : ℚ) := by
    have := Interval64Proofs.ExactAdd.mag_pos (e := e) hm
    simp only [signedVal]; linarith
  exact_mod_cast this

/-- IEEE comparison of canonical non-NaN unpacked floats is the `EReal` comparison. -/
theorem ucompare_spec {u v : UnpackedFloat} (hu : UOk u) (hv : UOk v) :
    u.compare v = some (compare (uE u) (uE v)) := by
  cases u with
  | notANumber => exact hu.elim
  | infinity s =>
    cases v with
    | notANumber => exact hv.elim
    | infinity t =>
      cases s <;> cases t <;> simp [UnpackedFloat.compare, uE] <;> rfl
    | zero t =>
      cases s <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_lt_iff_lt.2 (by simp)).symm
        | exact congrArg some (compare_gt_iff_gt.2 (by simp)).symm
    | finite t m e hm =>
      cases s <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_lt_iff_lt.2 (EReal.bot_lt_coe _)).symm
        | exact congrArg some (compare_gt_iff_gt.2 (EReal.coe_lt_top _)).symm
  | zero s =>
    cases v with
    | notANumber => exact hv.elim
    | infinity t =>
      cases t <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_lt_iff_lt.2 (by simp)).symm
        | exact congrArg some (compare_gt_iff_gt.2 (by simp)).symm
    | zero t => simp [UnpackedFloat.compare, uE]
    | finite t m e hm =>
      have p := uE_finite_pos_pos m e hm
      have n := uE_finite_neg_neg m e hm
      cases t <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_lt_iff_lt.2 p).symm
        | exact congrArg some (compare_gt_iff_gt.2 n).symm
  | finite s m e hm =>
    cases v with
    | notANumber => exact hv.elim
    | infinity t =>
      cases s <;> cases t <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_lt_iff_lt.2 (EReal.coe_lt_top _)).symm
        | exact congrArg some (compare_gt_iff_gt.2 (EReal.bot_lt_coe _)).symm
    | zero t =>
      have p := uE_finite_pos_pos m e hm
      have n := uE_finite_neg_neg m e hm
      cases s <;> simp only [UnpackedFloat.compare, uE] <;>
        first
        | exact congrArg some (compare_gt_iff_gt.2 p).symm
        | exact congrArg some (compare_lt_iff_lt.2 n).symm
    | finite t m' e' hm' =>
      have hc : IsCanonicalFinite m e := hu
      have hc' : IsCanonicalFinite m' e' := hv
      have p := uE_finite_pos_pos m e hm
      have n := uE_finite_neg_neg m e hm
      have p' := uE_finite_pos_pos m' e' hm'
      have n' := uE_finite_neg_neg m' e' hm'
      cases s <;> cases t <;> simp only [UnpackedFloat.compare, uE]
      all_goals first
        | exact congrArg some (compare_lt_iff_lt.2 (lt_trans n p')).symm
        | exact congrArg some (compare_gt_iff_gt.2 (lt_trans n' p)).symm
        | (rw [compare_ratE, lex_compare_mag hc hc']; rfl)
        | (rw [compare_ratE, lex_compare_mag hc hc']
           simp only [signedVal]
           exact congrArg some (compare_neg_swap _ _).symm)

theorem float_compare_spec {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (unpackBits a.toBits).compare (unpackBits b.toBits) = some (compare a.toE b.toE) :=
  ucompare_spec (uOk_of_float ha) (uOk_of_float hb)

theorem float_le_iff_toE {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a ≤ b ↔ a.toE ≤ b.toE := by
  rw [float_le_iff, UnpackedFloat.le, float_compare_spec ha hb]
  simp only [Option.any_some]
  rw [← compare_le_iff_le]
  cases compare a.toE b.toE <;> simp [Ordering.isLE]

theorem float_lt_iff_toE {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a < b ↔ a.toE < b.toE := by
  rw [Interval64Proofs.IntervalMem.float_lt_iff, UnpackedFloat.lt, float_compare_spec ha hb]
  rw [← compare_lt_iff_lt]
  cases compare a.toE b.toE <;> simp

/-! ### `loR` / `hiR` / `toSet` in `EReal` terms -/

theorem loR_toEVal (u : UnpackedFloat) (x : ℝ) :
    loR (toEVal u) x ↔ u.isNaN = false ∧ uE u ≤ (x : EReal) := by
  cases u with
  | notANumber => simp [toEVal, loR, UnpackedFloat.isNaN]
  | infinity s => cases s <;> simp [toEVal, loR, UnpackedFloat.isNaN, uE]
  | zero s => simp [toEVal, loR, UnpackedFloat.isNaN, uE]
  | finite s m e hm =>
    simp only [toEVal, loR, UnpackedFloat.isNaN, uE, true_and]
    exact_mod_cast Iff.rfl

theorem hiR_toEVal (u : UnpackedFloat) (x : ℝ) :
    hiR (toEVal u) x ↔ u.isNaN = false ∧ (x : EReal) ≤ uE u := by
  cases u with
  | notANumber => simp [toEVal, hiR, UnpackedFloat.isNaN]
  | infinity s => cases s <;> simp [toEVal, hiR, UnpackedFloat.isNaN, uE]
  | zero s => simp [toEVal, hiR, UnpackedFloat.isNaN, uE]
  | finite s m e hm =>
    simp only [toEVal, hiR, UnpackedFloat.isNaN, uE, true_and]
    exact_mod_cast Iff.rfl

theorem loR_iff_toE (f : Float) (x : ℝ) :
    loR (bitsToEVal f.toBits) x ↔ f.isNaN = false ∧ f.toE ≤ (x : EReal) := by
  rw [bitsToEVal, loR_toEVal, float_isNaN]; rfl

theorem hiR_iff_toE (f : Float) (x : ℝ) :
    hiR (bitsToEVal f.toBits) x ↔ f.isNaN = false ∧ (x : EReal) ≤ f.toE := by
  rw [bitsToEVal, hiR_toEVal, float_isNaN]; rfl

theorem mem_toSet_iff_toE {I : Interval64} {x : ℝ} :
    x ∈ I.toSet ↔ (I.lo.isNaN = false ∧ I.lo.toE ≤ (x : EReal)) ∧
      (I.hi.isNaN = false ∧ (x : EReal) ≤ I.hi.toE) := by
  rw [mem_toSet, loR_iff_toE, hiR_iff_toE]

theorem mem_toSet_of_toE {I : Interval64} {x : ℝ} (hl : I.lo.isNaN = false)
    (hh : I.hi.isNaN = false) (h1 : I.lo.toE ≤ (x : EReal)) (h2 : (x : EReal) ≤ I.hi.toE) :
    x ∈ I.toSet := mem_toSet_iff_toE.2 ⟨⟨hl, h1⟩, ⟨hh, h2⟩⟩

theorem toE_of_bitsToRat? {f : Float} {q : ℚ} (h : bitsToRat? f.toBits = some q) :
    f.toE = (((q : ℚ) : ℝ) : EReal) := by
  rcases bitsToRat?_cases h with ⟨s, hu, rfl⟩ | ⟨s, m, e, hm, hu, rfl, -⟩
  · simp [Float.toE, hu, uE]
  · simp [Float.toE, hu, uE]

theorem isNaN_false_of_bitsToRat? {f : Float} {q : ℚ} (h : bitsToRat? f.toBits = some q) :
    f.isNaN = false := not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? h)

/-- A non-NaN float with a finite extended value has a rational value. -/
theorem exists_rat_of_toE {f : Float} (hn : f.isNaN = false) (hb : f.toE ≠ ⊥)
    (ht : f.toE ≠ ⊤) : ∃ q : ℚ, bitsToRat? f.toBits = some q ∧ f.toE = ((q : ℝ) : EReal) := by
  unfold Float.toE at hb ht ⊢
  rw [float_isNaN] at hn
  unfold bitsToRat?
  cases hu : unpackBits f.toBits with
  | notANumber => rw [hu] at hn; simp [UnpackedFloat.isNaN] at hn
  | infinity s => cases s <;> simp [hu, uE] at hb ht
  | zero s => exact ⟨0, by simp [toRat?], by simp [uE]⟩
  | finite s m e hm =>
    refine ⟨signedVal s m e, ?_, by simp [uE]⟩
    cases s <;> rfl

theorem toE_ne_top_of_loR {f : Float} {x : ℝ} (h : loR (bitsToEVal f.toBits) x) : f.toE ≠ ⊤ := by
  rw [loR_iff_toE] at h
  intro ht; rw [ht] at h; exact absurd h.2 (by simp)

theorem toE_ne_bot_of_hiR {f : Float} {x : ℝ} (h : hiR (bitsToEVal f.toBits) x) : f.toE ≠ ⊥ := by
  rw [hiR_iff_toE] at h
  intro ht; rw [ht] at h; exact absurd h.2 (by simp)

/-! ### Constants -/

theorem unpack_zero_float : unpackBits (0 : Float).toBits = .zero .positive := by rfl
theorem unpack_one_float : unpackBits (1 : Float).toBits = .finite .positive (2 ^ 52) (-52) (by decide) := by
  rfl
theorem unpack_inf_float : unpackBits Float.inf.toBits = .infinity .positive := by rfl
theorem unpack_neginf_float : unpackBits (-Float.inf).toBits = .infinity .negative := by rfl

@[simp] theorem toE_zero : (0 : Float).toE = 0 := by simp [Float.toE, unpack_zero_float, uE]
@[simp] theorem isNaN_zero : (0 : Float).isNaN = false := by
  rw [float_isNaN, unpack_zero_float]; rfl
@[simp] theorem toE_one : (1 : Float).toE = 1 := by
  simp only [Float.toE, unpack_one_float, uE]
  have : signedVal .positive (2 ^ 52) (-52) = 1 := by decide +kernel
  rw [this]; simp
@[simp] theorem isNaN_one : (1 : Float).isNaN = false := by
  rw [float_isNaN, unpack_one_float]; rfl
@[simp] theorem toE_inf : Float.inf.toE = ⊤ := by simp [Float.toE, unpack_inf_float, uE]
@[simp] theorem isNaN_inf : Float.inf.isNaN = false := by
  rw [float_isNaN, unpack_inf_float]; rfl
@[simp] theorem toE_neginf : (-Float.inf).toE = ⊥ := by simp [Float.toE, unpack_neginf_float, uE]
@[simp] theorem isNaN_neginf : (-Float.inf).isNaN = false := by
  rw [float_isNaN, unpack_neginf_float]; rfl

/-! ### Comparisons, `fmin` / `fmax` -/

theorem zero_le_iff_toE {f : Float} (hf : f.isNaN = false) : (0 : Float) ≤ f ↔ 0 ≤ f.toE := by
  rw [float_le_iff_toE isNaN_zero hf, toE_zero]

theorem le_zero_iff_toE {f : Float} (hf : f.isNaN = false) : f ≤ (0 : Float) ↔ f.toE ≤ 0 := by
  rw [float_le_iff_toE hf isNaN_zero, toE_zero]

theorem zero_lt_iff_toE {f : Float} (hf : f.isNaN = false) : (0 : Float) < f ↔ 0 < f.toE := by
  rw [float_lt_iff_toE isNaN_zero hf, toE_zero]

theorem lt_zero_iff_toE {f : Float} (hf : f.isNaN = false) : f < (0 : Float) ↔ f.toE < 0 := by
  rw [float_lt_iff_toE hf isNaN_zero, toE_zero]

theorem fmin_isNaN {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (fmin a b).isNaN = false := by
  unfold fmin; split <;> assumption

theorem fmax_isNaN {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (fmax a b).isNaN = false := by
  unfold fmax; split <;> assumption

theorem toE_fmin {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (fmin a b).toE = min a.toE b.toE := by
  unfold fmin
  by_cases h : a < b
  · simp only [h, decide_true, ↓reduceIte]
    exact (min_eq_left ((float_lt_iff_toE ha hb).1 h).le).symm
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (min_eq_right (not_lt.1 (fun h' => h ((float_lt_iff_toE ha hb).2 h')))).symm

theorem toE_fmax {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    (fmax a b).toE = max a.toE b.toE := by
  unfold fmax
  by_cases h : b < a
  · simp only [h, decide_true, ↓reduceIte]
    exact (max_eq_left ((float_lt_iff_toE hb ha).1 h).le).symm
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (not_lt.1 (fun h' => h ((float_lt_iff_toE hb ha).2 h')))).symm

/-! ### `isInf`, `== 0` -/

theorem isInf_iff_toE {f : Float} : f.isInf = true ↔ (f.toE = ⊤ ∨ f.toE = ⊥) ∧ f.isNaN = false := by
  rw [Interval64Proofs.IntervalMem.float_isInf, float_isNaN]
  unfold Float.toE
  cases unpackBits f.toBits with
  | notANumber => simp [UnpackedFloat.isInf, uE]
  | infinity s => cases s <;> simp [UnpackedFloat.isInf, uE, UnpackedFloat.isNaN]
  | zero s => simp [UnpackedFloat.isInf, uE]
  | finite s m e hm =>
    simp only [UnpackedFloat.isInf, uE, Bool.false_eq_true, false_iff, not_and]
    intro h; rcases h with h | h <;> simp at h

theorem beq_zero_iff_toE {f : Float} (hf : f.isNaN = false) : (f == 0) = true ↔ f.toE = 0 := by
  show ((unpackBits f.toBits).compare (unpackBits (0 : Float).toBits) == some .eq) = true ↔ _
  rw [float_compare_spec hf isNaN_zero, toE_zero]
  simp only [beq_iff_eq, Option.some.injEq]
  exact compare_eq_iff_eq

/-! ### Directed scalar operations on extended values -/

theorem bitsToRat?_of_unpack_zero {f : Float} {s : Sign} (h : unpackBits f.toBits = .zero s) :
    bitsToRat? f.toBits = some 0 := by
  unfold bitsToRat?; rw [h]; rfl

theorem bitsToRat?_of_unpack_finite {f : Float} {s : Sign} {m : Nat} {e : Int} {hm : 0 < m}
    (h : unpackBits f.toBits = .finite s m e hm) :
    bitsToRat? f.toBits = some (signedVal s m e) := by
  unfold bitsToRat?; rw [h]; cases s <;> rfl

theorem toE_le_of_loEnc {f : Float} {q : ℚ} (h : loEncloses? (bitsToEVal f.toBits) q) :
    f.isNaN = false ∧ f.toE ≤ (((q : ℚ) : ℝ) : EReal) :=
  (loR_iff_toE f q).1 ((loR_cast _ q).2 h)

theorem toE_ge_of_hiEnc {f : Float} {q : ℚ} (h : hiEncloses? (bitsToEVal f.toBits) q) :
    f.isNaN = false ∧ (((q : ℚ) : ℝ) : EReal) ≤ f.toE :=
  (hiR_iff_toE f q).1 ((hiR_cast _ q).2 h)

theorem toE_rat_mul (qa qb : ℚ) :
    (((qa * qb : ℚ) : ℝ) : EReal) = ((qa : ℝ) : EReal) * ((qb : ℝ) : EReal) := by
  rw [Rat.cast_mul, EReal.coe_mul]

theorem toE_rat_div (qa qb : ℚ) :
    (((qa / qb : ℚ) : ℝ) : EReal) = ((qa : ℝ) : EReal) / ((qb : ℝ) : EReal) := by
  rw [Rat.cast_div, EReal.coe_div]

theorem unpack_mulDown_of_mulU {a b : Float} {t : Sign}
    (h : mulU (unpackBits a.toBits) (unpackBits b.toBits) false = .infinity t) :
    unpackBits (Directed.mulDown a b).toBits = .infinity t := by
  rw [mulDown_toBits]
  simp only [Spec.mulDown, Spec.mul, h, packDirected_inf, unpackBits_inf]

theorem unpack_mulUp_of_mulU {a b : Float} {t : Sign}
    (h : mulU (unpackBits a.toBits) (unpackBits b.toBits) true = .infinity t) :
    unpackBits (Directed.mulUp a b).toBits = .infinity t := by
  rw [mulUp_toBits]
  simp only [Spec.mulUp, Spec.mul, h, packDirected_inf, unpackBits_inf]

theorem unpack_divDown_of_divU {a b : Float} {u : UnpackedFloat}
    (hu : u = .infinity .positive ∨ u = .infinity .negative ∨ u = .zero .positive ∨ u = .zero .negative)
    (h : divU (unpackBits a.toBits) (unpackBits b.toBits) false = u) :
    unpackBits (Directed.divDown a b).toBits = u := by
  rw [divDown_toBits]
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp only [Spec.divDown, Spec.div, h, packDirected_inf, packDirected_zero, unpackBits_inf,
      unpackBits_zero]

theorem unpack_divUp_of_divU {a b : Float} {u : UnpackedFloat}
    (hu : u = .infinity .positive ∨ u = .infinity .negative ∨ u = .zero .positive ∨ u = .zero .negative)
    (h : divU (unpackBits a.toBits) (unpackBits b.toBits) true = u) :
    unpackBits (Directed.divUp a b).toBits = u := by
  rw [divUp_toBits]
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp only [Spec.divUp, Spec.div, h, packDirected_inf, packDirected_zero, unpackBits_inf,
      unpackBits_zero]

/-- `0 · ∞` pattern (in either order), on extended values. -/
def SkipMul (a b : EReal) : Prop := (a = 0 ∧ (b = ⊤ ∨ b = ⊥)) ∨ (b = 0 ∧ (a = ⊤ ∨ a = ⊥))

theorem toE_finite_pos {f : Float} {m : Nat} {e : Int} {hm : 0 < m}
    (h : unpackBits f.toBits = .finite .positive m e hm) : 0 < f.toE := by
  simp only [Float.toE, h, uE]; exact uE_finite_pos_pos m e hm

theorem toE_finite_neg {f : Float} {m : Nat} {e : Int} {hm : 0 < m}
    (h : unpackBits f.toBits = .finite .negative m e hm) : f.toE < 0 := by
  simp only [Float.toE, h, uE]; exact uE_finite_neg_neg m e hm

theorem toE_finite_coe {f : Float} {s : Sign} {m : Nat} {e : Int} {hm : 0 < m}
    (h : unpackBits f.toBits = .finite s m e hm) : f.toE = ((signedVal s m e : ℝ) : EReal) := by
  simp only [Float.toE, h, uE]

theorem uE_inf_mul_fin (s t : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    uE (.infinity (s * t)) = uE (.infinity s) * uE (.finite t m e hm) := by
  have hp := uE_finite_pos_pos m e hm
  have hn := uE_finite_neg_neg m e hm
  cases s <;> cases t <;> simp only [uE] at hp hn ⊢
  · exact (EReal.bot_mul_coe_of_neg (by exact_mod_cast hn)).symm
  · exact (EReal.bot_mul_coe_of_pos (by exact_mod_cast hp)).symm
  · exact (EReal.top_mul_coe_of_neg (by exact_mod_cast hn)).symm
  · exact (EReal.top_mul_coe_of_pos (by exact_mod_cast hp)).symm

theorem uE_fin_mul_inf (s t : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    uE (.infinity (s * t)) = uE (.finite s m e hm) * uE (.infinity t) := by
  have hp := uE_finite_pos_pos m e hm
  have hn := uE_finite_neg_neg m e hm
  cases s <;> cases t <;> simp only [uE] at hp hn ⊢
  · exact (EReal.coe_mul_bot_of_neg (by exact_mod_cast hn)).symm
  · exact (EReal.coe_mul_top_of_neg (by exact_mod_cast hn)).symm
  · exact (EReal.coe_mul_bot_of_pos (by exact_mod_cast hp)).symm
  · exact (EReal.coe_mul_top_of_pos (by exact_mod_cast hp)).symm

theorem uE_inf_mul_inf (s t : Sign) :
    uE (.infinity (s * t)) = uE (.infinity s) * uE (.infinity t) := by
  cases s <;> cases t <;> rfl

/-- Directed multiplication of two non-NaN values that are not a `0 · ∞` pair:
    the result is not NaN and brackets the extended-real product. -/
theorem corner_mul {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hs : ¬ SkipMul a.toE b.toE) :
    ((Directed.mulDown a b).isNaN = false ∧ (Directed.mulDown a b).toE ≤ a.toE * b.toE) ∧
    ((Directed.mulUp a b).isNaN = false ∧ a.toE * b.toE ≤ (Directed.mulUp a b).toE) := by
  have hrat : ∀ qa qb : ℚ, bitsToRat? a.toBits = some qa → bitsToRat? b.toBits = some qb →
      ((Directed.mulDown a b).isNaN = false ∧ (Directed.mulDown a b).toE ≤ a.toE * b.toE) ∧
      ((Directed.mulUp a b).isNaN = false ∧ a.toE * b.toE ≤ (Directed.mulUp a b).toE) := by
    intro qa qb hqa hqb
    have h1 := toE_le_of_loEnc (Interval64Proofs.IntervalMem.loEncloses_mulDown hqa hqb)
    have h2 := toE_ge_of_hiEnc (Interval64Proofs.IntervalMem.hiEncloses_mulUp hqa hqb)
    rw [toE_of_bitsToRat? hqa, toE_of_bitsToRat? hqb, ← toE_rat_mul]
    exact ⟨h1, h2⟩
  have hinf : ∀ t : Sign, mulU (unpackBits a.toBits) (unpackBits b.toBits) false = .infinity t →
      mulU (unpackBits a.toBits) (unpackBits b.toBits) true = .infinity t →
      uE (.infinity t) = a.toE * b.toE →
      ((Directed.mulDown a b).isNaN = false ∧ (Directed.mulDown a b).toE ≤ a.toE * b.toE) ∧
      ((Directed.mulUp a b).isNaN = false ∧ a.toE * b.toE ≤ (Directed.mulUp a b).toE) := by
    intro t h1 h2 he
    have e1 := unpack_mulDown_of_mulU h1
    have e2 := unpack_mulUp_of_mulU h2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [float_isNaN, e1]; rfl
    · show uE (unpackBits (Directed.mulDown a b).toBits) ≤ _
      rw [e1, he]
    · rw [float_isNaN, e2]; rfl
    · show _ ≤ uE (unpackBits (Directed.mulUp a b).toBits)
      rw [e2, he]
  have hA : a.toE = uE (unpackBits a.toBits) := rfl
  have hB : b.toE = uE (unpackBits b.toBits) := rfl
  cases hua : unpackBits a.toBits with
  | notANumber => rw [float_isNaN, hua] at ha; simp [UnpackedFloat.isNaN] at ha
  | infinity sa =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      exact hinf (sa * sb) (by simp [mulU, hua, hub]) (by simp [mulU, hua, hub])
        (by rw [hA, hB, hua, hub]; exact uE_inf_mul_inf sa sb)
    | zero sb =>
      exfalso; apply hs; right
      rw [hA, hB, hua, hub]
      cases sa <;> simp [uE]
    | finite sb mb eb hmb =>
      exact hinf (sa * sb) (by simp [mulU, hua, hub]) (by simp [mulU, hua, hub])
        (by rw [hA, hB, hua, hub]; exact uE_inf_mul_fin sa sb mb eb hmb)
  | zero sa =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      exfalso; apply hs; left
      rw [hA, hB, hua, hub]
      cases sb <;> simp [uE]
    | zero sb => exact hrat 0 0 (bitsToRat?_of_unpack_zero hua) (bitsToRat?_of_unpack_zero hub)
    | finite sb mb eb hmb =>
      exact hrat _ _ (bitsToRat?_of_unpack_zero hua) (bitsToRat?_of_unpack_finite hub)
  | finite sa ma ea hma =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      exact hinf (sa * sb) (by simp [mulU, hua, hub]) (by simp [mulU, hua, hub])
        (by rw [hA, hB, hua, hub]; exact uE_fin_mul_inf sa sb ma ea hma)
    | zero sb => exact hrat _ _ (bitsToRat?_of_unpack_finite hua) (bitsToRat?_of_unpack_zero hub)
    | finite sb mb eb hmb =>
      exact hrat _ _ (bitsToRat?_of_unpack_finite hua) (bitsToRat?_of_unpack_finite hub)

theorem uE_inf_div_fin (s t : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    uE (.infinity (s / t)) = uE (.infinity s) / uE (.finite t m e hm) := by
  have hp := uE_finite_pos_pos m e hm
  have hn := uE_finite_neg_neg m e hm
  cases s <;> cases t <;> simp only [uE] at hp hn ⊢
  · exact (EReal.bot_div_of_neg_ne_bot hn (EReal.coe_ne_bot _)).symm
  · exact (EReal.bot_div_of_pos_ne_top hp (EReal.coe_ne_top _)).symm
  · exact (EReal.top_div_of_neg_ne_bot hn (EReal.coe_ne_bot _)).symm
  · exact (EReal.top_div_of_pos_ne_top hp (EReal.coe_ne_top _)).symm

/-- Directed division of non-NaN values with a nonzero divisor, not `±∞ / ±∞`:
    the result is not NaN and brackets the extended-real quotient. -/
theorem corner_div {a b : Float} (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hb0 : b.toE ≠ 0) (hs : ¬ ((a.toE = ⊤ ∨ a.toE = ⊥) ∧ (b.toE = ⊤ ∨ b.toE = ⊥))) :
    ((Directed.divDown a b).isNaN = false ∧ (Directed.divDown a b).toE ≤ a.toE / b.toE) ∧
    ((Directed.divUp a b).isNaN = false ∧ a.toE / b.toE ≤ (Directed.divUp a b).toE) := by
  have hrat : ∀ qa qb : ℚ, bitsToRat? a.toBits = some qa → bitsToRat? b.toBits = some qb →
      ((Directed.divDown a b).isNaN = false ∧ (Directed.divDown a b).toE ≤ a.toE / b.toE) ∧
      ((Directed.divUp a b).isNaN = false ∧ a.toE / b.toE ≤ (Directed.divUp a b).toE) := by
    intro qa qb hqa hqb
    have hqb0 : qb ≠ 0 := by
      intro h; apply hb0; rw [toE_of_bitsToRat? hqb, h]; simp
    have h1 := toE_le_of_loEnc (Interval64Proofs.Div.loEncloses_divDown hqa hqb hqb0)
    have h2 := toE_ge_of_hiEnc (Interval64Proofs.Div.hiEncloses_divUp hqa hqb hqb0)
    rw [toE_of_bitsToRat? hqa, toE_of_bitsToRat? hqb, ← toE_rat_div]
    exact ⟨h1, h2⟩
  have hexact : ∀ u : UnpackedFloat,
      (u = .infinity .positive ∨ u = .infinity .negative ∨ u = .zero .positive ∨ u = .zero .negative) →
      divU (unpackBits a.toBits) (unpackBits b.toBits) false = u →
      divU (unpackBits a.toBits) (unpackBits b.toBits) true = u →
      uE u = a.toE / b.toE →
      ((Directed.divDown a b).isNaN = false ∧ (Directed.divDown a b).toE ≤ a.toE / b.toE) ∧
      ((Directed.divUp a b).isNaN = false ∧ a.toE / b.toE ≤ (Directed.divUp a b).toE) := by
    intro u hu h1 h2 he
    have e1 := unpack_divDown_of_divU hu h1
    have e2 := unpack_divUp_of_divU hu h2
    have hnan : u.isNaN = false := by rcases hu with rfl | rfl | rfl | rfl <;> rfl
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [float_isNaN, e1]; exact hnan
    · show uE (unpackBits (Directed.divDown a b).toBits) ≤ _
      rw [e1, he]
    · rw [float_isNaN, e2]; exact hnan
    · show _ ≤ uE (unpackBits (Directed.divUp a b).toBits)
      rw [e2, he]
  have hA : a.toE = uE (unpackBits a.toBits) := rfl
  have hB : b.toE = uE (unpackBits b.toBits) := rfl
  have zsign : ∀ s : Sign, UnpackedFloat.zero s = .zero .positive ∨ UnpackedFloat.zero s = .zero .negative := by
    intro s; cases s <;> simp
  have isign : ∀ s : Sign, (UnpackedFloat.infinity s = .infinity .positive ∨
      UnpackedFloat.infinity s = .infinity .negative ∨ UnpackedFloat.infinity s = .zero .positive ∨
      UnpackedFloat.infinity s = .zero .negative) := by
    intro s; cases s <;> simp
  cases hua : unpackBits a.toBits with
  | notANumber => rw [float_isNaN, hua] at ha; simp [UnpackedFloat.isNaN] at ha
  | infinity sa =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      exfalso; apply hs; rw [hA, hB, hua, hub]
      cases sa <;> cases sb <;> simp [uE]
    | zero sb => exfalso; apply hb0; rw [hB, hub]; rfl
    | finite sb mb eb hmb =>
      exact hexact (.infinity (sa / sb)) (isign _) (by simp [divU, hua, hub]) (by simp [divU, hua, hub])
        (by rw [hA, hB, hua, hub]; exact uE_inf_div_fin sa sb mb eb hmb)
  | zero sa =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      refine hexact (.zero (sa / sb)) (Or.inr (Or.inr (zsign _))) (by simp [divU, hua, hub])
        (by simp [divU, hua, hub]) ?_
      rw [hA, hB, hua, hub]; cases sb <;> simp [uE, EReal.div_top, EReal.div_bot]
    | zero sb => exfalso; apply hb0; rw [hB, hub]; rfl
    | finite sb mb eb hmb =>
      exact hrat _ _ (bitsToRat?_of_unpack_zero hua) (bitsToRat?_of_unpack_finite hub)
  | finite sa ma ea hma =>
    cases hub : unpackBits b.toBits with
    | notANumber => rw [float_isNaN, hub] at hb; simp [UnpackedFloat.isNaN] at hb
    | infinity sb =>
      refine hexact (.zero (sa / sb)) (Or.inr (Or.inr (zsign _))) (by simp [divU, hua, hub])
        (by simp [divU, hua, hub]) ?_
      rw [hA, hB, hua, hub]; cases sb <;> simp [uE, EReal.div_top, EReal.div_bot]
    | zero sb => exfalso; apply hb0; rw [hB, hub]; rfl
    | finite sb mb eb hmb =>
      exact hrat _ _ (bitsToRat?_of_unpack_finite hua) (bitsToRat?_of_unpack_finite hub)

end RealFP

end
