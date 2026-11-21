/-
Real enclosures for the directed `sinh`, `cosh`, `tanh`, `log2`, `log10` of `Interval64.Hyp`.
-/
import RealFPMathlib.InvTrig
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

open Interval64 Interval64.Spec Interval64.Transc Interval64.InvTrig Interval64.Hyp
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pow2

namespace RealFP.Hyp

open RealFP.Transc RealFP.Trig RealFP.InvTrig

/-! ### Rational enclosures -/

theorem divPos_spec {n d : ℚ × ℚ} {x y : ℝ} (hn : (n.1 : ℝ) ≤ x ∧ x ≤ n.2)
    (hd : (d.1 : ℝ) ≤ y ∧ y ≤ d.2) (hd0 : (0 : ℝ) < d.1) :
    ((divPos n d).1 : ℝ) ≤ x / y ∧ x / y ≤ (divPos n d).2 := by
  have hy : 0 < y := lt_of_lt_of_le hd0 hd.1
  have hd2 : (0 : ℝ) < d.2 := lt_of_lt_of_le hy hd.2
  unfold divPos
  constructor
  · split
    · rename_i h; have h' : (0 : ℝ) ≤ n.1 := by exact_mod_cast h
      push_cast
      calc (n.1 : ℝ) / d.2 ≤ n.1 / y := div_le_div_of_nonneg_left h' hy hd.2
        _ ≤ x / y := div_le_div_of_nonneg_right hn.1 hy.le
    · rename_i h; have h' : (n.1 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      push_cast
      calc (n.1 : ℝ) / d.1 ≤ n.1 / y := by
            rw [div_le_div_iff₀ hd0 hy]; nlinarith [hd.1]
        _ ≤ x / y := div_le_div_of_nonneg_right hn.1 hy.le
  · by_cases h : 0 ≤ n.2
    · have h' : (0 : ℝ) ≤ n.2 := by exact_mod_cast h
      simp only [h, if_true]; push_cast
      calc x / y ≤ n.2 / y := div_le_div_of_nonneg_right hn.2 hy.le
        _ ≤ n.2 / d.1 := div_le_div_of_nonneg_left h' hd0 hd.1
    · have h' : (n.2 : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
      simp only [h, if_false]; push_cast
      calc x / y ≤ n.2 / y := div_le_div_of_nonneg_right hn.2 hy.le
        _ ≤ n.2 / d.2 := by rw [div_le_div_iff₀ hy hd2]; nlinarith [hd.2]

theorem sinhBounds_spec (q : ℚ) (p : ℕ) :
    ((sinhBounds q p).1 : ℝ) ≤ Real.sinh q ∧ Real.sinh q ≤ (sinhBounds q p).2 := by
  unfold sinhBounds; dsimp only
  obtain ⟨a, b⟩ := expBounds_spec q p
  obtain ⟨c, d⟩ := expBounds_spec (-q) p
  rw [Real.sinh_eq]; push_cast at *
  constructor <;> linarith

theorem coshBounds_spec (q : ℚ) (p : ℕ) :
    ((coshBounds q p).1 : ℝ) ≤ Real.cosh q ∧ Real.cosh q ≤ (coshBounds q p).2 := by
  unfold coshBounds; dsimp only
  obtain ⟨a, b⟩ := expBounds_spec q p
  obtain ⟨c, d⟩ := expBounds_spec (-q) p
  rw [Real.cosh_eq]; push_cast at *
  constructor <;> linarith

theorem tanhBounds_spec (q : ℚ) (p : ℕ) :
    ((tanhBounds q p).1 : ℝ) ≤ Real.tanh q ∧ Real.tanh q ≤ (tanhBounds q p).2 := by
  unfold tanhBounds; dsimp only
  rw [Real.tanh_eq_sinh_div_cosh]
  obtain ⟨c1, c2⟩ := coshBounds_spec q p
  refine divPos_spec (sinhBounds_spec q p) ⟨?_, c2⟩ (by push_cast; exact lt_of_lt_of_le one_pos (le_max_right _ _))
  push_cast
  exact max_le c1 (Real.one_le_cosh _)

theorem log2Exact?_spec {q : ℚ} {k : ℤ} (h : log2Exact? q = some k) : (q : ℝ) = (2 : ℝ) ^ k := by
  unfold log2Exact? at h
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      have h2' : q.den = 2 ^ Nat.log2 q.den := by simpa using h2
      rw [hq, h1]; push_cast
      rw [show (q.den : ℝ) = 2 ^ (Nat.log2 q.den) by exact_mod_cast h2']
      rw [zpow_neg, zpow_natCast, one_div]
    · cases h
  · split at h
    · rename_i _ h1
      split at h
      · rename_i h2
        cases h
        have h2' : q.num.toNat = 2 ^ Nat.log2 q.num.toNat := by simpa using h2
        have hn : (q.num : ℝ) = ((q.num.toNat : ℕ) : ℝ) := by
          have := Int.toNat_of_nonneg h1.2.le; exact_mod_cast this.symm
        rw [hq, h1.1, hn, show ((q.num.toNat : ℕ) : ℝ) = 2 ^ (Nat.log2 q.num.toNat) by
          exact_mod_cast h2']
        push_cast; rw [zpow_natCast]; simp
      · cases h
    · cases h

theorem log10Exact?_spec {q : ℚ} {k : ℕ} (h : log10Exact? q = some k) : (q : ℝ) = (10 : ℝ) ^ k := by
  unfold log10Exact? at h
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  rw [this]; push_cast; rfl

theorem two_lt_log_ten : (2 : ℝ) < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos 1]

theorem log2Bounds_spec {q : ℚ} (hq : 0 < q) (p : ℕ) :
    ((log2Bounds q p).1 : ℝ) ≤ Real.logb 2 q ∧ Real.logb 2 q ≤ (log2Bounds q p).2 := by
  unfold log2Bounds
  split
  · rename_i k hk
    rw [log2Exact?_spec hk, ← Real.log_div_log, Real.log_zpow]
    have : Real.log 2 ≠ 0 := by positivity
    push_cast; field_simp; exact ⟨le_rfl, le_rfl⟩
  · rw [← Real.log_div_log]
    obtain ⟨l1, l2⟩ := ln2Bounds_spec p
    have h2 := Real.log_two_gt_d9
    refine divPos_spec (logBounds_spec hq p) ⟨?_, l2⟩ (by push_cast; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    push_cast; exact max_le l1 (by linarith)

theorem log10Bounds_spec {q : ℚ} (hq : 0 < q) (p : ℕ) :
    ((log10Bounds q p).1 : ℝ) ≤ Real.logb 10 q ∧ Real.logb 10 q ≤ (log10Bounds q p).2 := by
  unfold log10Bounds
  split
  · rename_i k hk
    rw [log10Exact?_spec hk, Real.logb_pow]
    simp [Real.logb_self_eq_one]
  · rw [← Real.log_div_log]
    obtain ⟨l1, l2⟩ := logBounds_spec (q := 10) (by norm_num) p
    have h2 := two_lt_log_ten
    refine divPos_spec (logBounds_spec hq p) ⟨?_, ?_⟩ (by push_cast; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    · push_cast; exact max_le (by simpa [ln10Bounds] using l1) h2.le
    · simpa [ln10Bounds] using l2

/-! ### Overflow and saturation lemmas -/

theorem ovf_le_sinh {q : ℝ} (hq : 711 < q) : (expOvfBound : ℝ) ≤ Real.sinh q := by
  have hB := expOvfBound_le_exp (q := q - 1) (by linarith)
  have hB0 : (0 : ℝ) ≤ expOvfBound := by unfold expOvfBound; positivity
  have he : Real.exp q = Real.exp (q - 1) * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp (-q) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : (2 : ℝ) ≤ expOvfBound := by
    unfold expOvfBound; push_cast
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 1024 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h4 : (expOvfBound : ℝ) * 2.7 ≤ Real.exp (q - 1) * Real.exp 1 :=
    mul_le_mul hB (by linarith) (by norm_num) (Real.exp_pos _).le
  rw [Real.sinh_eq, he]; linarith

theorem sinh_le_neg_ovf {q : ℝ} (hq : q < -711) : Real.sinh q ≤ ((-expOvfBound : ℚ) : ℝ) := by
  have := ovf_le_sinh (q := -q) (by linarith)
  rw [Real.sinh_neg] at this; push_cast; linarith

theorem ovf_le_cosh {q : ℝ} (hq : 711 < |q|) : (expOvfBound : ℝ) ≤ Real.cosh q := by
  rw [← Real.cosh_abs]
  exact (ovf_le_sinh hq).trans (Real.sinh_lt_cosh _).le

theorem tanh_ge_of_ge {q : ℝ} (hq : 22 ≤ q) : 1 - 1 / 2 ^ 60 ≤ Real.tanh q := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  set a := Real.exp q
  have ha : 0 < a := Real.exp_pos q
  have hb : Real.exp (-q) = a⁻¹ := Real.exp_neg q
  rw [hb]
  have hsq : (2 : ℝ) ^ 61 ≤ a * a := by
    rw [← Real.exp_add, show ((2 : ℝ) ^ 61) = 2 ^ (61 : ℕ) by norm_num, two_pow_eq_exp,
      Real.exp_le_exp]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hden : 0 < (a + a⁻¹) / 2 := by positivity
  rw [le_div_iff₀ hden]
  have : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  nlinarith

theorem tanh_le_of_le {q : ℝ} (hq : q ≤ -22) : Real.tanh q ≤ -1 + 1 / 2 ^ 60 := by
  have := tanh_ge_of_ge (q := -q) (by linarith)
  rw [Real.tanh_neg] at this; linarith

theorem tanh_mono {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  have key : ∀ t : ℝ, Real.tanh t = 1 - 2 / (Real.exp (2 * t) + 1) := by
    intro t
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [← Real.exp_add]; ring_nf
    have hn : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    rw [he, hn]
    have := Real.exp_pos t
    field_simp; ring
  rw [key, key]
  have h1 : Real.exp (2 * x) ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith)
  have h2 := Real.exp_pos (2 * x)
  have : 2 / (Real.exp (2 * y) + 1) ≤ 2 / (Real.exp (2 * x) + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

/-! ### Rational inputs -/

attribute [local irreducible] expOvfBound ofRatDown ofRatUp

theorem sinhRat_down (q : ℚ) : loR (bitsToEVal (sinhRat q false).1) (Real.sinh q) := by
  unfold sinhRat hypOvf
  by_cases h1 : (711 : ℚ) < q
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]
    exact ofRatDown_loR (ovf_le_sinh (by exact_mod_cast h1))
  · by_cases h2 : q < -711
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]; rw [bitsToEVal_negInf]; trivial
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact rndD_down_loR (fun p => (sinhBounds_spec q p).1)

theorem sinhRat_up (q : ℚ) : hiR (bitsToEVal (sinhRat q true).1) (Real.sinh q) := by
  unfold sinhRat hypOvf
  by_cases h1 : (711 : ℚ) < q
  · simp only [h1, ↓reduceIte]; rw [bitsToEVal_posInf]; trivial
  · by_cases h2 : q < -711
    · simp only [h1, h2, ↓reduceIte]
      exact ofRatUp_hiR (sinh_le_neg_ovf (by exact_mod_cast h2))
    · simp only [h1, h2, ↓reduceIte]
      exact rndD_up_hiR (fun p => (sinhBounds_spec q p).2)

theorem coshRat_down (q : ℚ) : loR (bitsToEVal (coshRat q false).1) (Real.cosh q) := by
  unfold coshRat hypOvf
  by_cases h1 : (711 : ℚ) < ratAbs' q
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]
    refine ofRatDown_loR (ovf_le_cosh ?_)
    have : ((ratAbs' q : ℚ) : ℝ) = |(q : ℝ)| := by
      unfold ratAbs'; split <;> push_cast
      · rename_i h; rw [abs_of_neg (by exact_mod_cast h)]
      · rename_i h; rw [abs_of_nonneg (by exact_mod_cast (not_lt.1 h))]
    rw [← this]; exact_mod_cast h1
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]
    exact rndD_down_loR (fun p => (coshBounds_spec q p).1)

theorem coshRat_up (q : ℚ) : hiR (bitsToEVal (coshRat q true).1) (Real.cosh q) := by
  unfold coshRat hypOvf
  by_cases h1 : (711 : ℚ) < ratAbs' q
  · simp only [h1, ↓reduceIte]; rw [bitsToEVal_posInf]; trivial
  · simp only [h1, ↓reduceIte]
    exact rndD_up_hiR (fun p => (coshBounds_spec q p).2)

theorem tanhRat_down (q : ℚ) : loR (bitsToEVal (tanhRat q false).1) (Real.tanh q) := by
  unfold tanhRat
  by_cases h1 : (22 : ℚ) ≤ q
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]
    exact ofRatDown_loR (by push_cast; exact tanh_ge_of_ge (by exact_mod_cast h1))
  · by_cases h2 : q ≤ -22
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact ofRatDown_loR (by push_cast; exact (Real.neg_one_lt_tanh _).le)
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact rndD_down_loR (fun p => (tanhBounds_spec q p).1)

theorem tanhRat_up (q : ℚ) : hiR (bitsToEVal (tanhRat q true).1) (Real.tanh q) := by
  unfold tanhRat
  by_cases h1 : (22 : ℚ) ≤ q
  · simp only [h1, ↓reduceIte]
    exact ofRatUp_hiR (by push_cast; exact (Real.tanh_lt_one _).le)
  · by_cases h2 : q ≤ -22
    · simp only [h1, h2, ↓reduceIte]
      exact ofRatUp_hiR (by push_cast; exact tanh_le_of_le (by exact_mod_cast h2))
    · simp only [h1, h2, ↓reduceIte]
      exact rndD_up_hiR (fun p => (tanhBounds_spec q p).2)

/-! ### Bit-level and `Float` directed results -/

theorem sinhDownBits_loR {b : UInt64} {x : ℝ} (h : loR (bitsToEVal b) x) :
    loR (bitsToEVal (sinhDownBits b)) (Real.sinh x) := by
  unfold sinhDownBits sinhBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, loR]
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s =>
    have h0 : (0 : ℝ) ≤ x := by simpa [bitsToEVal, hu, toEVal, loR] using h
    simpa [bitsToEVal, hu, toEVal, loR] using Real.sinh_nonneg_iff.2 h0
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (sinhRat_down _) (Real.sinh_le_sinh.2 hq)

theorem sinhUpBits_hiR {b : UInt64} {x : ℝ} (h : hiR (bitsToEVal b) x) :
    hiR (bitsToEVal (sinhUpBits b)) (Real.sinh x) := by
  unfold sinhUpBits sinhBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => simp [bitsToEVal, hu, toEVal, hiR]
  | zero s =>
    have h0 : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    simpa [bitsToEVal, hu, toEVal, hiR] using Real.sinh_nonpos_iff.2 h0
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (sinhRat_up _) (Real.sinh_le_sinh.2 hq)

theorem tanhDownBits_loR {b : UInt64} {x : ℝ} (h : loR (bitsToEVal b) x) :
    loR (bitsToEVal (tanhDownBits b)) (Real.tanh x) := by
  unfold tanhDownBits tanhBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative =>
      exact ofRatDown_loR (by push_cast; exact (Real.neg_one_lt_tanh _).le)
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s =>
    have h0 : (0 : ℝ) ≤ x := by simpa [bitsToEVal, hu, toEVal, loR] using h
    have := tanh_mono h0; rw [Real.tanh_zero] at this
    simpa [bitsToEVal, hu, toEVal, loR] using this
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (tanhRat_down _) (tanh_mono hq)

theorem tanhUpBits_hiR {b : UInt64} {x : ℝ} (h : hiR (bitsToEVal b) x) :
    hiR (bitsToEVal (tanhUpBits b)) (Real.tanh x) := by
  unfold tanhUpBits tanhBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => exact ofRatUp_hiR (by push_cast; exact (Real.tanh_lt_one _).le)
  | zero s =>
    have h0 : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    have := tanh_mono h0; rw [Real.tanh_zero] at this
    simpa [bitsToEVal, hu, toEVal, hiR] using this
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (tanhRat_up _) (tanh_mono hq)

theorem sinhDown_loR {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Directed.sinhDown a).toBits) (Real.sinh x) := loR_ofBits (sinhDownBits_loR h)
theorem sinhUp_hiR {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) :
    hiR (bitsToEVal (Directed.sinhUp a).toBits) (Real.sinh x) := hiR_ofBits (sinhUpBits_hiR h)
theorem tanhDown_loR {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Directed.tanhDown a).toBits) (Real.tanh x) := loR_ofBits (tanhDownBits_loR h)
theorem tanhUp_hiR {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) :
    hiR (bitsToEVal (Directed.tanhUp a).toBits) (Real.tanh x) := hiR_ofBits (tanhUpBits_hiR h)

/-- `sinh` interval enclosure. -/
theorem sinh_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.sinh x ∈ (Interval64.sinh X).toSet := by
  unfold Interval64.sinh
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨sinhDown_loR hx.1, sinhUp_hiR hx.2⟩

/-- `tanh` interval enclosure. -/
theorem tanh_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.tanh x ∈ (Interval64.tanh X).toSet := by
  unfold Interval64.tanh
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨tanhDown_loR hx.1, tanhUp_hiR hx.2⟩

/-! ### `cosh` (even) -/

theorem cosh_le_of_abs {x y : ℝ} (h : |x| ≤ |y|) : Real.cosh x ≤ Real.cosh y := Real.cosh_le_cosh.2 h

theorem coshDown_loR_nonneg {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x)
    (h0 : 0 ≤ a.toE) : loR (bitsToEVal (Directed.coshDown a).toBits) (Real.cosh x) := by
  apply loR_ofBits
  unfold coshDownBits coshBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative => simp [Float.toE, hu, uE] at h0
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s => exact ofRatDown_loR (by push_cast; exact Real.one_le_cosh x)
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    have hq0 : (0 : ℝ) ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [toE_finite_coe hu] at h0; exact_mod_cast h0
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (coshRat_down _) (cosh_le_of_abs (by
      rw [abs_of_nonneg hq0, abs_of_nonneg (hq0.trans hq)]; exact hq))

theorem coshUp_hiR_nonneg {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x)
    (h0 : 0 ≤ x) : hiR (bitsToEVal (Directed.coshUp a).toBits) (Real.cosh x) := by
  apply hiR_ofBits
  unfold coshUpBits coshBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => rw [bitsToEVal_posInf]; trivial
  | zero s =>
    have : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    have hx : x = 0 := le_antisymm this h0
    exact ofRatUp_hiR (by rw [hx]; simp)
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (coshRat_up _) (cosh_le_of_abs (by
      rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans hq)]; exact hq))

theorem coshDown_loR_nonpos {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x)
    (h0 : a.toE ≤ 0) : loR (bitsToEVal (Directed.coshDown a).toBits) (Real.cosh x) := by
  apply loR_ofBits
  unfold coshDownBits coshBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => simp [Float.toE, hu, uE] at h0
  | zero s => exact ofRatDown_loR (by push_cast; exact Real.one_le_cosh x)
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    have hq0 : ((signedVal s m e : ℚ) : ℝ) ≤ 0 := by
      rw [toE_finite_coe hu] at h0; exact_mod_cast h0
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (coshRat_down _) (cosh_le_of_abs (by
      rw [abs_of_nonpos hq0, abs_of_nonpos (hq.trans hq0)]; linarith))

theorem coshUp_hiR_nonpos {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x)
    (h0 : x ≤ 0) : hiR (bitsToEVal (Directed.coshUp a).toBits) (Real.cosh x) := by
  apply hiR_ofBits
  unfold coshUpBits coshBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative => rw [bitsToEVal_posInf]; trivial
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s =>
    have : 0 ≤ x := by simpa [bitsToEVal, hu, toEVal, loR] using h
    have hx : x = 0 := le_antisymm h0 this
    exact ofRatUp_hiR (by rw [hx]; simp)
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (coshRat_up _) (cosh_le_of_abs (by
      rw [abs_of_nonpos h0, abs_of_nonpos (hq.trans h0)]; linarith))

/-- `cosh` interval enclosure. -/
theorem cosh_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.cosh x ∈ (Interval64.cosh X).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  unfold Interval64.cosh
  simp only [hXl, hXh, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : (0 : Float) ≤ X.lo
  · simp only [h1, decide_true, ↓reduceIte]
    have h0 := (zero_le_iff_toE hXl).1 h1
    exact ⟨coshDown_loR_nonneg hx.1 h0, coshUp_hiR_nonneg hx.2 (EReal.coe_nonneg.1 (h0.trans hXl'))⟩
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hlo : X.lo.toE < 0 := lt_of_not_ge (fun h => h1 ((zero_le_iff_toE hXl).2 h))
    by_cases h2 : X.hi ≤ (0 : Float)
    · simp only [h2, decide_true, ↓reduceIte]
      have h0 := (le_zero_iff_toE hXh).1 h2
      exact ⟨coshDown_loR_nonpos hx.2 h0,
        coshUp_hiR_nonpos hx.1 (EReal.coe_nonpos.1 (hXh'.trans h0))⟩
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hhi : 0 < X.hi.toE := lt_of_not_ge (fun h => h2 ((le_zero_iff_toE hXh).2 h))
      refine ⟨ofBits_down_loR (by push_cast; exact Real.one_le_cosh x), ?_⟩
      have ha : loR (bitsToEVal X.lo.toBits) (min x 0) := (loR_iff_toE _ _).2 ⟨hXl, by
        rcases min_choice x 0 with h | h <;> rw [h]
        · exact hXl'
        · simpa using hlo.le⟩
      have hb : hiR (bitsToEVal X.hi.toBits) (max x 0) := (hiR_iff_toE _ _).2 ⟨hXh, by
        rcases max_choice x 0 with h | h <;> rw [h]
        · exact hXh'
        · simpa using hhi.le⟩
      refine hiR_fmax (coshUp_hiR_nonpos ha (min_le_right _ _))
        (coshUp_hiR_nonneg hb (le_max_right _ _)) ?_
      rcases le_total x 0 with hx0 | hx0
      · rw [min_eq_left hx0]; exact le_max_left _ _
      · rw [max_eq_left hx0]; exact le_max_right _ _

/-! ### `log2` / `log10` -/

/-- The base of `logBBitsD ten`. -/
noncomputable def baseR (ten : Bool) : ℝ := if ten then 10 else 2

theorem one_lt_baseR (ten : Bool) : 1 < baseR ten := by cases ten <;> norm_num [baseR]

theorem logBBounds_spec (ten : Bool) {q : ℚ} (hq : 0 < q) (p : ℕ) :
    (((if ten then log10Bounds q else log2Bounds q) p).1 : ℝ) ≤ Real.logb (baseR ten) q ∧
    Real.logb (baseR ten) q ≤ ((if ten then log10Bounds q else log2Bounds q) p).2 := by
  cases ten
  · simpa [baseR] using log2Bounds_spec hq p
  · simpa [baseR] using log10Bounds_spec hq p

theorem logBDown_loR (ten : Bool) {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x)
    {s : Float.Model.UnpackedFloat.Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hu : unpackBits a.toBits = .finite .positive m e hm) :
    loR (bitsToEVal (logBBitsD ten a.toBits false).1) (Real.logb (baseR ten) x) := by
  unfold logBBitsD
  rw [hu]
  simp only [bitsToRat?_of_finite hu]
  have hq : ((signedVal .positive m e : ℚ) : ℝ) ≤ x := by
    rw [bitsToEVal_of_finite hu] at h; exact h
  have hq0 := signedVal_pos (e := e) hm
  refine loR_mono (rndD_down_loR (fun p => (logBBounds_spec ten (by exact_mod_cast hq0) p).1)) ?_
  exact Real.logb_le_logb_of_le (one_lt_baseR ten) hq0 hq

/-- Lower endpoint of `log2`/`log10` intervals. -/
theorem logBLo_loR (ten : Bool) {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Interval64.logBLo ten a).toBits) (Real.logb (baseR ten) x) := by
  unfold Interval64.logBLo
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative => exact negInf_loR
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s => exact negInf_loR
  | finite s m e hm =>
    cases s with
    | negative => exact negInf_loR
    | positive =>
      have := loR_ofBits (logBDown_loR ten h (s := .positive) hu)
      cases ten
      · exact this
      · exact this

theorem logBUp_hiR (ten : Bool) {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) (hx : 0 < x) :
    hiR (bitsToEVal (logBBitsD ten a.toBits true).1) (Real.logb (baseR ten) x) := by
  unfold logBBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => show hiR (bitsToEVal posInf) _; rw [bitsToEVal_posInf]; trivial
  | zero s =>
    have : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    linarith
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    cases s with
    | negative => linarith [signedVal_neg' (e := e) hm]
    | positive =>
      simp only [bitsToRat?_of_finite hu]
      have hq0 := signedVal_pos (e := e) hm
      refine hiR_mono (rndD_up_hiR (fun p => (logBBounds_spec ten (by exact_mod_cast hq0) p).2)) ?_
      exact Real.logb_le_logb_of_le (one_lt_baseR ten) hx hq

theorem logBUpF_hiR (ten : Bool) {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) (hx : 0 < x) :
    hiR (bitsToEVal (if ten then Directed.log10Up a else Directed.log2Up a).toBits)
      (Real.logb (baseR ten) x) := by
  have := hiR_ofBits (logBUp_hiR ten h hx)
  cases ten
  · exact this
  · exact this

/-- `log2`/`log10` interval enclosure for every positive member. -/
theorem logB_mem_toSet (ten : Bool) {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 < x) :
    Real.logb (baseR ten) x ∈ (Interval64.logB ten X).toSet := by
  unfold Interval64.logB
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  have h2 := hx.2
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  cases hu : unpackBits X.hi.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h2
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h2
    | positive => exact ⟨logBLo_loR ten hx.1, posInf_hiR⟩
  | zero s =>
    have : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h2
    linarith
  | finite s m e hm =>
    cases s with
    | negative =>
      have : x ≤ ((signedVal .negative m e : ℚ) : ℝ) := by
        rw [bitsToEVal_of_finite hu] at h2; exact h2
      linarith [signedVal_neg' (e := e) hm]
    | positive => exact ⟨logBLo_loR ten hx.1, logBUpF_hiR ten h2 hx0⟩

theorem log2_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 < x) :
    Real.logb 2 x ∈ (Interval64.log2 X).toSet := by
  have := logB_mem_toSet false hx hx0
  simp only [baseR, Bool.false_eq_true, ↓reduceIte] at this; exact this

theorem log10_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 < x) :
    Real.logb 10 x ∈ (Interval64.log10 X).toSet := by
  have := logB_mem_toSet true hx hx0
  simp only [baseR, ↓reduceIte] at this; exact this

end RealFP.Hyp
