/-
Real enclosures for the directed `exp` / `log` of `Interval64.Transc`.

* `expBounds_spec`, `logBounds_spec` : the rational bounds of the Lean spec
  enclose `Real.exp q` / `Real.log q` (Taylor remainder `Real.exp_bound`,
  log series remainder `Real.abs_log_sub_add_sum_range_le`).
* `expDown_loR` … `logUp_hiR` : pointwise lifting to floats (any input, the
  extended-real reading of `loR` / `hiR`).
* `exp_mem_toSet`, `log_mem_toSet` : interval enclosure.

The Ziv loop only selects *which* precision's bound is rounded, so validity
does not depend on fuel or on convergence (`ziv_eq`).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Rat.Floor
import RealFPMathlib.Basic
import RealFPMathlib.Tight

open Interval64 Interval64.Spec Interval64.Transc
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pow2
open Finset

namespace RealFP.Transc

/-! ### Rational helpers -/

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, Nat.factorial, ih]

theorem floorP_le (q : ℚ) (p : ℕ) : floorP q p ≤ q := by
  unfold floorP
  have h : (((q * 2 ^ p).floor : ℤ) : ℚ) ≤ q * 2 ^ p := Int.floor_le (q * 2 ^ p)
  rw [div_le_iff₀ (by positivity)]
  exact h

theorem le_ceilP (q : ℚ) (p : ℕ) : q ≤ ceilP q p := by
  unfold ceilP
  linarith [floorP_le (-q) p]

theorem ratAbs'_eq (q : ℚ) : ratAbs' q = |q| := by
  unfold ratAbs'
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

theorem pow2_cast (e : ℤ) : ((pow2 e : ℚ) : ℝ) = (2 : ℝ) ^ e := by
  rw [pow2_eq_zpow]; push_cast; rfl

/-! ### exp -/

theorem expTaylor_eq (r : ℚ) (n : ℕ) :
    (expTaylor r n : ℝ) = ∑ m ∈ range n, (r : ℝ) ^ m / m.factorial := by
  induction n with
  | zero => simp [expTaylor]
  | succ n ih => rw [expTaylor, sum_range_succ, ← ih, fact_eq]; push_cast; ring

theorem expSmall_spec {r : ℚ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {n : ℕ} (hn : 0 < n) :
    ((expSmall r n).1 : ℝ) ≤ Real.exp r ∧ Real.exp r ≤ (expSmall r n).2 := by
  have h0' : (0 : ℝ) ≤ r := by exact_mod_cast h0
  have hb := Real.exp_bound (x := (r : ℝ)) (by rw [abs_of_nonneg h0']; exact_mod_cast h1) hn
  have he : (expErr r n : ℝ) = |(r : ℝ)| ^ n * (n.succ / (n.factorial * n)) := by
    rw [abs_of_nonneg h0']; simp [expErr, fact_eq]
  rw [← expTaylor_eq, ← he] at hb
  obtain ⟨hl, hh⟩ := abs_le.mp hb
  simp only [expSmall]; push_cast
  constructor <;> linarith

theorem sqIter_spec (p : ℕ) : ∀ (s : ℕ) (b : ℚ × ℚ) (x : ℝ),
    (b.1 : ℝ) ≤ Real.exp x → Real.exp x ≤ b.2 →
    ((sqIter p s b).1 : ℝ) ≤ Real.exp (2 ^ s * x) ∧ Real.exp (2 ^ s * x) ≤ (sqIter p s b).2
  | 0, b, x, h1, h2 => by simpa [sqIter] using ⟨h1, h2⟩
  | s + 1, b, x, h1, h2 => by
    simp only [sqIter]
    have hx2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]; ring_nf
    have hep := Real.exp_pos x
    have key := sqIter_spec p s
      (floorP ((if b.1 < 0 then 0 else b.1) * (if b.1 < 0 then 0 else b.1)) p,
        ceilP (b.2 * b.2) p) (2 * x) ?_ ?_
    · rwa [show (2 : ℝ) ^ (s + 1) * x = 2 ^ s * (2 * x) by ring]
    · set l : ℚ := if b.1 < 0 then 0 else b.1 with hl
      have hl0 : (0 : ℝ) ≤ l := by
        rw [hl]; split_ifs with h
        · simp
        · exact_mod_cast not_lt.mp h
      have hlx : (l : ℝ) ≤ Real.exp x := by
        rw [hl]; split_ifs with h
        · simpa using hep.le
        · exact h1
      calc ((floorP (l * l) p : ℚ) : ℝ) ≤ ((l * l : ℚ) : ℝ) := by exact_mod_cast floorP_le _ _
        _ = (l : ℝ) * l := by push_cast; ring
        _ ≤ Real.exp x * Real.exp x := mul_le_mul hlx hlx hl0 hep.le
        _ = Real.exp (2 * x) := hx2.symm
    · calc Real.exp (2 * x) = Real.exp x * Real.exp x := hx2
        _ ≤ (b.2 : ℝ) * b.2 := mul_le_mul h2 h2 hep.le (le_trans hep.le h2)
        _ = ((b.2 * b.2 : ℚ) : ℝ) := by push_cast; ring
        _ ≤ ((ceilP (b.2 * b.2) p : ℚ) : ℝ) := by exact_mod_cast le_ceilP _ _

theorem expTerms_pos (p : ℕ) : 0 < expTerms p := by unfold expTerms; omega

theorem lt_two_pow_expShift {t : ℚ} (ht : 0 ≤ t) : t < 2 ^ expShift t := by
  have hnum : (0 : ℤ) ≤ t.num := Rat.num_nonneg.mpr ht
  have h1 : t ≤ (t.num : ℚ) := by
    have hd : (1 : ℚ) ≤ t.den := by exact_mod_cast t.den_pos
    have hn : (0 : ℚ) ≤ t.num := by exact_mod_cast hnum
    calc t = (t.num : ℚ) / t.den := (Rat.num_div_den t).symm
      _ ≤ (t.num : ℚ) / 1 := div_le_div_of_nonneg_left hn one_pos hd
      _ = t.num := by simp
  have h2 : (t.num.toNat : ℚ) = t.num := by exact_mod_cast Int.toNat_of_nonneg hnum
  have h3 : t.num.toNat < 2 ^ (t.num.toNat.log2 + 1) := Nat.lt_log2_self
  have h4 : 2 ^ (t.num.toNat.log2 + 1) ≤ 2 ^ expShift t :=
    Nat.pow_le_pow_right (by norm_num) (by unfold expShift; omega)
  have h5 : ((t.num.toNat : ℕ) : ℚ) < ((2 ^ expShift t : ℕ) : ℚ) := by exact_mod_cast lt_of_lt_of_le h3 h4
  push_cast at h5
  linarith

theorem expPosBounds_spec {t : ℚ} (ht : 0 ≤ t) (p : ℕ) :
    ((expPosBounds t p).1 : ℝ) ≤ Real.exp t ∧ Real.exp t ≤ (expPosBounds t p).2 := by
  unfold expPosBounds
  split_ifs with hsmall
  · refine expSmall_spec ht ?_ (expTerms_pos p)
    have : (1 : ℚ) / 2 ^ 20 ≤ 1 := by norm_num
    linarith
  · have hpos : (0 : ℚ) < 2 ^ expShift t := by positivity
    have hr0 : 0 ≤ t / 2 ^ expShift t := div_nonneg ht hpos.le
    have hr1 : t / 2 ^ expShift t ≤ 1 := by
      rw [div_le_one hpos]; exact (lt_two_pow_expShift ht).le
    obtain ⟨h1, h2⟩ := expSmall_spec hr0 hr1 (expTerms_pos p)
    have key := sqIter_spec p (expShift t) _ _ h1 h2
    have he : (2 : ℝ) ^ expShift t * ((t / 2 ^ expShift t : ℚ) : ℝ) = t := by
      push_cast; field_simp
    rwa [he] at key

theorem expBounds_spec (q : ℚ) (p : ℕ) :
    ((expBounds q p).1 : ℝ) ≤ Real.exp q ∧ Real.exp q ≤ (expBounds q p).2 := by
  unfold expBounds
  dsimp only
  by_cases hq : 0 ≤ q
  · simp only [hq, ↓reduceIte]; exact expPosBounds_spec hq p
  · simp only [hq, ↓reduceIte]
    have hq' : 0 ≤ -q := by linarith [not_le.mp hq]
    obtain ⟨h1, h2⟩ := expPosBounds_spec hq' p
    push_cast at h1 h2
    have hinv : Real.exp (q : ℝ) = 1 / Real.exp (-(q : ℝ)) := by
      rw [Real.exp_neg]; simp
    have hpos := Real.exp_pos (-(q : ℝ))
    constructor
    · by_cases hb : 0 < (expPosBounds (-q) p).2
      · simp only [hb, ↓reduceIte]; push_cast; rw [hinv]
        exact one_div_le_one_div_of_le hpos h2
      · simp only [hb, ↓reduceIte]; push_cast; exact (Real.exp_pos _).le
    · by_cases hb : 0 < (expPosBounds (-q) p).1
      · simp only [hb, ↓reduceIte]; push_cast; rw [hinv]
        exact one_div_le_one_div_of_le (by exact_mod_cast hb) h1
      · simp only [hb, ↓reduceIte]; push_cast
        exact Real.exp_le_one_iff.mpr (by exact_mod_cast (not_le.mp hq).le)

/-! ### log -/

theorem logSeries_eq (y : ℚ) (n : ℕ) :
    (logSeries y n : ℝ) = ∑ i ∈ range n, (y : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [logSeries]
  | succ n ih => rw [logSeries, sum_range_succ, ← ih]; push_cast; ring

/-- `log (1 - y)` lies within `logErr y n` of `-logSeries y n`. -/
theorem log_one_sub_bounds {y : ℚ} (hy : |y| ≤ 1 / 2) (n : ℕ) :
    ((-logSeries y n - logErr y n : ℚ) : ℝ) ≤ Real.log (1 - y) ∧
      Real.log (1 - y) ≤ ((-logSeries y n + logErr y n : ℚ) : ℝ) := by
  have hy' : |(y : ℝ)| < 1 := by
    have : ((|y| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hy
    rw [Rat.cast_abs] at this
    push_cast at this
    linarith
  have hb := Real.abs_log_sub_add_sum_range_le hy' n
  have he : (logErr y n : ℝ) = |(y : ℝ)| ^ (n + 1) / (1 - |(y : ℝ)|) := by
    simp [logErr, ratAbs'_eq]
  rw [← logSeries_eq, ← he] at hb
  obtain ⟨hl, hh⟩ := abs_le.mp hb
  push_cast
  constructor <;> linarith

theorem ln2Bounds_spec (p : ℕ) :
    ((ln2Bounds p).1 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (ln2Bounds p).2 := by
  obtain ⟨h1, h2⟩ := log_one_sub_bounds (y := 1 / 2) (by norm_num) (p + 2)
  have hl : Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [hl] at h1 h2
  simp only [ln2Bounds]
  push_cast at h1 h2 ⊢
  constructor <;> linarith

theorem logBounds_spec {q : ℚ} (hq : 0 < q) (p : ℕ) :
    ((logBounds q p).1 : ℝ) ≤ Real.log q ∧ Real.log q ≤ (logBounds q p).2 := by
  unfold logBounds
  dsimp only
  by_cases hy : ratAbs' (1 - q / pow2 (logRedExp q)) ≤ 1 / 2
  · simp only [hy, ↓reduceIte]
    set e := logRedExp q
    set y : ℚ := 1 - q / pow2 e with hydef
    rw [ratAbs'_eq] at hy
    obtain ⟨hB1, hB2⟩ := log_one_sub_bounds hy (logTerms y p)
    obtain ⟨hL1, hL2⟩ := ln2Bounds_spec p
    have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
    have hlog : Real.log q = Real.log (1 - (y : ℝ)) + e * Real.log 2 := by
      have : (1 : ℝ) - y = (q : ℝ) / (2 : ℝ) ^ e := by
        rw [hydef]; push_cast; rw [pow2_cast]; ring
      rw [this, Real.log_div (by exact_mod_cast hq.ne') h2e.ne', Real.log_zpow]; ring
    rw [hlog]
    push_cast at hB1 hB2
    by_cases he : 0 ≤ e
    · simp only [he, ↓reduceIte]
      have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
      have := mul_le_mul_of_nonneg_left hL1 he'
      have := mul_le_mul_of_nonneg_left hL2 he'
      push_cast
      constructor <;> linarith
    · simp only [he, ↓reduceIte]
      have he' : (e : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp he).le
      have := mul_le_mul_of_nonpos_left hL1 he'
      have := mul_le_mul_of_nonpos_left hL2 he'
      push_cast
      constructor <;> linarith
  · simp only [hy, ↓reduceIte]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    push_cast
    constructor
    · have := Real.one_sub_inv_le_log_of_pos hq'
      simpa [one_div] using this
    · exact Real.log_le_sub_one_of_pos hq'


/-! ### Ziv loop and rounding -/

theorem ziv_eq (f : ℕ → ℚ × ℚ) (rnd : ℚ → UInt64) (pick : ℚ × ℚ → ℚ) :
    ∀ fuel k, ∃ p, (ziv f rnd pick k fuel).1 = rnd (pick (f p))
  | 0, k => ⟨_, rfl⟩
  | fuel + 1, k => by
    simp only [ziv]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ziv_eq f rnd pick fuel (k + 1)

theorem zivDown_loR {f : ℕ → ℚ × ℚ} {y : ℝ} (hf : ∀ p, ((f p).1 : ℝ) ≤ y) :
    loR (bitsToEVal (zivDown f).1) y := by
  obtain ⟨p, hp⟩ := ziv_eq f ofRatDown Prod.fst zivFuel 0
  unfold zivDown; rw [hp]
  exact loR_mono (ofRatDown_isRoundDownR _).1 (hf p)

theorem zivUp_hiR {f : ℕ → ℚ × ℚ} {y : ℝ} (hf : ∀ p, y ≤ ((f p).2 : ℝ)) :
    hiR (bitsToEVal (zivUp f).1) y := by
  obtain ⟨p, hp⟩ := ziv_eq f ofRatUp Prod.snd zivFuel 0
  unfold zivUp; rw [hp]
  exact hiR_mono (ofRatUp_isRoundUpR _).1 (hf p)

theorem ofRatDown_loR {c : ℚ} {y : ℝ} (h : (c : ℝ) ≤ y) : loR (bitsToEVal (ofRatDown c)) y :=
  loR_mono (ofRatDown_isRoundDownR c).1 h

theorem ofRatUp_hiR {c : ℚ} {y : ℝ} (h : y ≤ (c : ℝ)) : hiR (bitsToEVal (ofRatUp c)) y :=
  hiR_mono (ofRatUp_isRoundUpR c).1 h

theorem bitsToEVal_posInf : bitsToEVal posInf = some .posInf := by decide
theorem bitsToEVal_negInf : bitsToEVal negInf = some .negInf := by decide

theorem loR_ofBits {B : UInt64} {y : ℝ} (h : loR (bitsToEVal B) y) :
    loR (bitsToEVal (Float.ofBits B).toBits) y := by
  rcases hB : bitsToEVal B with _ | ev
  · rw [hB] at h; exact h.elim
  · rw [bitsToEVal_toBits_ofBits hB, ← hB]; exact h

theorem hiR_ofBits {B : UInt64} {y : ℝ} (h : hiR (bitsToEVal B) y) :
    hiR (bitsToEVal (Float.ofBits B).toBits) y := by
  rcases hB : bitsToEVal B with _ | ev
  · rw [hB] at h; exact h.elim
  · rw [bitsToEVal_toBits_ofBits hB, ← hB]; exact h

/-! ### Overflow / underflow thresholds -/

theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [← Real.log_pow, Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) n)]

theorem expOvfBound_le_exp {q : ℝ} (hq : 710 < q) : (expOvfBound : ℝ) ≤ Real.exp q := by
  rw [expOvfBound, Rat.cast_pow, Rat.cast_ofNat, two_pow_eq_exp, Real.exp_le_exp]
  have := Real.log_two_lt_d9
  push_cast
  linarith

theorem exp_le_expUnfBound {q : ℝ} (hq : q < -746) : Real.exp q ≤ (expUnfBound : ℝ) := by
  rw [expUnfBound, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, two_pow_eq_exp,
    one_div, ← Real.exp_neg, Real.exp_le_exp]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-! ### Rational-input lemmas -/

-- Keep the elaborator from evaluating `2^1024` / the rounding functions.
attribute [local irreducible] expOvfBound expUnfBound ofRatDown ofRatUp

theorem expRat_down (q : ℚ) : loR (bitsToEVal (expRat q false).1) (Real.exp q) := by
  unfold expRat
  by_cases h1 : 710 < q
  · simp only [h1, ↓reduceIte, Bool.false_eq_true]
    exact ofRatDown_loR (expOvfBound_le_exp (by exact_mod_cast h1))
  · by_cases h2 : q < -746
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact ofRatDown_loR (by push_cast; exact (Real.exp_pos _).le)
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact zivDown_loR (fun p => (expBounds_spec q p).1)

theorem expRat_up (q : ℚ) : hiR (bitsToEVal (expRat q true).1) (Real.exp q) := by
  unfold expRat
  by_cases h1 : 710 < q
  · simp only [h1, ↓reduceIte]
    rw [bitsToEVal_posInf]; trivial
  · by_cases h2 : q < -746
    · simp only [h1, h2, ↓reduceIte]
      exact ofRatUp_hiR (exp_le_expUnfBound (by exact_mod_cast h2))
    · simp only [h1, h2, ↓reduceIte]
      exact zivUp_hiR (fun p => (expBounds_spec q p).2)

theorem logRat_down {q : ℚ} {x : ℝ} (hq : 0 ≤ q) (hqx : (q : ℝ) ≤ x) :
    loR (bitsToEVal (logRat q false).1) (Real.log x) := by
  unfold logRat
  have hn : ¬ q < 0 := not_lt.mpr hq
  by_cases h0 : q = 0
  · simp only [h0, lt_self_iff_false, ↓reduceIte]
    rw [bitsToEVal_negInf]; trivial
  · have hq0 : 0 < q := lt_of_le_of_ne hq (Ne.symm h0)
    have hlog : Real.log q ≤ Real.log x := Real.log_le_log (by exact_mod_cast hq0) hqx
    by_cases h1 : q = 1
    · subst h1
      simp only [hn, ↓reduceIte, Bool.false_eq_true, one_ne_zero]
      exact ofRatDown_loR (by simpa using hlog)
    · simp only [hn, h0, h1, ↓reduceIte, Bool.false_eq_true]
      exact zivDown_loR (fun p => le_trans (logBounds_spec hq0 p).1 hlog)

theorem logRat_up {q : ℚ} {x : ℝ} (hxq : x ≤ (q : ℝ)) (hx : 0 < x) :
    hiR (bitsToEVal (logRat q true).1) (Real.log x) := by
  have hq0 : 0 < q := by exact_mod_cast lt_of_lt_of_le hx hxq
  unfold logRat
  have hn : ¬ q < 0 := not_lt.mpr hq0.le
  have h0 : q ≠ 0 := hq0.ne'
  have hlog : Real.log x ≤ Real.log q := Real.log_le_log hx hxq
  by_cases h1 : q = 1
  · subst h1
    simp only [hn, ↓reduceIte, one_ne_zero]
    exact ofRatUp_hiR (by simpa using hlog)
  · simp only [hn, h0, h1, ↓reduceIte]
    exact zivUp_hiR (fun p => le_trans hlog (logBounds_spec hq0 p).2)


/-! ### Bit-level and float-level lifting -/

theorem bitsToEVal_of_finite {b : UInt64} {s : Float.Model.UnpackedFloat.Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hu : unpackBits b = .finite s m e hm) : bitsToEVal b = some (.rat (signedVal s m e)) := by
  simp [bitsToEVal, hu, toEVal]

theorem bitsToRat?_of_finite {b : UInt64} {s : Float.Model.UnpackedFloat.Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (hu : unpackBits b = .finite s m e hm) : bitsToRat? b = some (signedVal s m e) := by
  simp only [bitsToRat?, hu, toRat?_finite _ _ _ hm]

theorem isNaN_false_of_loR {f : Float} {x : ℝ} (h : loR (bitsToEVal f.toBits) x) :
    f.isNaN = false := by
  rcases hb : bitsToEVal f.toBits with _ | ev
  · rw [hb] at h; exact h.elim
  · exact not_isNaN_of_bitsToEVal hb

theorem isNaN_false_of_hiR {f : Float} {x : ℝ} (h : hiR (bitsToEVal f.toBits) x) :
    f.isNaN = false := by
  rcases hb : bitsToEVal f.toBits with _ | ev
  · rw [hb] at h; exact h.elim
  · exact not_isNaN_of_bitsToEVal hb

theorem expDownBits_loR {b : UInt64} {x : ℝ} (h : loR (bitsToEVal b) x) :
    loR (bitsToEVal (expDownBits b)) (Real.exp x) := by
  unfold expDownBits expBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ofRatDown_loR (by push_cast; exact (Real.exp_pos x).le)
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s =>
    have h0 : (0 : ℝ) ≤ x := by simpa [bitsToEVal, hu, toEVal, loR] using h
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ofRatDown_loR (by push_cast; exact Real.one_le_exp h0)
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (expRat_down _) (Real.exp_le_exp.mpr hq)

theorem expUpBits_hiR {b : UInt64} {x : ℝ} (h : hiR (bitsToEVal b) x) :
    hiR (bitsToEVal (expUpBits b)) (Real.exp x) := by
  unfold expUpBits expBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive => show hiR (bitsToEVal posInf) _; rw [bitsToEVal_posInf]; trivial
  | zero s =>
    have h0 : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    simp only [↓reduceIte]
    exact ofRatUp_hiR (by push_cast; exact Real.exp_le_one_iff.mpr h0)
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (expRat_up _) (Real.exp_le_exp.mpr hq)

/-- `expDown` is a lower bound for `exp` (any input, extended reals). -/
theorem expDown_loR {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Directed.expDown a).toBits) (Real.exp x) :=
  loR_ofBits (expDownBits_loR h)

/-- `expUp` is an upper bound for `exp` (any input, extended reals). -/
theorem expUp_hiR {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) :
    hiR (bitsToEVal (Directed.expUp a).toBits) (Real.exp x) :=
  hiR_ofBits (expUpBits_hiR h)

theorem negInf_loR {x : ℝ} : loR (bitsToEVal (Float.ofBits negInf).toBits) x := by
  apply loR_ofBits; rw [bitsToEVal_negInf]; trivial

theorem posInf_hiR {x : ℝ} : hiR (bitsToEVal (Float.ofBits posInf).toBits) x := by
  apply hiR_ofBits; rw [bitsToEVal_posInf]; trivial

/-- Lower endpoint of the interval `log`: `logLo a ≤ log x` whenever `a ≤ x`
    (`logLo a = logDown a` for `a > 0`, `-∞` for `a ≤ 0`). -/
theorem logLo_loR {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Interval64.logLo a).toBits) (Real.log x) := by
  unfold Interval64.logLo
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
      have hq : ((signedVal .positive m e : ℚ) : ℝ) ≤ x := by
        rw [bitsToEVal_of_finite hu] at h; exact h
      apply loR_ofBits
      unfold logDownBits logBitsD
      rw [hu]
      simp only [bitsToRat?_of_finite hu]
      exact logRat_down (by simpa [signedVal] using mag_nonneg m e) hq

/-- `logUp a ≥ log x` whenever `x ≤ a` and `x > 0`. -/
theorem logUp_hiR {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) (hx : 0 < x) :
    hiR (bitsToEVal (Directed.logUp a).toBits) (Real.log x) := by
  apply hiR_ofBits
  unfold logUpBits logBitsD
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
    simp only [bitsToRat?_of_finite hu]
    exact logRat_up hq hx

/-! ### Interval enclosures -/

/-- `exp` interval enclosure: no finiteness assumption. -/
theorem exp_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.exp x ∈ (Interval64.exp X).toSet := by
  unfold Interval64.exp
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨expDown_loR hx.1, expUp_hiR hx.2⟩

/-- `log` interval enclosure for every positive member. -/
theorem log_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 < x) :
    Real.log x ∈ (Interval64.log X).toSet := by
  unfold Interval64.log
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  have h2 := hx.2
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  cases hu : unpackBits X.hi.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h2
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h2
    | positive => exact ⟨logLo_loR hx.1, posInf_hiR⟩
  | zero s =>
    have : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h2
    linarith
  | finite s m e hm =>
    cases s with
    | negative =>
      have : x ≤ ((signedVal .negative m e : ℚ) : ℝ) := by
        rw [bitsToEVal_of_finite hu] at h2; exact h2
      have hneg : ((signedVal .negative m e : ℚ) : ℝ) ≤ 0 := by
        have := mag_nonneg m e
        simp [signedVal]; exact_mod_cast this
      linarith
    | positive => exact ⟨logLo_loR hx.1, logUp_hiR h2 hx0⟩

end RealFP.Transc
