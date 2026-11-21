/-
Real semantics of extended division (`Interval64.divSplit`).

* `Membership ℝ Interval64Pair`: `x ∈ P ↔ x ∈ P.piece1 ∨ x ∈ P.piece2` (union).
* `mem_hull`: `x ∈ P → x ∈ P.hull` (so the coercion to `Interval64` is sound).
* `mem_divSplit`: `x ∈ A → y ∈ B → y ≠ 0 → x / y ∈ divSplit A B`, no finiteness
  assumption (`mem_divSplit_hull` for the hull). The older `divSplit_mem` /
  `divSplit_hull_mem` (finite endpoints) are deprecated.
-/
import RealFPMathlib.Conv
import RealFPMathlib.Unbounded
import Interval64.Split

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.FloatBits Interval64Proofs.Div

namespace RealFP

instance : Membership ℝ Interval64Pair := ⟨fun P x => x ∈ P.piece1 ∨ x ∈ P.piece2⟩

@[simp] theorem pair_mem_iff {P : Interval64Pair} {x : ℝ} :
    x ∈ P ↔ x ∈ P.piece1 ∨ x ∈ P.piece2 := Iff.rfl

theorem not_mem_invalid (x : ℝ) : x ∉ invalid := by
  intro h
  have h1 := h.1
  rw [show bitsToEVal invalid.lo.toBits = none by decide +kernel] at h1
  exact h1

theorem mem_whole (x : ℝ) : x ∈ whole := by
  refine ⟨?_, ?_⟩
  · rw [show bitsToEVal whole.lo.toBits = some .negInf by decide +kernel]; trivial
  · rw [show bitsToEVal whole.hi.toBits = some .posInf by decide +kernel]; trivial

theorem mem_lowerRay {u : Float} {x : ℝ} :
    x ∈ (⟨-Float.inf, u⟩ : Interval64) ↔ hiR (bitsToEVal u.toBits) x := by
  show (loR _ x ∧ hiR _ x) ↔ _
  rw [show bitsToEVal (-Float.inf).toBits = some .negInf by decide +kernel]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

theorem mem_upperRay {l : Float} {x : ℝ} :
    x ∈ (⟨l, Float.inf⟩ : Interval64) ↔ loR (bitsToEVal l.toBits) x := by
  show (loR _ x ∧ hiR _ x) ↔ _
  rw [show bitsToEVal Float.inf.toBits = some .posInf by decide +kernel]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem mem_toList {P : Interval64Pair} {x : ℝ} : x ∈ P ↔ ∃ I ∈ P.toList, x ∈ I := by
  cases P with
  | empty =>
    simp only [pair_mem_iff, Interval64Pair.piece1, Interval64Pair.piece2,
      Interval64Pair.toList, List.not_mem_nil, false_and, exists_false, or_self, iff_false]
    exact not_mem_invalid x
  | one I =>
    simp only [pair_mem_iff, Interval64Pair.piece1, Interval64Pair.piece2,
      Interval64Pair.toList, List.mem_singleton, exists_eq_left]
    exact ⟨fun h => h.elim id (fun h' => (not_mem_invalid x h').elim), Or.inl⟩
  | two u l =>
    simp only [pair_mem_iff, Interval64Pair.piece1, Interval64Pair.piece2,
      Interval64Pair.toList, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]

theorem mem_hull {P : Interval64Pair} {x : ℝ} (h : x ∈ P) : x ∈ P.hull := by
  cases P with
  | empty => exact (h.elim (not_mem_invalid x) (not_mem_invalid x)).elim
  | one I => exact h.elim id (fun h' => (not_mem_invalid x h').elim)
  | two u l => exact mem_whole x

/-- Coercion form of `mem_hull`. -/
theorem mem_coe {P : Interval64Pair} {x : ℝ} (h : x ∈ P) : x ∈ (P : Interval64) := mem_hull h

/-! ### Directed division against reals -/

theorem divDown_loR {a b : Float} {qa qb : ℚ} (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) (hqb : qb ≠ 0) :
    loR (bitsToEVal (Directed.divDown a b).toBits) ((qa : ℝ) / qb) := by
  have h := loEncloses_divDown ha hb hqb
  rw [← loR_cast] at h; push_cast at h; exact h

theorem divUp_hiR {a b : Float} {qa qb : ℚ} (ha : bitsToRat? a.toBits = some qa)
    (hb : bitsToRat? b.toBits = some qb) (hqb : qb ≠ 0) :
    hiR (bitsToEVal (Directed.divUp a b).toBits) ((qa : ℝ) / qb) := by
  have h := hiEncloses_divUp ha hb hqb
  rw [← hiR_cast] at h; push_cast at h; exact h

/-! ### Sign-case inequalities -/

theorem div_pp {a x y d : ℝ} (ha : 0 < a) (hax : a ≤ x) (hy : 0 < y) (hyd : y ≤ d) :
    a / d ≤ x / y := by
  rw [div_le_div_iff₀ (by linarith) hy]; nlinarith

theorem div_pn {a x y c : ℝ} (ha : 0 < a) (hax : a ≤ x) (hy : y < 0) (hcy : c ≤ y) :
    x / y ≤ a / c := by
  rw [← neg_div_neg_eq x y, ← neg_div_neg_eq a c, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem div_np {a x y d : ℝ} (ha : a < 0) (hxa : x ≤ a) (hy : 0 < y) (hyd : y ≤ d) :
    x / y ≤ a / d := by
  rw [div_le_div_iff₀ hy (by linarith)]; nlinarith

theorem div_nn {a x y c : ℝ} (ha : a < 0) (hxa : x ≤ a) (hy : y < 0) (hcy : c ≤ y) :
    a / c ≤ x / y := by
  rw [← neg_div_neg_eq x y, ← neg_div_neg_eq a c, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### Enclosure -/

set_option linter.unusedSimpArgs false in
@[deprecated "use RealFP.mem_divSplit (no finiteness hypotheses)" (since := "2026-11-21")]
theorem divSplit_mem {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) (hy0 : y ≠ 0)
    (hAlo : ∃ q, bitsToRat? A.lo.toBits = some q) (hAhi : ∃ q, bitsToRat? A.hi.toBits = some q)
    (hBlo : ∃ q, bitsToRat? B.lo.toBits = some q) (hBhi : ∃ q, bitsToRat? B.hi.toBits = some q) :
    x / y ∈ divSplit A B := by
  obtain ⟨al, hal⟩ := hAlo; obtain ⟨ah, hah⟩ := hAhi
  obtain ⟨bl, hbl⟩ := hBlo; obtain ⟨bh, hbh⟩ := hBhi
  obtain ⟨-, -, hax, hxa⟩ := memIv_endpoints hal hah hx
  obtain ⟨-, -, hby, hyb⟩ := memIv_endpoints hbl hbh hy
  have hnan : anyNan A B = false := by
    simp only [anyNan, not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hal),
      not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hah),
      not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hbl),
      not_isNaN_of_bitsToEVal (bitsToEVal_rat_of_bitsToRat? hbh), Bool.or_self]
  have e1 : decide (0 ≤ B.lo) = decide (0 ≤ bl) := decide_eq_decide.mpr (zero_le_iff_rat hbl)
  have e2 : decide (B.hi ≤ 0) = decide (bh ≤ 0) := decide_eq_decide.mpr (le_zero_iff_rat hbh)
  have e3 : decide (A.lo ≤ 0) = decide (al ≤ 0) := decide_eq_decide.mpr (le_zero_iff_rat hal)
  have e4 : containsZero A = decide (al ≤ 0 ∧ 0 ≤ ah) := by
    rw [Bool.eq_iff_iff, containsZero_iff hal hah, decide_eq_true_iff]
  have e5 : containsZero B = decide (bl ≤ 0 ∧ 0 ≤ bh) := by
    rw [Bool.eq_iff_iff, containsZero_iff hbl hbh, decide_eq_true_iff]
  have hblR : ∀ {q : ℚ}, (q ≤ bl) → (q : ℝ) ≤ bl := fun h => by exact_mod_cast h
  unfold divSplit
  simp only [hnan, e1, e2, e3, e4, e5, Bool.false_eq_true, ↓reduceIte]
  by_cases hcb : bl ≤ 0 ∧ 0 ≤ bh
  swap
  · simp only [hcb, decide_false, Bool.not_false, ↓reduceIte]
    exact Or.inl (mem_toSet_div hx hy hy0)
  simp only [hcb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hbl0 : (bl : ℝ) ≤ 0 := by exact_mod_cast hcb.1
  have hbh0 : (0 : ℝ) ≤ bh := by exact_mod_cast hcb.2
  by_cases hbn : 0 ≤ bl
  · -- b.lo = 0, so y > 0
    have hblz : (bl : ℝ) = 0 := le_antisymm hbl0 (by exact_mod_cast hbn)
    have hyp : 0 < y := lt_of_le_of_ne (hblz ▸ hby) (Ne.symm hy0)
    have hbhp : 0 < bh := by exact_mod_cast (lt_of_lt_of_le hyp hyb)
    simp only [hbn, decide_true, Bool.not_true, Bool.true_and, Bool.false_and]
    by_cases hbp : bh ≤ 0
    · exact absurd hbp (not_le.mpr hbhp)
    simp only [hbp, decide_false, Bool.not_false, Bool.true_eq_false, ↓reduceIte]
    by_cases hca : al ≤ 0 ∧ 0 ≤ ah
    · simp only [hca, decide_true, ↓reduceIte]; exact Or.inl (mem_whole _)
    simp only [hca, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hap : al ≤ 0
    · -- a < 0
      have hahn : ah < 0 := by
        by_contra h; exact hca ⟨hap, not_lt.mp h⟩
      simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Or.inl (mem_lowerRay.mpr (hiR_mono (divUp_hiR hah hbh hbhp.ne') ?_))
      exact div_np (by exact_mod_cast hahn) hxa hyp hyb
    · simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
      have halp : (0 : ℝ) < al := by exact_mod_cast (not_le.mp hap)
      refine Or.inl (mem_upperRay.mpr (loR_mono (divDown_loR hal hbh hbhp.ne') ?_))
      exact div_pp halp hax hyp hyb
  · have hbln : bl < 0 := not_le.mp hbn
    simp only [hbn, decide_false, Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    by_cases hca : al ≤ 0 ∧ 0 ≤ ah
    · simp only [hca, decide_true, ↓reduceIte]; exact Or.inl (mem_whole _)
    simp only [hca, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hbp : bh ≤ 0
    · -- b.hi = 0, so y < 0
      have hyn : y < 0 := lt_of_le_of_ne (le_trans hyb (by exact_mod_cast hbp)) hy0
      simp only [hbp, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hap : al ≤ 0
      · have hahn : ah < 0 := by
          by_contra h; exact hca ⟨hap, not_lt.mp h⟩
        simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine Or.inl (mem_upperRay.mpr (loR_mono (divDown_loR hah hbl hbln.ne) ?_))
        exact div_nn (by exact_mod_cast hahn) hxa hyn hby
      · simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
        have halp : (0 : ℝ) < al := by exact_mod_cast (not_le.mp hap)
        refine Or.inl (mem_lowerRay.mpr (hiR_mono (divUp_hiR hal hbl hbln.ne) ?_))
        exact div_pn halp hax hyn hby
    · have hbhp : 0 < bh := not_le.mp hbp
      simp only [hbp, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hap : al ≤ 0
      · have hahn : ah < 0 := by
          by_contra h; exact hca ⟨hap, not_lt.mp h⟩
        simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases lt_or_gt_of_ne hy0 with hyn | hyp
        · refine Or.inr (mem_upperRay.mpr (loR_mono (divDown_loR hah hbl hbln.ne) ?_))
          exact div_nn (by exact_mod_cast hahn) hxa hyn hby
        · refine Or.inl (mem_lowerRay.mpr (hiR_mono (divUp_hiR hah hbh hbhp.ne') ?_))
          exact div_np (by exact_mod_cast hahn) hxa hyp hyb
      · simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
        have halp : (0 : ℝ) < al := by exact_mod_cast (not_le.mp hap)
        rcases lt_or_gt_of_ne hy0 with hyn | hyp
        · refine Or.inl (mem_lowerRay.mpr (hiR_mono (divUp_hiR hal hbl hbln.ne) ?_))
          exact div_pn halp hax hyn hby
        · refine Or.inr (mem_upperRay.mpr (loR_mono (divDown_loR hal hbh hbhp.ne') ?_))
          exact div_pp halp hax hyp hyb

/-- Hull form: `x / y ∈ (divSplit A B : Interval64)`. -/
@[deprecated "use RealFP.mem_divSplit_hull (no finiteness hypotheses)" (since := "2026-11-21")]
theorem divSplit_hull_mem {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) (hy0 : y ≠ 0)
    (hAlo : ∃ q, bitsToRat? A.lo.toBits = some q) (hAhi : ∃ q, bitsToRat? A.hi.toBits = some q)
    (hBlo : ∃ q, bitsToRat? B.lo.toBits = some q) (hBhi : ∃ q, bitsToRat? B.hi.toBits = some q) :
    x / y ∈ (divSplit A B : Interval64) :=
  set_option linter.deprecated false in
  mem_hull (divSplit_mem hx hy hy0 hAlo hAhi hBlo hBhi)

/-! ### Enclosure without finiteness assumptions -/

theorem goodDLo_pp {a x y : ℝ} {D : EReal} (ha : 0 < a) (hax : a ≤ x) (hy : 0 < y)
    (hyD : (y : EReal) ≤ D) : GoodDLo (a : EReal) D (x / y) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h; rw [h] at hyD; exact absurd hyD (not_le.2 (by exact_mod_cast hy))
  · induction D using EReal.rec with
    | bot => exact absurd hyD (by simp)
    | coe d =>
      exact coe_div_le (div_pp ha hax hy (by exact_mod_cast hyD))
    | top =>
      rw [EReal.div_top]
      exact_mod_cast (div_pos (lt_of_lt_of_le ha hax) hy).le

theorem goodDHi_pn {a x y : ℝ} {C : EReal} (ha : 0 < a) (hax : a ≤ x) (hy : y < 0)
    (hCy : C ≤ (y : EReal)) : GoodDHi (a : EReal) C (x / y) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h; rw [h] at hCy; exact absurd hCy (not_le.2 (by exact_mod_cast hy))
  · induction C using EReal.rec with
    | bot =>
      rw [EReal.div_bot]
      exact_mod_cast div_nonpos_of_nonneg_of_nonpos (lt_of_lt_of_le ha hax).le hy.le
    | coe c =>
      exact coe_le_div (div_pn ha hax hy (by exact_mod_cast hCy))
    | top => exact absurd hCy (by simp)

theorem goodDHi_np {a x y : ℝ} {D : EReal} (ha : a < 0) (hxa : x ≤ a) (hy : 0 < y)
    (hyD : (y : EReal) ≤ D) : GoodDHi (a : EReal) D (x / y) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h; rw [h] at hyD; exact absurd hyD (not_le.2 (by exact_mod_cast hy))
  · induction D using EReal.rec with
    | bot => exact absurd hyD (by simp)
    | coe d =>
      exact coe_le_div (div_np ha hxa hy (by exact_mod_cast hyD))
    | top =>
      rw [EReal.div_top]
      exact_mod_cast div_nonpos_of_nonpos_of_nonneg (le_trans hxa ha.le) hy.le

theorem goodDLo_nn {a x y : ℝ} {C : EReal} (ha : a < 0) (hxa : x ≤ a) (hy : y < 0)
    (hCy : C ≤ (y : EReal)) : GoodDLo (a : EReal) C (x / y) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h; rw [h] at hCy; exact absurd hCy (not_le.2 (by exact_mod_cast hy))
  · induction C using EReal.rec with
    | bot =>
      rw [EReal.div_bot]
      exact_mod_cast div_nonneg_of_nonpos (le_trans hxa ha.le) hy.le
    | coe c =>
      exact coe_div_le (div_nn ha hxa hy (by exact_mod_cast hCy))
    | top => exact absurd hCy (by simp)

theorem mem_upperRay_of {l : Float} {z : ℝ} (h : l.isNaN = false ∧ l.toE ≤ (z : EReal)) :
    z ∈ (⟨l, Float.inf⟩ : Interval64) :=
  mem_upperRay.2 ((loR_iff_toE _ _).2 h)

theorem mem_lowerRay_of {u : Float} {z : ℝ} (h : u.isNaN = false ∧ (z : EReal) ≤ u.toE) :
    z ∈ (⟨-Float.inf, u⟩ : Interval64) :=
  mem_lowerRay.2 ((hiR_iff_toE _ _).2 h)

set_option linter.unusedSimpArgs false in
/-- `x / y ∈ divSplit A B` for `x ∈ A`, `y ∈ B`, `y ≠ 0`, with no finiteness assumption
    (half-lines and `whole` allowed). -/
theorem mem_divSplit {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) (hy0 : y ≠ 0) :
    x / y ∈ divSplit A B := by
  obtain ⟨⟨hAl, hAl'⟩, ⟨hAh, hAh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hBl, hBl'⟩, ⟨hBh, hBh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan A B = false := by simp [anyNan, hAl, hAh, hBl, hBh]
  have e1 : decide (0 ≤ B.lo) = decide (0 ≤ B.lo.toE) :=
    decide_eq_decide.mpr (zero_le_iff_toE hBl)
  have e2 : decide (B.hi ≤ 0) = decide (B.hi.toE ≤ 0) :=
    decide_eq_decide.mpr (le_zero_iff_toE hBh)
  have e3 : decide (A.lo ≤ 0) = decide (A.lo.toE ≤ 0) :=
    decide_eq_decide.mpr (le_zero_iff_toE hAl)
  have e4 : containsZero A = decide (A.lo.toE ≤ 0 ∧ 0 ≤ A.hi.toE) := by
    rw [Bool.eq_iff_iff, containsZero_iff_toE hAl hAh, decide_eq_true_iff]
  have e5 : containsZero B = decide (B.lo.toE ≤ 0 ∧ 0 ≤ B.hi.toE) := by
    rw [Bool.eq_iff_iff, containsZero_iff_toE hBl hBh, decide_eq_true_iff]
  unfold divSplit
  simp only [hnan, e1, e2, e3, e4, e5, Bool.false_eq_true, ↓reduceIte]
  by_cases hcb : B.lo.toE ≤ 0 ∧ 0 ≤ B.hi.toE
  swap
  · simp only [hcb, decide_false, Bool.not_false, ↓reduceIte]
    exact Or.inl (mem_toSet_div hx hy hy0)
  simp only [hcb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hApos : ¬ A.lo.toE ≤ 0 → ∃ al : ℝ, A.lo.toE = (al : EReal) ∧ 0 < al ∧ al ≤ x := by
    intro h
    have h0 : 0 < A.lo.toE := not_le.1 h
    obtain ⟨q, -, he⟩ := exists_rat_of_toE hAl (fun hb => by rw [hb] at h0; simp at h0)
      (fun ht => by rw [ht] at hAl'; simp at hAl')
    rw [he] at h0 hAl'
    exact ⟨q, he, by exact_mod_cast h0, by exact_mod_cast hAl'⟩
  have hAneg : A.lo.toE ≤ 0 → ¬ (A.lo.toE ≤ 0 ∧ 0 ≤ A.hi.toE) →
      ∃ ah : ℝ, A.hi.toE = (ah : EReal) ∧ ah < 0 ∧ x ≤ ah := by
    intro h hc
    have h0 : A.hi.toE < 0 := by by_contra h'; exact hc ⟨h, not_lt.1 h'⟩
    obtain ⟨q, -, he⟩ := exists_rat_of_toE hAh (fun hb => by rw [hb] at hAh'; simp at hAh')
      (fun ht => by rw [ht] at h0; simp at h0)
    rw [he] at h0 hAh'
    exact ⟨q, he, by exact_mod_cast h0, by exact_mod_cast hAh'⟩
  by_cases hbn : 0 ≤ B.lo.toE
  · -- b.lo = 0, so y > 0
    have hyp : 0 < y := by
      have : ((0 : ℝ) : EReal) ≤ y := le_trans (by simpa using hbn) hBl'
      exact lt_of_le_of_ne (by exact_mod_cast this) (Ne.symm hy0)
    have hbhp : 0 < B.hi.toE := lt_of_lt_of_le (by exact_mod_cast hyp) hBh'
    simp only [hbn, decide_true, Bool.not_true, Bool.true_and, Bool.false_and]
    have hbp : ¬ B.hi.toE ≤ 0 := not_le.2 hbhp
    simp only [hbp, decide_false, Bool.not_false, Bool.true_eq_false, ↓reduceIte]
    by_cases hca : A.lo.toE ≤ 0 ∧ 0 ≤ A.hi.toE
    · simp only [hca, decide_true, ↓reduceIte]; exact Or.inl (mem_whole _)
    simp only [hca, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hap : A.lo.toE ≤ 0
    · obtain ⟨ah, he, ha0, hxa⟩ := hAneg hap hca
      simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine Or.inl (mem_lowerRay_of (divUp_good hAh hBh ?_))
      rw [he]; exact goodDHi_np ha0 hxa hyp hBh'
    · obtain ⟨al, he, ha0, hax⟩ := hApos hap
      simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
      refine Or.inl (mem_upperRay_of (divDown_good hAl hBh ?_))
      rw [he]; exact goodDLo_pp ha0 hax hyp hBh'
  · simp only [hbn, decide_false, Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    by_cases hca : A.lo.toE ≤ 0 ∧ 0 ≤ A.hi.toE
    · simp only [hca, decide_true, ↓reduceIte]; exact Or.inl (mem_whole _)
    simp only [hca, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hbp : B.hi.toE ≤ 0
    · -- b.hi = 0, so y < 0
      have hyn : y < 0 := by
        have : (y : EReal) ≤ ((0 : ℝ) : EReal) := le_trans hBh' (by simpa using hbp)
        exact lt_of_le_of_ne (by exact_mod_cast this) hy0
      simp only [hbp, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hap : A.lo.toE ≤ 0
      · obtain ⟨ah, he, ha0, hxa⟩ := hAneg hap hca
        simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine Or.inl (mem_upperRay_of (divDown_good hAh hBl ?_))
        rw [he]; exact goodDLo_nn ha0 hxa hyn hBl'
      · obtain ⟨al, he, ha0, hax⟩ := hApos hap
        simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
        refine Or.inl (mem_lowerRay_of (divUp_good hAl hBl ?_))
        rw [he]; exact goodDHi_pn ha0 hax hyn hBl'
    · simp only [hbp, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hap : A.lo.toE ≤ 0
      · obtain ⟨ah, he, ha0, hxa⟩ := hAneg hap hca
        simp only [hap, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases lt_or_gt_of_ne hy0 with hyn | hyp
        · refine Or.inr (mem_upperRay_of (divDown_good hAh hBl ?_))
          rw [he]; exact goodDLo_nn ha0 hxa hyn hBl'
        · refine Or.inl (mem_lowerRay_of (divUp_good hAh hBh ?_))
          rw [he]; exact goodDHi_np ha0 hxa hyp hBh'
      · obtain ⟨al, he, ha0, hax⟩ := hApos hap
        simp only [hap, decide_false, Bool.not_false, ↓reduceIte]
        rcases lt_or_gt_of_ne hy0 with hyn | hyp
        · refine Or.inl (mem_lowerRay_of (divUp_good hAl hBl ?_))
          rw [he]; exact goodDHi_pn ha0 hax hyn hBl'
        · refine Or.inr (mem_upperRay_of (divDown_good hAl hBh ?_))
          rw [he]; exact goodDLo_pp ha0 hax hyp hBh'

/-- Hull form of `mem_divSplit`, no finiteness assumption. -/
theorem mem_divSplit_hull {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B)
    (hy0 : y ≠ 0) : x / y ∈ (divSplit A B : Interval64) :=
  mem_hull (mem_divSplit hx hy hy0)

end RealFP
