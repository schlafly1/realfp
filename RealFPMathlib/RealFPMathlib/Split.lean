/-
Real semantics of extended division (`Interval64.divSplit`).

* `Membership ℝ Interval64Pair`: `x ∈ P ↔ x ∈ P.piece1 ∨ x ∈ P.piece2` (union).
* `mem_hull`: `x ∈ P → x ∈ P.hull` (so the coercion to `Interval64` is sound).
* `divSplit_mem`: `x ∈ A → y ∈ B → y ≠ 0 → x / y ∈ divSplit A B` (finite endpoints,
  the same hypotheses as `div_mem_toSet`).
-/
import RealFPMathlib.Conv
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
    exact Or.inl (div_mem_toSet hx hy hy0 ⟨al, hal⟩ ⟨ah, hah⟩ ⟨bl, hbl⟩ ⟨bh, hbh⟩)
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
theorem divSplit_hull_mem {A B : Interval64} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) (hy0 : y ≠ 0)
    (hAlo : ∃ q, bitsToRat? A.lo.toBits = some q) (hAhi : ∃ q, bitsToRat? A.hi.toBits = some q)
    (hBlo : ∃ q, bitsToRat? B.lo.toBits = some q) (hBhi : ∃ q, bitsToRat? B.hi.toBits = some q) :
    x / y ∈ (divSplit A B : Interval64) :=
  mem_hull (divSplit_mem hx hy hy0 hAlo hAhi hBlo hBhi)

end RealFP
