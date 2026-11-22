/-
Soundness of the Bernstein range enclosures (core `Interval64/Bernstein.lean`).

* `pow_eq_sum_bern` : `t^i = Σ_k C(k,i)/C(n,i) · B_{n,k}(t)` (`i ≤ n`).
* `eval_eq_sum_bern` : `q(t) = Σ_k β_k B_{n,k}(t)` with `β_k = Σ_{i≤k} C(k,i)/C(n,i) a_i`.
* `mem_bern01`, `mem_bernOn`, `mem_bernRange` : 1D enclosures; `lt_of_checkGtB`, `le_of_checkGeB`.
* `mem_bern2On`, `lt_of_checkGt2B` : 2D (tensor) enclosures on boxes.
-/
import RealFPMathlib.Poly
import RealFPMathlib.Quad
import Interval64.Bernstein

open Interval64 RealFP RealFP.Poly Polynomial Finset
open Interval64.Mat (zeroI)

noncomputable section

namespace RealFP.Bern

theorem choose_eq : ∀ n k, IPoly.choose n k = Nat.choose n k
  | n, 0 => by cases n <;> rfl
  | 0, k + 1 => rfl
  | n + 1, k + 1 => by
    show IPoly.choose n k + IPoly.choose n (k + 1) = _
    rw [choose_eq n k, choose_eq n (k + 1), Nat.choose_succ_succ]

/-- Bernstein basis polynomial `B_{n,k}(t)`. -/
def bern (n k : ℕ) (t : ℝ) : ℝ := (n.choose k : ℝ) * t ^ k * (1 - t) ^ (n - k)

def bq (n k i : ℕ) : ℝ := (k.choose i : ℝ) / (n.choose i : ℝ)

theorem bern_nonneg (n k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bern n k t := by
  unfold bern
  have : 0 ≤ 1 - t := by linarith [ht.2]
  have := ht.1
  positivity

theorem pow_eq_sum_bern {n i : ℕ} (hi : i ≤ n) (t : ℝ) :
    t ^ i = ∑ k ∈ range (n + 1), bq n k i * bern n k t := by
  rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ n + 1 by omega)]
  have h0 : ∑ k ∈ range i, bq n k i * bern n k t = 0 :=
    sum_eq_zero fun k hk => by simp [bq, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hk)]
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range]
  have hc : (n.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have key : ∀ j ∈ range (n + 1 - i), bq n (i + j) i * bern n (i + j) t =
      t ^ i * (t ^ j * (1 - t) ^ (n - i - j) * ((n - i).choose j : ℝ)) := by
    intro j hj
    have hj' : i + j ≤ n := by have := Finset.mem_range.1 hj; omega
    have hcm := Nat.choose_mul (n := n) (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at hcm
    have hcm' : (n.choose (i + j) : ℝ) * ((i + j).choose i : ℝ) =
        (n.choose i : ℝ) * ((n - i).choose j : ℝ) := by exact_mod_cast hcm
    have hr : ((i + j).choose i : ℝ) / (n.choose i : ℝ) * (n.choose (i + j) : ℝ) =
        ((n - i).choose j : ℝ) := by
      rw [div_mul_eq_mul_div, div_eq_iff hc]; linarith [hcm']
    simp only [bq, bern]
    rw [show n - (i + j) = n - i - j by omega, pow_add]
    linear_combination (t ^ i * t ^ j * (1 - t) ^ (n - i - j)) * hr
  rw [sum_congr rfl key, ← mul_sum, show n + 1 - i = n - i + 1 by omega, ← add_pow]
  simp

theorem sum_bern (n : ℕ) (t : ℝ) : ∑ k ∈ range (n + 1), bern n k t = 1 := by
  have := pow_eq_sum_bern (Nat.zero_le n) t
  simpa [bq] using this.symm

/-- Bernstein coefficients of the coefficient function `a`. -/
def beta (a : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ range (k + 1), bq n k i * a i

theorem eval_eq_sum_bern {q : ℝ[X]} {n : ℕ} (h : ∀ k, n + 1 ≤ k → q.coeff k = 0) (t : ℝ) :
    q.eval t = ∑ k ∈ range (n + 1), beta q.coeff n k * bern n k t := by
  rw [eval_eq_sum h t]
  have e1 : ∑ i ∈ range (n + 1), q.coeff i * t ^ i =
      ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1), q.coeff i * (bq n k i * bern n k t) :=
    sum_congr rfl fun i hi => by
      rw [pow_eq_sum_bern (n := n) (by have := Finset.mem_range.1 hi; omega), mul_sum]
  rw [e1, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ n + 1 := by have := Finset.mem_range.1 hk; omega
  rw [beta, sum_mul, ← Finset.sum_range_add_sum_Ico _ hk']
  have h0 : ∑ i ∈ Ico (k + 1) (n + 1), q.coeff i * (bq n k i * bern n k t) = 0 :=
    sum_eq_zero fun i hi => by
      simp [bq, Nat.choose_eq_zero_of_lt (show k < i by have := (Finset.mem_Ico.1 hi).1; omega)]
  rw [h0, add_zero]
  exact sum_congr rfl fun i _ => by ring

/-! ### Interval side -/

theorem mem_hullUpTo {F : ℕ → Interval64} {y : ℝ} :
    ∀ n {k}, k ≤ n → y ∈ F k → y ∈ IPoly.hullUpTo F n
  | 0, k, hk, hy => by obtain rfl : k = 0 := by omega
                       exact hy
  | n + 1, k, hk, hy => by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact mem_hull_left (mem_hullUpTo n (by omega) hy)
    · obtain rfl : k = n + 1 := by omega
      exact mem_hull_right hy

/-- Convex combinations stay in an interval. -/
theorem convex_mem {D : Interval64} {n : ℕ} {w y : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (h1 : ∑ k ∈ range (n + 1), w k = 1) (hy : ∀ k ≤ n, y k ∈ D) :
    ∑ k ∈ range (n + 1), w k * y k ∈ D := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 (hy 0 (Nat.zero_le n))
  refine mem_toSet_of_toE hl hh ?_ ?_
  · rcases RealFP.Quad.ereal_cases D.lo.toE with h | h | ⟨r, h⟩
    · rw [h]; exact bot_le
    · rw [h] at hl'; exact absurd hl' (by simp)
    · rw [h]; refine EReal.coe_le_coe_iff.2 ?_
      have hr : ∀ k ∈ range (n + 1), w k * r ≤ w k * y k := fun k hk => by
        have := (mem_toSet_iff_toE.1 (hy k (by have := Finset.mem_range.1 hk; omega))).1.2
        rw [h] at this
        exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.1 this) (hw k)
      have := sum_le_sum hr
      rwa [← sum_mul, h1, one_mul] at this
  · rcases RealFP.Quad.ereal_cases D.hi.toE with h | h | ⟨r, h⟩
    · rw [h] at hh'; exact absurd hh' (by simp)
    · rw [h]; exact le_top
    · rw [h]; refine EReal.coe_le_coe_iff.2 ?_
      have hr : ∀ k ∈ range (n + 1), w k * y k ≤ w k * r := fun k hk => by
        have := (mem_toSet_iff_toE.1 (hy k (by have := Finset.mem_range.1 hk; omega))).2.2
        rw [h] at this
        exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.1 this) (hw k)
      have := sum_le_sum hr
      rwa [← sum_mul, h1, one_mul] at this

theorem bernQ_mem (n k i : ℕ) : bq n k i ∈ ofRat (IPoly.bernQ n k i) := by
  have := mem_toSet_ofRat (IPoly.bernQ n k i)
  have e : ((IPoly.bernQ n k i : ℚ) : ℝ) = bq n k i := by
    simp [IPoly.bernQ, bq, choose_eq]
  rw [e] at this; exact this

theorem mem_bernCoeffF {c : ℕ → Interval64} {a : ℕ → ℝ} (h : ∀ i, a i ∈ c i) (n k : ℕ) :
    beta a n k ∈ IPoly.bernCoeffF c n k := by
  have g : ∀ m, (∑ i ∈ range m, bq n k i * a i) ∈
      (List.range m).foldl (fun acc i => acc + ofRat (IPoly.bernQ n k i) * c i) zeroI := by
    intro m
    induction m with
    | zero => simpa using RealFP.Mat.zeroI_mem
    | succ m ih =>
      rw [sum_range_succ, List.range_succ, List.foldl_append]
      exact Iv.add_mem ih (Iv.mem_mul (bernQ_mem n k m) (h m))
  exact g (k + 1)

/-- **Bernstein enclosure on `[0, 1]`.** -/
theorem mem_bern01 {P : IPoly} {q : ℝ[X]} (hP : Contains P q) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : q.eval t ∈ IPoly.bern01 P n := by
  have hN : ∀ k, IPoly.bernDeg P n + 1 ≤ k → q.coeff k = 0 := fun k hk =>
    coeff_zero_of_le hP (by unfold IPoly.bernDeg at hk; omega)
  rw [eval_eq_sum_bern hN t]
  show _ ∈ IPoly.hullUpTo (fun k => IPoly.bernCoeffF P.coeff (IPoly.bernDeg P n) k) (IPoly.bernDeg P n)
  simp_rw [mul_comm (beta _ _ _)]
  exact convex_mem (fun k => bern_nonneg _ k ht) (sum_bern _ t)
    fun k hk => mem_hullUpTo _ hk (mem_bernCoeffF (fun i => hP i) _ k)

/-! ### Boxes: the affine map `x = lo + (hi - lo) s` -/

theorem contains_affine {A W : Interval64} {a w : ℝ} (ha : a ∈ A) (hw : w ∈ W) :
    Contains #[A, W] (C a + C w * X) := fun k => by
  rcases k with _ | _ | k
  · simpa [IPoly.coeff] using ha
  · simpa [IPoly.coeff, coeff_C] using hw
  · simp [IPoly.coeff, Array.getD, coeff_X, coeff_C]; exact RealFP.Mat.zeroI_mem

theorem affine_cover {X : Interval64} {x : ℝ} (hx : x ∈ X) (hfl : Quad.finite X.lo = true)
    (hfh : Quad.finite X.hi = true) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ L : ℝ[X],
      Contains #[point X.lo, point X.hi - point X.lo] L ∧ L.eval s = x := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 hx
  rw [toE_eq_toReal (RealFP.Quad.finite_spec hfl).1 (RealFP.Quad.finite_spec hfl).2] at h1
  rw [toE_eq_toReal (RealFP.Quad.finite_spec hfh).1 (RealFP.Quad.finite_spec hfh).2] at h2
  have h1' : X.lo.toReal ≤ x := EReal.coe_le_coe_iff.1 h1
  have h2' : x ≤ X.hi.toReal := EReal.coe_le_coe_iff.1 h2
  have hc := contains_affine (RealFP.Quad.toReal_mem hfl)
    (Iv.sub_mem (RealFP.Quad.toReal_mem hfh) (RealFP.Quad.toReal_mem hfl))
  by_cases hw : X.hi.toReal - X.lo.toReal = 0
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, _, hc, ?_⟩
    simp only [eval_add, eval_C, eval_mul, eval_X, mul_zero, add_zero]; linarith
  · have hpos : 0 < X.hi.toReal - X.lo.toReal := lt_of_le_of_ne (by linarith) (Ne.symm hw)
    refine ⟨(x - X.lo.toReal) / (X.hi.toReal - X.lo.toReal),
      ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩, _, hc, ?_⟩
    simp only [eval_add, eval_C, eval_mul, eval_X]
    field_simp; ring

/-- **Bernstein enclosure on a box `X`.** -/
theorem mem_bernOn {P : IPoly} {q : ℝ[X]} (hP : Contains P q) (n : ℕ) {X : Interval64} {x : ℝ}
    (hx : x ∈ X) : q.eval x ∈ IPoly.bernOn P X n := by
  unfold IPoly.bernOn
  split_ifs with hf
  · simp only [Bool.and_eq_true] at hf
    obtain ⟨s, hs, L, hL, e⟩ := affine_cover hx hf.1 hf.2
    have := mem_bern01 (contains_comp hP hL) n hs
    rwa [eval_comp, e] at this
  · exact mem_eval hP hx

/-- Subdivision. -/
theorem mem_bernRange {P : IPoly} {q : ℝ[X]} (hP : Contains P q) (n fuel : ℕ) :
    ∀ {X : Interval64} {x : ℝ}, x ∈ X → q.eval x ∈ IPoly.bernRange P n fuel X := by
  induction fuel with
  | zero => intro X x hx; exact mem_bernOn hP n hx
  | succ k ih =>
    intro X x hx
    rcases bisect_cover hx with h | h
    · exact mem_hull_left (ih h)
    · exact mem_hull_right (ih h)

theorem checkAuxB_sound {P : IPoly} {q : ℝ[X]} (hP : Contains P q) (n : ℕ)
    {g : Interval64 → Bool} (fuel : ℕ) :
    ∀ {X : Interval64}, IPoly.checkAuxB P n g fuel X = true → ∀ {x : ℝ}, x ∈ X →
      ∃ R, g R = true ∧ q.eval x ∈ R := by
  induction fuel with
  | zero => intro X h x hx; exact ⟨_, h, mem_bernOn hP n hx⟩
  | succ k ih =>
    intro X h x hx
    simp only [IPoly.checkAuxB, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨_, h, mem_bernOn hP n hx⟩
    · rcases bisect_cover hx with hb | hb
      · exact ih h1 hb
      · exact ih h2 hb

/-- **Polynomial positivity** by Bernstein enclosures. -/
theorem lt_of_checkGtB {P : IPoly} {q : ℝ[X]} (hP : Contains P q) {c : Float} {X : Interval64}
    {n fuel : ℕ} (h : P.checkGtB c X n fuel = true) {x : ℝ} (hx : x ∈ X) :
    c.toReal < q.eval x := by
  simp only [IPoly.checkGtB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAuxB_sound hP n fuel h hx
  exact lt_of_lo hn hi hy (of_decide_eq_true hR)

theorem le_of_checkGeB {P : IPoly} {q : ℝ[X]} (hP : Contains P q) {c : Float} {X : Interval64}
    {n fuel : ℕ} (h : P.checkGeB c X n fuel = true) {x : ℝ} (hx : x ∈ X) :
    c.toReal ≤ q.eval x := by
  simp only [IPoly.checkGeB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAuxB_sound hP n fuel h hx
  exact le_of_lo hn hi hy (of_decide_eq_true hR)

/-! ### 2D (tensor) enclosures -/

theorem size_le_maxSizeL {Q : IPoly} : ∀ {l : List IPoly}, Q ∈ l → Q.size ≤ IPoly2.maxSizeL l
  | _ :: _, List.Mem.head _ => le_max_left _ _
  | _ :: _, List.Mem.tail _ h => le_trans (size_le_maxSizeL h) (le_max_right _ _)

theorem eval2R_eq_sum {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) (x y : ℝ) :
    eval2R x y p = ∑ j ∈ range P.size, (p.coeff j).eval x * y ^ j := by
  unfold eval2R
  conv_lhs => rw [eq_sum_range (fun j hj => coeff2_zero hP hj)]
  simp [eval_finsetSum]

theorem coeff_sumCX (c : ℕ → ℝ) (M j : ℕ) :
    (∑ i ∈ range M, C (c i) * X ^ i : ℝ[X]).coeff j = if j < M then c j else 0 := by
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- **Tensor Bernstein enclosure on a box `X × Y`.** -/
theorem mem_bern2On {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) (n m : ℕ)
    {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    eval2R x y p ∈ IPoly2.bern2On P X Y n m := by
  unfold IPoly2.bern2On
  split_ifs with hf
  · dsimp only
    simp only [Bool.and_eq_true] at hf
    obtain ⟨s, hs, L, hL, e⟩ := affine_cover hx hf.1 hf.2
    set Q : IPoly2 := P.map fun Pj => Pj.comp #[point X.lo, point X.hi - point X.lo] with hQdef
    set N := max n (IPoly2.maxSize Q - 1) with hN
    have hQs : Q.size = P.size := by simp [hQdef]
    have hQc : ∀ j < P.size, Q.coeff j = (P.coeff j).comp #[point X.lo, point X.hi - point X.lo] :=
      fun j hj => by simp [hQdef, IPoly2.coeff, Array.getD, hj]
    have hcq : ∀ j < P.size, Contains (Q.coeff j) ((p.coeff j).comp L) := fun j hj => by
      rw [hQc j hj]; exact contains_comp (hP j) hL
    have hsz : ∀ j < P.size, (Q.coeff j).size ≤ N + 1 := fun j hj => by
      have hmem : Q.coeff j ∈ Q.toList := by
        simp only [IPoly2.coeff, Array.getD, show j < Q.size by omega, ↓reduceDIte]
        exact Array.getElem_mem_toList _
      have := size_le_maxSizeL hmem
      simp only [IPoly2.maxSize] at hN; omega
    -- p(x, y) = Σ_k B_k(s) r_k(y)
    set b : ℕ → ℕ → ℝ := fun k j => beta ((p.coeff j).comp L).coeff N k with hb
    have hrep : eval2R x y p = ∑ k ∈ range (N + 1), bern N k s *
        (∑ j ∈ range P.size, C (b k j) * Polynomial.X ^ j : ℝ[X]).eval y := by
      rw [eval2R_eq_sum hP]
      have : ∀ j ∈ range P.size, (p.coeff j).eval x * y ^ j =
          ∑ k ∈ range (N + 1), bern N k s * (b k j * y ^ j) := fun j hj => by
        have hz : ∀ k, N + 1 ≤ k → ((p.coeff j).comp L).coeff k = 0 := fun k hk =>
          coeff_zero_of_le (hcq j (Finset.mem_range.1 hj)) (by
            have := hsz j (Finset.mem_range.1 hj); omega)
        rw [← e, ← eval_comp, eval_eq_sum_bern hz, sum_mul]
        exact sum_congr rfl fun k _ => by ring
      rw [sum_congr rfl this, sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_sum]; congr 1
      simp [eval_finsetSum]
    rw [hrep]
    refine convex_mem (fun k => bern_nonneg _ k hs) (sum_bern _ s) fun k hk =>
      mem_hullUpTo _ hk ?_
    refine mem_bernOn ?_ m hy
    refine contains_ofFn (fun j hj => ?_) (fun j hj => ?_)
    · rw [hQs] at hj
      rw [coeff_sumCX, ite_eq_left hj]; exact mem_bernCoeffF (fun i => hcq j hj i) N k
    · rw [hQs] at hj
      rw [coeff_sumCX, ite_eq_right (by omega)]
  · exact mem_eval2 hP hx hy

theorem checkAux2B_sound {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) (n m : ℕ)
    {g : Interval64 → Bool} (fuel : ℕ) :
    ∀ {X Y : Interval64}, IPoly2.checkAux2B P n m g fuel X Y = true →
      ∀ {x y : ℝ}, x ∈ X → y ∈ Y → ∃ R, g R = true ∧ eval2R x y p ∈ R := by
  induction fuel with
  | zero => intro X Y h x y hx hy; exact ⟨_, h, mem_bern2On hP n m hx hy⟩
  | succ k ih =>
    intro X Y h x y hx hy
    simp only [IPoly2.checkAux2B, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact ⟨_, h, mem_bern2On hP n m hx hy⟩
    · rcases bisect_cover hx with hbx | hbx <;> rcases bisect_cover hy with hby | hby
      · exact ih h1 hbx hby
      · exact ih h2 hbx hby
      · exact ih h3 hbx hby
      · exact ih h4 hbx hby

/-- **Bivariate polynomial positivity** by tensor Bernstein enclosures. -/
theorem lt_of_checkGt2B {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) {c : Float} {X Y : Interval64}
    {n m fuel : ℕ} (h : P.checkGt2B c X Y n m fuel = true) {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    c.toReal < eval2R x y p := by
  simp only [IPoly2.checkGt2B, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hv⟩ := checkAux2B_sound hP n m fuel h hx hy
  exact lt_of_lo hn hi hv (of_decide_eq_true hR)

end RealFP.Bern
