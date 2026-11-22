/-
Soundness of rigorous quadrature (`Interval64.Quad`, core file `Interval64/Quad.lean`).

* `integral_mem_polyIntegral` : `∫ x in a..b, p.eval x ∈ polyIntegral P A B`.
* `integral_mem_mul` : weighted-average lemma (`∫ φ ∈ E * Q` when `φ = e · w`, `e ∈ E`, `∫ w ∈ Q`).
* `integral_mem_cell0`, `integral_mem_cell1` : one cell.
* `integral_mem_quadAux`, `integral_mem_integrate` : adaptive bisection.
* `integral_mem_integrate0` / `integral_mem_integrate1` : for an interval extension `F` of `f`
  (and `D` of `f'`).
* `integral_mem_integrateE0` / `integral_mem_integrateE1` : for an `IExpr` (`f x = e.denote [x]`).
-/
import RealFPMathlib.Poly
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

open Interval64 Interval64.Quad Interval64.KF Set intervalIntegral MeasureTheory

noncomputable section

namespace RealFP.Quad

open RealFP.Poly RealFP.Mat

theorem ereal_cases (z : EReal) : z = ⊥ ∨ z = ⊤ ∨ ∃ r : ℝ, z = r := by
  induction z using EReal.rec <;> simp

/-- Weighted average: if `φ x = e x · w x` with `e x ∈ E`, `w ≥ 0`, `∫ w = K ∈ Q`, `K > 0`,
    then `∫ φ ∈ E * Q`. -/
theorem integral_mem_mul {c d K : ℝ} (hcd : c < d) {φ w : ℝ → ℝ} {E Q : Interval64}
    (hK : K ∈ Q) (hK0 : 0 < K) (hwK : ∫ x in c..d, w x = K) (hw0 : ∀ x ∈ Icc c d, 0 ≤ w x)
    (hφi : IntervalIntegrable φ volume c d) (hwi : IntervalIntegrable w volume c d)
    (hφ : ∀ x ∈ Icc c d, ∃ e ∈ E, φ x = e * w x) : (∫ x in c..d, φ x) ∈ E * Q := by
  obtain ⟨e0, he0, -⟩ := hφ c ⟨le_rfl, hcd.le⟩
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 he0
  set avg := (∫ x in c..d, φ x) / K with havg_def
  have hlow : E.lo.toE ≤ (avg : EReal) := by
    rcases ereal_cases E.lo.toE with h | h | ⟨r, h⟩
    · rw [h]; exact bot_le
    · rw [h] at hl'; exact absurd hl' (by simp)
    · rw [h]
      refine EReal.coe_le_coe_iff.2 ?_
      have hle : ∀ x ∈ Icc c d, r * w x ≤ φ x := fun x hx => by
        obtain ⟨e, he, hφx⟩ := hφ x hx
        have : (r : EReal) ≤ e := h ▸ (mem_toSet_iff_toE.1 he).1.2
        rw [hφx]; exact mul_le_mul_of_nonneg_right (EReal.coe_le_coe_iff.1 this) (hw0 x hx)
      have := integral_mono_on hcd.le (hwi.const_mul r) hφi hle
      rw [intervalIntegral.integral_const_mul, hwK] at this
      rw [havg_def, le_div_iff₀ hK0]; linarith
  have hupp : (avg : EReal) ≤ E.hi.toE := by
    rcases ereal_cases E.hi.toE with h | h | ⟨r, h⟩
    · rw [h] at hh'; exact absurd hh' (by simp)
    · rw [h]; exact le_top
    · rw [h]
      refine EReal.coe_le_coe_iff.2 ?_
      have hle : ∀ x ∈ Icc c d, φ x ≤ r * w x := fun x hx => by
        obtain ⟨e, he, hφx⟩ := hφ x hx
        have : (e : EReal) ≤ r := h ▸ (mem_toSet_iff_toE.1 he).2.2
        rw [hφx]; exact mul_le_mul_of_nonneg_right (EReal.coe_le_coe_iff.1 this) (hw0 x hx)
      have := integral_mono_on hcd.le hφi (hwi.const_mul r) hle
      rw [intervalIntegral.integral_const_mul, hwK] at this
      rw [havg_def, div_le_iff₀ hK0]; linarith
  have e : (∫ x in c..d, φ x) = avg * K := by rw [havg_def]; field_simp
  rw [e]
  exact Iv.mem_mul (mem_toSet_of_toE hl hh hlow hupp) hK

/-! ### Floats as reals -/

theorem finite_spec {x : Float} (h : finite x = true) : x.isNaN = false ∧ x.isInf = false := by
  simpa [finite] using h

theorem mem_box {lo hi : Float} (hlo : finite lo = true) (hhi : finite hi = true) {x : ℝ}
    (hx : x ∈ Icc lo.toReal hi.toReal) : x ∈ (⟨lo, hi⟩ : Interval64) := by
  obtain ⟨h1, h2⟩ := finite_spec hlo
  obtain ⟨h3, h4⟩ := finite_spec hhi
  refine mem_toSet_of_toE (I := ⟨lo, hi⟩) h1 h3 ?_ ?_
  · show lo.toE ≤ _; rw [toE_eq_toReal h1 h2]; exact EReal.coe_le_coe_iff.2 hx.1
  · show _ ≤ hi.toE; rw [toE_eq_toReal h3 h4]; exact EReal.coe_le_coe_iff.2 hx.2

theorem toReal_mem {x : Float} (h : finite x = true) : x.toReal ∈ point x :=
  toReal_mem_point (finite_spec h).1 (finite_spec h).2

/-- `mid [lo, hi]` is finite and lies between `lo` and `hi`. -/
theorem mid_finite {lo hi : Float} (hlo : finite lo = true) (hhi : finite hi = true)
    (hle : lo.toReal ≤ hi.toReal) :
    finite (mid ⟨lo, hi⟩) = true ∧ lo.toReal ≤ (mid ⟨lo, hi⟩).toReal ∧
      (mid ⟨lo, hi⟩).toReal ≤ hi.toReal := by
  obtain ⟨h1, h2⟩ := finite_spec hlo
  obtain ⟨h3, h4⟩ := finite_spec hhi
  obtain ⟨hm, hm1, hm2⟩ := mid_spec (mem_box hlo hhi ⟨le_rfl, hle⟩)
  change lo.toE ≤ _ at hm1; change _ ≤ hi.toE at hm2
  rw [toE_eq_toReal h1 h2] at hm1; rw [toE_eq_toReal h3 h4] at hm2
  have hmi : (mid ⟨lo, hi⟩).isInf = false := by
    cases hc : (mid ⟨lo, hi⟩).isInf
    · rfl
    · rcases (isInf_iff_toE.1 hc).1 with h | h <;> rw [h] at hm1 hm2 <;> simp at hm1 hm2
  rw [toE_eq_toReal hm hmi] at hm1 hm2
  exact ⟨by simp [finite, hm, hmi], EReal.coe_le_coe_iff.1 hm1, EReal.coe_le_coe_iff.1 hm2⟩

theorem half_mem : (1 / 2 : ℝ) ∈ half := by
  have := RealFP.ratCoe_mem (1 / 2); push_cast at this; exact this

/-! ### Cells -/

section
variable {f : ℝ → ℝ} {F : Interval64 → Interval64}

theorem integral_mem_cell0 (hF : ∀ X x, x ∈ X → f x ∈ F X) {lo hi : Float}
    (hlo : finite lo = true) (hhi : finite hi = true) (hle : lo.toReal ≤ hi.toReal)
    (hc : ContinuousOn f (Icc lo.toReal hi.toReal)) :
    (∫ x in lo.toReal..hi.toReal, f x) ∈ cell0 F lo hi := by
  show _ ∈ F ⟨lo, hi⟩ * (point hi - point lo)
  have hW : hi.toReal - lo.toReal ∈ point hi - point lo := Iv.sub_mem (toReal_mem hhi) (toReal_mem hlo)
  rcases hle.lt_or_eq with hlt | heq
  · have hK : (∫ _ in lo.toReal..hi.toReal, (1 : ℝ)) = hi.toReal - lo.toReal := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact integral_mem_mul (w := fun _ => 1) hlt hW (sub_pos.2 hlt) hK
      (fun _ _ => zero_le_one) (hc.intervalIntegrable_of_Icc hle) intervalIntegrable_const
      (fun x hx => ⟨f x, hF _ x (mem_box hlo hhi hx), (mul_one _).symm⟩)
  · have h0 : (∫ x in lo.toReal..hi.toReal, f x) = f lo.toReal * (hi.toReal - lo.toReal) := by
      rw [← heq, integral_same, sub_self, mul_zero]
    rw [h0]
    exact Iv.mem_mul (hF _ _ (mem_box hlo hhi ⟨le_rfl, hle⟩)) hW

/-- `∫_c^d (f x - f m) ∈ D * Q` on a half cell `[m, d]` (`φ = e · (x - m)`). -/
theorem half_right {f' : ℝ → ℝ} {DX Q : Interval64} {m d : ℝ} (hmd : m ≤ d)
    (hderiv : ∀ x ∈ Icc m d, HasDerivAt f (f' x) x) (hD : ∀ x ∈ Icc m d, f' x ∈ DX)
    (hQ : (d - m) ^ 2 / 2 ∈ Q) : (∫ x in m..d, (f x - f m)) ∈ DX * Q := by
  have hcont : ContinuousOn f (Icc m d) := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  rcases hmd.lt_or_eq with hlt | heq
  · refine integral_mem_mul (w := fun x => x - m) hlt hQ (by positivity) ?_
      (fun x hx => sub_nonneg.2 hx.1)
      ((hcont.intervalIntegrable_of_Icc hmd).sub intervalIntegrable_const)
      (intervalIntegrable_id.sub intervalIntegrable_const) (fun x hx => ?_)
    · rw [intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]; ring
    · obtain ⟨dd, hdd, he⟩ := mvt_uIcc (φ := f) (S := fun d => d ∈ DX) (a := m) (b := x)
        (fun t ht => by
          have ht' : t ∈ Icc m d := by
            rw [uIcc_of_le hx.1] at ht; exact ⟨ht.1, le_trans ht.2 hx.2⟩
          exact ⟨f' t, hD t ht', hderiv t ht'⟩)
      exact ⟨dd, hdd, he⟩
  · subst heq
    rw [integral_same, show (0 : ℝ) = f' m * ((m - m) ^ 2 / 2) by ring]
    exact Iv.mem_mul (hD m ⟨le_rfl, le_rfl⟩) hQ

/-- Left half `[c, m]`: `∫_c^m (f x - f m) ∈ (-D) * Q`. -/
theorem half_left {f' : ℝ → ℝ} {DX Q : Interval64} {c m : ℝ} (hcm : c ≤ m)
    (hderiv : ∀ x ∈ Icc c m, HasDerivAt f (f' x) x) (hD : ∀ x ∈ Icc c m, f' x ∈ DX)
    (hQ : (m - c) ^ 2 / 2 ∈ Q) : (∫ x in c..m, (f x - f m)) ∈ (-DX) * Q := by
  have hcont : ContinuousOn f (Icc c m) := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  rcases hcm.lt_or_eq with hlt | heq
  · refine integral_mem_mul (w := fun x => m - x) hlt hQ (by positivity) ?_
      (fun x hx => sub_nonneg.2 hx.2)
      ((hcont.intervalIntegrable_of_Icc hcm).sub intervalIntegrable_const)
      (intervalIntegrable_const.sub intervalIntegrable_id) (fun x hx => ?_)
    · rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]; ring
    · obtain ⟨dd, hdd, he⟩ := mvt_uIcc (φ := f) (S := fun d => d ∈ DX) (a := m) (b := x)
        (fun t ht => by
          have ht' : t ∈ Icc c m := by
            rw [uIcc_of_ge hx.2] at ht; exact ⟨le_trans hx.1 ht.1, ht.2⟩
          exact ⟨f' t, hD t ht', hderiv t ht'⟩)
      exact ⟨-dd, mem_neg hdd, by rw [he]; ring⟩
  · subst heq
    rw [integral_same, show (0 : ℝ) = -f' c * ((c - c) ^ 2 / 2) by ring]
    exact Iv.mem_mul (mem_neg (hD c ⟨le_rfl, le_rfl⟩)) hQ

theorem integral_mem_cell1 {f' : ℝ → ℝ} {D : Interval64 → Interval64}
    (hF : ∀ X x, x ∈ X → f x ∈ F X) (hD : ∀ X x, x ∈ X → f' x ∈ D X) {lo hi : Float}
    (hlo : finite lo = true) (hhi : finite hi = true) (hle : lo.toReal ≤ hi.toReal)
    (hderiv : ∀ x ∈ Icc lo.toReal hi.toReal, HasDerivAt f (f' x) x) :
    (∫ x in lo.toReal..hi.toReal, f x) ∈ cell1 F D lo hi := by
  have hcont : ContinuousOn f (Icc lo.toReal hi.toReal) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have h0 := integral_mem_cell0 hF hlo hhi hle hcont
  unfold cell1
  simp only
  split
  · exact h0
  · refine mem_intersect h0 ?_
    obtain ⟨hmf, hm1, hm2⟩ := mid_finite hlo hhi hle
    set m := mid (⟨lo, hi⟩ : Interval64)
    set a := lo.toReal; set b := hi.toReal; set r := m.toReal
    have hsplit : (∫ x in a..b, f x) = f r * (b - a) + (∫ x in r..b, (f x - f r)) +
        ∫ x in a..r, (f x - f r) := by
      rw [intervalIntegral.integral_sub (hcont.mono (Icc_subset_Icc hm1 le_rfl)
          |>.intervalIntegrable_of_Icc hm2) intervalIntegrable_const,
        intervalIntegral.integral_sub (hcont.mono (Icc_subset_Icc le_rfl hm2)
          |>.intervalIntegrable_of_Icc hm1) intervalIntegrable_const,
        intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul,
        ← integral_add_adjacent_intervals
          ((hcont.mono (Icc_subset_Icc le_rfl hm2)).intervalIntegrable_of_Icc hm1)
          ((hcont.mono (Icc_subset_Icc hm1 le_rfl)).intervalIntegrable_of_Icc hm2)]
      ring
    rw [hsplit]
    have hDX : ∀ x ∈ Icc a b, f' x ∈ D ⟨lo, hi⟩ := fun x hx => hD _ x (mem_box hlo hhi hx)
    have hr := toReal_mem hmf
    refine Iv.add_mem (Iv.add_mem ?_ ?_) ?_
    · exact Iv.mem_mul (hF _ _ hr) (Iv.sub_mem (toReal_mem hhi) (toReal_mem hlo))
    · refine half_right hm2 (fun x hx => hderiv x ⟨le_trans hm1 hx.1, hx.2⟩)
        (fun x hx => hDX x ⟨le_trans hm1 hx.1, hx.2⟩) ?_
      rw [show (b - r) ^ 2 / 2 = (b - r) ^ 2 * (1 / 2) by ring]
      exact Iv.mem_mul (mem_square (Iv.sub_mem (toReal_mem hhi) hr)) half_mem
    · refine half_left hm1 (fun x hx => hderiv x ⟨hx.1, le_trans hx.2 hm2⟩)
        (fun x hx => hDX x ⟨hx.1, le_trans hx.2 hm2⟩) ?_
      rw [show (r - a) ^ 2 / 2 = (r - a) ^ 2 * (1 / 2) by ring]
      exact Iv.mem_mul (mem_square (Iv.sub_mem hr (toReal_mem hlo))) half_mem

/-! ### Adaptive bisection -/

theorem integral_mem_quadAux {cell : Float → Float → Interval64} {a b : ℝ}
    (hcell : ∀ lo hi : Float, finite lo = true → finite hi = true → a ≤ lo.toReal →
      lo.toReal ≤ hi.toReal → hi.toReal ≤ b → (∫ x in lo.toReal..hi.toReal, f x) ∈ cell lo hi)
    (hc : ContinuousOn f (Icc a b)) (fuel : ℕ) :
    ∀ (tol lo hi : Float), finite lo = true → finite hi = true → a ≤ lo.toReal →
      lo.toReal ≤ hi.toReal → hi.toReal ≤ b →
      (∫ x in lo.toReal..hi.toReal, f x) ∈ quadAux cell fuel tol lo hi := by
  induction fuel with
  | zero => intro tol lo hi h1 h2 h3 h4 h5; exact hcell lo hi h1 h2 h3 h4 h5
  | succ n ih =>
    intro tol lo hi h1 h2 h3 h4 h5
    simp only [quadAux]
    split
    · exact hcell lo hi h1 h2 h3 h4 h5
    · obtain ⟨hmf, hm1, hm2⟩ := mid_finite h1 h2 h4
      rw [← integral_add_adjacent_intervals
        ((hc.mono (Icc_subset_Icc h3 (le_trans hm2 h5))).intervalIntegrable_of_Icc hm1)
        ((hc.mono (Icc_subset_Icc (le_trans h3 hm1) h5)).intervalIntegrable_of_Icc hm2)]
      exact Iv.add_mem (ih _ _ _ h1 hmf h3 hm1 (le_trans hm2 h5))
        (ih _ _ _ hmf h2 (le_trans h3 hm1) hm2 h5)

theorem integral_mem_integrate {cell : Float → Float → Interval64} {a b : Float}
    (hcell : ∀ lo hi : Float, finite lo = true → finite hi = true → a.toReal ≤ lo.toReal →
      lo.toReal ≤ hi.toReal → hi.toReal ≤ b.toReal →
      (∫ x in lo.toReal..hi.toReal, f x) ∈ cell lo hi)
    (hc : ContinuousOn f (uIcc a.toReal b.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, f x) ∈ integrate cell a b tol fuel := by
  unfold integrate
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    obtain ⟨ha1, ha2⟩ := finite_spec ha
    obtain ⟨hb1, hb2⟩ := finite_spec hb
    have hle : a.toReal ≤ b.toReal := by
      have := (float_le_iff_toE ha1 hb1).1 hab
      rw [toE_eq_toReal ha1 ha2, toE_eq_toReal hb1 hb2] at this
      exact EReal.coe_le_coe_iff.1 this
    rw [uIcc_of_le hle] at hc
    exact integral_mem_quadAux hcell hc fuel tol a b ha hb le_rfl hle le_rfl
  · exact mem_toSet_whole _

/-- **Zeroth-order quadrature** for an interval extension `F` of a continuous `f`. -/
theorem integral_mem_integrate0 (hF : ∀ X x, x ∈ X → f x ∈ F X) {a b : Float}
    (hc : ContinuousOn f (uIcc a.toReal b.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, f x) ∈ integrate (cell0 F) a b tol fuel := by
  refine integral_mem_integrate (fun lo hi h1 h2 h3 h4 h5 => integral_mem_cell0 hF h1 h2 h4 ?_) hc
    tol fuel
  refine hc.mono fun x hx => ?_
  rw [uIcc_of_le (le_trans h3 (le_trans h4 h5))]
  exact ⟨le_trans h3 hx.1, le_trans hx.2 h5⟩

/-- **Second-order quadrature** from enclosures `F` of `f` and `D` of `f'`. -/
theorem integral_mem_integrate1 {f' : ℝ → ℝ} {D : Interval64 → Interval64}
    (hF : ∀ X x, x ∈ X → f x ∈ F X) (hD : ∀ X x, x ∈ X → f' x ∈ D X) {a b : Float}
    (hderiv : ∀ x ∈ uIcc a.toReal b.toReal, HasDerivAt f (f' x) x) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, f x) ∈ integrate (cell1 F D) a b tol fuel := by
  have hc : ContinuousOn f (uIcc a.toReal b.toReal) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  refine integral_mem_integrate (fun lo hi h1 h2 h3 h4 h5 =>
    integral_mem_cell1 hF hD h1 h2 h4 fun x hx => hderiv x ?_) hc tol fuel
  rw [uIcc_of_le (le_trans h3 (le_trans h4 h5))]
  exact ⟨le_trans h3 hx.1, le_trans hx.2 h5⟩

end

/-! ### `IExpr` integrands -/

theorem evalI_ext (e : IExpr) : ∀ X x, x ∈ X → e.denote [x] ∈ evalI [X] e := fun _ _ hx =>
  eval_sound (List.Forall₂.cons hx List.Forall₂.nil) e

theorem integral_mem_integrateE0 (e : IExpr) {a b : Float}
    (hc : ContinuousOn (fun x => e.denote [x]) (uIcc a.toReal b.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, e.denote [x]) ∈ integrateE0 e a b tol fuel :=
  integral_mem_integrate0 (evalI_ext e) hc tol fuel

theorem integral_mem_integrateE1 (e : IExpr) {a b : Float}
    (hdom : ∀ x ∈ uIcc a.toReal b.toReal, Dom [x] e) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, e.denote [x]) ∈ integrateE1 e a b tol fuel := by
  refine integral_mem_integrate1 (f' := fun x => (e.diff 0).denote [x]) (evalI_ext e)
    (evalI_ext (e.diff 0)) (fun x hx => ?_) tol fuel
  have := hasDerivAt_denote (xs := [x]) (i := 0) (by simp) e (hdom x hx)
  simpa using this

/-! ### Polynomials -/

theorem integral_mem_polyIntegral {P : IPoly} {p : Polynomial ℝ} (hP : Contains P p)
    {A B : Interval64} {a b : ℝ} (ha : a ∈ A) (hb : b ∈ B) :
    (∫ x in a..b, p.eval x) ∈ polyIntegral P A B := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t => (integPoly p P.size).eval t) (p.eval x) x :=
    fun x _ => by
      have := Polynomial.hasDerivAt (integPoly p P.size) x
      rwa [derivative_integPoly (fun k hk => coeff_zero_of_le hP hk)] at this
  rw [integral_eq_sub_of_hasDerivAt hd ((Polynomial.continuous p).intervalIntegrable _ _)]
  exact Iv.sub_mem (mem_eval (contains_integ hP) hb) (mem_eval (contains_integ hP) ha)

end RealFP.Quad
