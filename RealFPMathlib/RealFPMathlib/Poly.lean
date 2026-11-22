/-
Soundness of interval polynomials (`Interval64.IPoly`, core file `Interval64/Poly.lean`).

* `Contains P p` : every coefficient of the real polynomial `p` lies in `P`.
* Evaluation: `mem_eval`, `mem_evalMV`, `mem_range`.
* Arithmetic: `contains_add`, `contains_neg`, `contains_sub`, `contains_smul`, `contains_mul`,
  `contains_deriv`, `contains_integ` (with `derivative_integPoly`), `contains_comp`,
  `contains_shift`.
* Sign certificates: `le_of_checkGe`, `lt_of_checkGt`, `ge_of_checkLe`, `gt_of_checkLt`.
* Bivariate: `Contains2`, `mem_eval2`, `le_of_checkGe2`, `lt_of_checkGt2`.
-/
import RealFPMathlib.Matrix
import RealFPMathlib.IntervalDeriv
import Interval64.Poly
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Interval64 Interval64.Mat Polynomial Finset

noncomputable section

namespace RealFP.Poly

/-! ### Basic facts -/

theorem mem_zeroI_iff {x : ℝ} : x ∈ Interval64.Mat.zeroI ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 h
    change (0 : Float).toE ≤ _ at h1; change _ ≤ (0 : Float).toE at h2
    rw [toE_zero] at h1 h2
    exact le_antisymm (by exact_mod_cast h2) (by exact_mod_cast h1)
  · rintro rfl; exact RealFP.Mat.zeroI_mem

/-- The real polynomial `p` lies in the interval polynomial `P`. -/
def Contains (P : IPoly) (p : ℝ[X]) : Prop := ∀ k, p.coeff k ∈ P.coeff k

theorem coeff_getD_of_le {P : IPoly} {k : ℕ} (hk : P.size ≤ k) : P.coeff k = zeroI := by
  simp [IPoly.coeff, Array.getD, show ¬ k < P.size by omega]

theorem coeff_zero_of_le {P : IPoly} {p : ℝ[X]} (h : Contains P p) {k : ℕ} (hk : P.size ≤ k) :
    p.coeff k = 0 := by
  have := h k; rw [coeff_getD_of_le hk] at this; exact mem_zeroI_iff.1 this

theorem natDegree_lt {p : ℝ[X]} {N : ℕ} (hN : 0 < N) (h : ∀ k, N ≤ k → p.coeff k = 0) :
    p.natDegree < N := by
  have : p.natDegree ≤ N - 1 :=
    (natDegree_le_iff_coeff_eq_zero).2 fun k hk => h k (by
      have : (N - 1 : ℕ) < k := by exact_mod_cast hk
      omega)
  omega

/-- `p = Σ_{k < N} C (p_k) X^k` when the coefficients vanish from `N` on. -/
theorem eq_sum_range {R : Type*} [Semiring R] {p : R[X]} {N : ℕ} (h : ∀ k, N ≤ k → p.coeff k = 0) :
    p = ∑ k ∈ range N, C (p.coeff k) * X ^ k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · ext k; simp [h k (Nat.zero_le _)]
  · have : p.natDegree < N := by
      have : p.natDegree ≤ N - 1 :=
        (natDegree_le_iff_coeff_eq_zero).2 fun k hk => h k (by
          have : (N - 1 : ℕ) < k := by exact_mod_cast hk
          omega)
      omega
    exact as_sum_range_C_mul_X_pow' p this

theorem eval_eq_sum {p : ℝ[X]} {N : ℕ} (h : ∀ k, N ≤ k → p.coeff k = 0) (x : ℝ) :
    p.eval x = ∑ k ∈ range N, p.coeff k * x ^ k := by
  conv_lhs => rw [eq_sum_range h]
  simp [eval_finsetSum]

theorem coeff_ofFn {m : ℕ} {f : ℕ → Interval64} {k : ℕ} :
    (IPoly.ofFn m f).coeff k = if k < m then f k else zeroI := by
  by_cases hk : k < m
  · simp [IPoly.coeff, IPoly.ofFn, Array.getD, hk]
  · simp [IPoly.coeff, IPoly.ofFn, Array.getD, hk]

theorem size_ofFn {m : ℕ} {f : ℕ → Interval64} : (IPoly.ofFn m f).size = m := by
  simp [IPoly.ofFn]

/-! ### Horner -/

theorem mem_hornerAux {c : ℕ → Interval64} {X : Interval64} {u : ℕ → ℝ} {x : ℝ} (hx : x ∈ X)
    (len : ℕ) : ∀ off, (∀ k < len, u (off + k) ∈ c (off + k)) →
      (∑ k ∈ range len, u (off + k) * x ^ k) ∈ IPoly.hornerAux c X off len := by
  induction len with
  | zero => intro off _; simpa [IPoly.hornerAux] using RealFP.Mat.zeroI_mem
  | succ n ih =>
    intro off hu
    rcases n with _ | m
    · simpa [IPoly.hornerAux] using hu 0 (by omega)
    · rw [sum_range_succ']
      have ih' := ih (off + 1) (fun k hk => by
        have := hu (k + 1) (by omega); rwa [show off + (k + 1) = off + 1 + k by omega] at this)
      have e : ∑ k ∈ range (m + 1), u (off + (k + 1)) * x ^ (k + 1) =
          x * ∑ k ∈ range (m + 1), u (off + 1 + k) * x ^ k := by
        rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
        rw [show off + (k + 1) = off + 1 + k by omega]; ring
      rw [e]
      simp only [Nat.add_zero, pow_zero, mul_one]
      rw [add_comm (x * _), IPoly.hornerAux]
      exact Iv.add_mem (hu 0 (by omega)) (Iv.mem_mul hx ih')

theorem mem_eval {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {X : Interval64} {x : ℝ}
    (hx : x ∈ X) : p.eval x ∈ P.eval X := by
  rw [eval_eq_sum (fun k hk => coeff_zero_of_le hP hk)]
  have := mem_hornerAux (c := P.coeff) (u := p.coeff) hx P.size 0 (fun k _ => by
    simpa using hP k)
  show _ ∈ IPoly.hornerAux P.coeff X 0 P.size
  simpa using this

/-! ### Arithmetic -/

theorem contains_ofFn {m : ℕ} {f : ℕ → Interval64} {p : ℝ[X]}
    (hin : ∀ k < m, p.coeff k ∈ f k) (hout : ∀ k, m ≤ k → p.coeff k = 0) :
    Contains (IPoly.ofFn m f) p := by
  intro k
  rw [coeff_ofFn]
  split_ifs with hk
  · exact hin k hk
  · rw [hout k (by omega)]; exact RealFP.Mat.zeroI_mem

theorem contains_add {P Q : IPoly} {p q : ℝ[X]} (hP : Contains P p) (hQ : Contains Q q) :
    Contains (P.add Q) (p + q) :=
  contains_ofFn (fun k _ => by rw [coeff_add]; exact Iv.add_mem (hP k) (hQ k))
    (fun k hk => by
      rw [coeff_add, coeff_zero_of_le hP (by omega), coeff_zero_of_le hQ (by omega), add_zero])

theorem contains_sub {P Q : IPoly} {p q : ℝ[X]} (hP : Contains P p) (hQ : Contains Q q) :
    Contains (P.sub Q) (p - q) :=
  contains_ofFn (fun k _ => by rw [coeff_sub]; exact Iv.sub_mem (hP k) (hQ k))
    (fun k hk => by
      rw [coeff_sub, coeff_zero_of_le hP (by omega), coeff_zero_of_le hQ (by omega), sub_zero])

theorem contains_neg {P : IPoly} {p : ℝ[X]} (hP : Contains P p) : Contains P.neg (-p) := by
  intro k
  rw [coeff_neg]
  by_cases hk : k < P.size
  · have : P.neg.coeff k = -(P.coeff k) := by
      simp [IPoly.neg, IPoly.coeff, Array.getD, hk]; rfl
    rw [this]; exact mem_neg (hP k)
  · have : P.neg.coeff k = zeroI := by simp [IPoly.neg, IPoly.coeff, Array.getD, hk]
    rw [this, coeff_zero_of_le hP (by omega), neg_zero]; exact RealFP.Mat.zeroI_mem

theorem contains_smul {A : Interval64} {a : ℝ} (ha : a ∈ A) {P : IPoly} {p : ℝ[X]}
    (hP : Contains P p) : Contains (IPoly.smul A P) (C a * p) :=
  contains_ofFn (fun k _ => by rw [coeff_C_mul]; exact Iv.mem_mul ha (hP k))
    (fun k hk => by rw [coeff_C_mul, coeff_zero_of_le hP hk, mul_zero])

theorem contains_mul {P Q : IPoly} {p q : ℝ[X]} (hP : Contains P p) (hQ : Contains Q q) :
    Contains (P.mul Q) (p * q) := by
  refine contains_ofFn (fun k _ => ?_) (fun k hk => ?_)
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j)]
    exact RealFP.Mat.mem_idot (k + 1) (fun i _ => hP i) (fun i _ => hQ (k - i))
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    unfold IPoly.mulSize at hk
    by_cases h1 : P.size ≤ ij.1
    · rw [coeff_zero_of_le hP h1, zero_mul]
    · have h2 : Q.size ≤ ij.2 := by split_ifs at hk with h <;> omega
      rw [coeff_zero_of_le hQ h2, mul_zero]

theorem contains_deriv {P : IPoly} {p : ℝ[X]} (hP : Contains P p) :
    Contains P.deriv (derivative p) := by
  refine contains_ofFn (fun k _ => ?_) (fun k hk => ?_)
  · rw [coeff_derivative]
    have hn := RealFP.natCast_mem (k + 1)
    push_cast at hn
    exact Iv.mem_mul (hP (k + 1)) hn
  · rw [coeff_derivative, coeff_zero_of_le hP (by omega), zero_mul]

/-- Real antiderivative `Σ_{k < N} p_k / (k + 1) X^(k+1)` (constant term `0`). -/
def integPoly (p : ℝ[X]) (N : ℕ) : ℝ[X] := ∑ k ∈ range N, C (p.coeff k / (k + 1)) * X ^ (k + 1)

theorem coeff_integPoly (p : ℝ[X]) (N j : ℕ) :
    (integPoly p N).coeff j = if j = 0 then 0 else if j - 1 < N then p.coeff (j - 1) / j else 0 := by
  rw [integPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rcases j with _ | i
  · simp
  · simp only [Nat.add_right_cancel_iff, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Finset.sum_ite_eq, Finset.mem_range]
    push_cast; rfl

theorem derivative_integPoly {p : ℝ[X]} {N : ℕ} (h : ∀ k, N ≤ k → p.coeff k = 0) :
    derivative (integPoly p N) = p := by
  rw [integPoly, derivative_sum]
  conv_rhs => rw [eq_sum_range h]
  refine sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 2
  push_cast
  field_simp

theorem contains_integ {P : IPoly} {p : ℝ[X]} (hP : Contains P p) :
    Contains P.integ (integPoly p P.size) := by
  refine contains_ofFn (fun k hk => ?_) (fun k hk => ?_)
  · rw [coeff_integPoly]
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte]; exact RealFP.Mat.zeroI_mem
    · simp only [h0, ↓reduceIte, show k - 1 < P.size by omega]
      have hr := RealFP.ratCoe_mem (1 / (k : ℚ))
      push_cast at hr
      rw [show p.coeff (k - 1) / (k : ℝ) = p.coeff (k - 1) * (1 / (k : ℝ)) by ring]
      exact Iv.mem_mul (hP (k - 1)) hr
  · rw [coeff_integPoly]
    simp [show ¬ k - 1 < P.size by omega]

theorem contains_single {A : Interval64} {a : ℝ} (ha : a ∈ A) : Contains #[A] (C a) :=
  fun k => by
    rcases k with _ | k
    · simpa [IPoly.coeff] using ha
    · simp [IPoly.coeff, Array.getD]; exact RealFP.Mat.zeroI_mem

theorem contains_empty : Contains #[] (0 : ℝ[X]) := fun k => by
  simp [IPoly.coeff, Array.getD]; exact RealFP.Mat.zeroI_mem

theorem contains_compAux {P Q : IPoly} {u : ℕ → ℝ} {q : ℝ[X]} (hQ : Contains Q q)
    (len : ℕ) : ∀ off, (∀ k < len, u (off + k) ∈ P.coeff (off + k)) →
      Contains (IPoly.compAux P Q off len) (∑ k ∈ range len, C (u (off + k)) * q ^ k) := by
  induction len with
  | zero => intro off _; simpa [IPoly.compAux] using contains_empty
  | succ n ih =>
    intro off hu
    rcases n with _ | m
    · simpa [IPoly.compAux] using contains_single (hu 0 (by omega))
    · rw [sum_range_succ']
      have ih' := ih (off + 1) (fun k hk => by
        have := hu (k + 1) (by omega); rwa [show off + (k + 1) = off + 1 + k by omega] at this)
      have e : ∑ k ∈ range (m + 1), C (u (off + (k + 1))) * q ^ (k + 1) =
          q * ∑ k ∈ range (m + 1), C (u (off + 1 + k)) * q ^ k := by
        rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
        rw [show off + (k + 1) = off + 1 + k by omega]; ring
      rw [e]
      simp only [Nat.add_zero, pow_zero, mul_one]
      rw [add_comm (q * _), IPoly.compAux]
      exact contains_add (contains_single (hu 0 (by omega))) (contains_mul hQ ih')

theorem contains_comp {P Q : IPoly} {p q : ℝ[X]} (hP : Contains P p) (hQ : Contains Q q) :
    Contains (P.comp Q) (p.comp q) := by
  have e : p.comp q = ∑ k ∈ range P.size, C (p.coeff k) * q ^ k := by
    conv_lhs => rw [eq_sum_range (fun k hk => coeff_zero_of_le hP hk)]
    simp [Polynomial.sum_comp]
  rw [e]
  have := contains_compAux (P := P) (u := p.coeff) hQ P.size 0 (fun k _ => by simpa using hP k)
  show Contains (IPoly.compAux P Q 0 P.size) _
  simpa using this

theorem contains_lin {A : Interval64} {a : ℝ} (ha : a ∈ A) :
    Contains #[A, ⟨1, 1⟩] (X + C a) := fun k => by
  rcases k with _ | _ | k
  · simpa [IPoly.coeff] using ha
  · simpa [IPoly.coeff] using RealFP.mem_one
  · simp [IPoly.coeff, Array.getD, coeff_X]; exact RealFP.Mat.zeroI_mem

/-- `shift P A` encloses `p(x + a)` for `a ∈ A`. -/
theorem contains_shift {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {A : Interval64} {a : ℝ}
    (ha : a ∈ A) : Contains (P.shift A) (p.comp (X + C a)) :=
  contains_comp hP (contains_lin ha)

/-! ### Mean-value form, ranges, sign certificates -/

theorem toE_eq_toReal {f : Float} (hn : f.isNaN = false) (hi : f.isInf = false) :
    f.toE = (f.toReal : EReal) := by
  have h := RealFP.Mat.toReal_mem_point hn hi
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 h
  exact le_antisymm h1 h2

theorem mem_evalMV {P dP : IPoly} {p : ℝ[X]} (hP : Contains P p) (hD : Contains dP (derivative p))
    {X : Interval64} {x : ℝ} (hx : x ∈ X) : p.eval x ∈ IPoly.evalMV P dP X := by
  unfold IPoly.evalMV
  simp only
  split
  · exact mem_eval hP hx
  · rename_i hinf
    have hinf' : (mid X).isInf = false := by simpa using hinf
    obtain ⟨hmn, hm1, hm2⟩ := mid_spec hx
    obtain ⟨⟨hl, -⟩, ⟨hh, -⟩⟩ := mem_toSet_iff_toE.1 hx
    set m := mid X with hm
    have hmr : m.toReal ∈ point m := RealFP.Mat.toReal_mem_point hmn hinf'
    have hmX : m.toReal ∈ X := by
      rw [toE_eq_toReal hmn hinf'] at hm1 hm2
      exact mem_toSet_of_toE hl hh hm1 hm2
    refine mem_intersect (mem_eval hP hx) ?_
    obtain ⟨d, hd, he⟩ := mvt_uIcc (φ := fun t => p.eval t) (S := fun d => d ∈ dP.eval X)
      (a := m.toReal) (b := x) (fun t ht =>
        ⟨(derivative p).eval t, mem_eval hD (seg_mem hx hmX (Set.uIcc_comm m.toReal x ▸ ht)),
          Polynomial.hasDerivAt p t⟩)
    have : p.eval x = p.eval m.toReal + d * (x - m.toReal) := by linarith
    rw [this]
    exact Iv.add_mem (mem_eval hP hmr) (Iv.mem_mul hd (Iv.sub_mem hx hmr))

theorem mem_rangeAux {P dP : IPoly} {p : ℝ[X]} (hP : Contains P p)
    (hD : Contains dP (derivative p)) (fuel : ℕ) :
    ∀ {X : Interval64} {x : ℝ}, x ∈ X → p.eval x ∈ IPoly.rangeAux P dP fuel X := by
  induction fuel with
  | zero => intro X x hx; exact mem_evalMV hP hD hx
  | succ n ih =>
    intro X x hx
    rcases bisect_cover hx with h | h
    · exact mem_hull_left (ih h)
    · exact mem_hull_right (ih h)

/-- `range P X fuel` encloses `p x` for all `x ∈ X`. -/
theorem mem_range {P : IPoly} {p : ℝ[X]} (hP : Contains P p) (fuel : ℕ) {X : Interval64}
    {x : ℝ} (hx : x ∈ X) : p.eval x ∈ IPoly.range P X fuel :=
  mem_rangeAux hP (contains_deriv hP) fuel hx

theorem checkAux_sound {P dP : IPoly} {p : ℝ[X]} (hP : Contains P p)
    (hD : Contains dP (derivative p)) {g : Interval64 → Bool} (fuel : ℕ) :
    ∀ {X : Interval64}, IPoly.checkAux P dP g fuel X = true → ∀ {x : ℝ}, x ∈ X →
      ∃ R, g R = true ∧ p.eval x ∈ R := by
  induction fuel with
  | zero => intro X h x hx; exact ⟨_, h, mem_evalMV hP hD hx⟩
  | succ n ih =>
    intro X h x hx
    simp only [IPoly.checkAux, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨_, h, mem_evalMV hP hD hx⟩
    · rcases bisect_cover hx with hb | hb
      · exact ih h1 hb
      · exact ih h2 hb

theorem le_of_lo {c : Float} (hcn : c.isNaN = false) (hci : c.isInf = false) {R : Interval64}
    {y : ℝ} (hy : y ∈ R) (h : c ≤ R.lo) : c.toReal ≤ y := by
  obtain ⟨⟨hl, hl'⟩, -⟩ := mem_toSet_iff_toE.1 hy
  have := (float_le_iff_toE hcn hl).1 h
  rw [toE_eq_toReal hcn hci] at this
  exact EReal.coe_le_coe_iff.1 (le_trans this hl')

theorem lt_of_lo {c : Float} (hcn : c.isNaN = false) (hci : c.isInf = false) {R : Interval64}
    {y : ℝ} (hy : y ∈ R) (h : c < R.lo) : c.toReal < y := by
  obtain ⟨⟨hl, hl'⟩, -⟩ := mem_toSet_iff_toE.1 hy
  have := (float_lt_iff_toE hcn hl).1 h
  rw [toE_eq_toReal hcn hci] at this
  exact EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le this hl')

theorem ge_of_hi {c : Float} (hcn : c.isNaN = false) (hci : c.isInf = false) {R : Interval64}
    {y : ℝ} (hy : y ∈ R) (h : R.hi ≤ c) : y ≤ c.toReal := by
  obtain ⟨-, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have := (float_le_iff_toE hh hcn).1 h
  rw [toE_eq_toReal hcn hci] at this
  exact EReal.coe_le_coe_iff.1 (le_trans hh' this)

theorem gt_of_hi {c : Float} (hcn : c.isNaN = false) (hci : c.isInf = false) {R : Interval64}
    {y : ℝ} (hy : y ∈ R) (h : R.hi < c) : y < c.toReal := by
  obtain ⟨-, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have := (float_lt_iff_toE hh hcn).1 h
  rw [toE_eq_toReal hcn hci] at this
  exact EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt hh' this)

/-- **Polynomial lower bound.** -/
theorem le_of_checkGe {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {c : Float} {X : Interval64}
    {fuel : ℕ} (h : P.checkGe c X fuel = true) {x : ℝ} (hx : x ∈ X) : c.toReal ≤ p.eval x := by
  simp only [IPoly.checkGe, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAux_sound hP (contains_deriv hP) fuel h hx
  exact le_of_lo hn hi hy (of_decide_eq_true hR)

theorem lt_of_checkGt {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {c : Float} {X : Interval64}
    {fuel : ℕ} (h : P.checkGt c X fuel = true) {x : ℝ} (hx : x ∈ X) : c.toReal < p.eval x := by
  simp only [IPoly.checkGt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAux_sound hP (contains_deriv hP) fuel h hx
  exact lt_of_lo hn hi hy (of_decide_eq_true hR)

theorem ge_of_checkLe {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {c : Float} {X : Interval64}
    {fuel : ℕ} (h : P.checkLe c X fuel = true) {x : ℝ} (hx : x ∈ X) : p.eval x ≤ c.toReal := by
  simp only [IPoly.checkLe, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAux_sound hP (contains_deriv hP) fuel h hx
  exact ge_of_hi hn hi hy (of_decide_eq_true hR)

theorem gt_of_checkLt {P : IPoly} {p : ℝ[X]} (hP : Contains P p) {c : Float} {X : Interval64}
    {fuel : ℕ} (h : P.checkLt c X fuel = true) {x : ℝ} (hx : x ∈ X) : p.eval x < c.toReal := by
  simp only [IPoly.checkLt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hy⟩ := checkAux_sound hP (contains_deriv hP) fuel h hx
  exact gt_of_hi hn hi hy (of_decide_eq_true hR)

/-! ### Bivariate -/

/-- `p : ℝ[X][X]` (outer variable `y`, inner `x`) lies in `P`. -/
def Contains2 (P : IPoly2) (p : ℝ[X][X]) : Prop := ∀ j, Contains (P.coeff j) (p.coeff j)

/-- Value at `(x, y)`: `(p.eval (C y)).eval x` (Mathlib's `Polynomial.evalEval x y p`). -/
def eval2R (x y : ℝ) (p : ℝ[X][X]) : ℝ := (p.eval (C y)).eval x

theorem coeff2_zero {P : IPoly2} {p : ℝ[X][X]} (h : Contains2 P p) {j : ℕ} (hj : P.size ≤ j) :
    p.coeff j = 0 := by
  have hc := h j
  have : P.coeff j = #[] := by simp [IPoly2.coeff, Array.getD, show ¬ j < P.size by omega]
  rw [this] at hc
  ext k
  have := hc k
  simp only [IPoly.coeff, Array.getD] at this
  simpa using mem_zeroI_iff.1 (by simpa using this)

theorem mem_eval2 {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) {X Y : Interval64} {x y : ℝ}
    (hx : x ∈ X) (hy : y ∈ Y) : eval2R x y p ∈ P.eval2 X Y := by
  have e : eval2R x y p = ∑ j ∈ range P.size, (p.coeff j).eval x * y ^ j := by
    unfold eval2R
    conv_lhs => rw [eq_sum_range (fun j hj => coeff2_zero hP hj)]
    simp [eval_finsetSum]
  rw [e]
  have := mem_hornerAux (c := fun j => (P.coeff j).eval X) (u := fun j => (p.coeff j).eval x)
    hy P.size 0 (fun k _ => mem_eval (hP (0 + k)) hx)
  show _ ∈ IPoly.hornerAux _ Y 0 P.size
  simpa using this

theorem checkAux2_sound {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) {g : Interval64 → Bool}
    (fuel : ℕ) : ∀ {X Y : Interval64}, IPoly2.checkAux2 P g fuel X Y = true →
      ∀ {x y : ℝ}, x ∈ X → y ∈ Y → ∃ R, g R = true ∧ eval2R x y p ∈ R := by
  induction fuel with
  | zero => intro X Y h x y hx hy; exact ⟨_, h, mem_eval2 hP hx hy⟩
  | succ n ih =>
    intro X Y h x y hx hy
    simp only [IPoly2.checkAux2, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨_, h, mem_eval2 hP hx hy⟩
    · split at h
      · simp only [Bool.and_eq_true] at h
        rcases bisect_cover hx with hb | hb
        · exact ih h.1 hb hy
        · exact ih h.2 hb hy
      · simp only [Bool.and_eq_true] at h
        rcases bisect_cover hy with hb | hb
        · exact ih h.1 hx hb
        · exact ih h.2 hx hb

/-- **Bivariate lower bound** on a box. -/
theorem le_of_checkGe2 {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) {c : Float}
    {X Y : Interval64} {fuel : ℕ} (h : P.checkGe2 c X Y fuel = true) {x y : ℝ} (hx : x ∈ X)
    (hy : y ∈ Y) : c.toReal ≤ eval2R x y p := by
  simp only [IPoly2.checkGe2, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hv⟩ := checkAux2_sound hP fuel h hx hy
  exact le_of_lo hn hi hv (of_decide_eq_true hR)

theorem lt_of_checkGt2 {P : IPoly2} {p : ℝ[X][X]} (hP : Contains2 P p) {c : Float}
    {X Y : Interval64} {fuel : ℕ} (h : P.checkGt2 c X Y fuel = true) {x y : ℝ} (hx : x ∈ X)
    (hy : y ∈ Y) : c.toReal < eval2R x y p := by
  simp only [IPoly2.checkGt2, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, h⟩ := h
  obtain ⟨R, hR, hv⟩ := checkAux2_sound hP fuel h hx hy
  exact lt_of_lo hn hi hv (of_decide_eq_true hR)

end RealFP.Poly
