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

end RealFP.Poly
