/-
Pure linear algebra behind the interval positive-definiteness certificate
(`RealFPMathlib.Matrix`):

* `posDef_of_diagDom` : a real symmetric matrix with `Σ_{l ≠ i} |B i l| < B i i` for all `i`
  (strict diagonal dominance, positive diagonal) is positive definite.
* `posDef_of_posDef_congr` : if `X * A * Xᵀ` is positive definite (any square `X`) and `A`
  is symmetric, then `A` is positive definite.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix BigOperators Finset

namespace RealFP.Mat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Off-diagonal absolute row sum `Σ_{l ≠ i} |B i l|`, written as a full sum. -/
noncomputable def offSum (B : Matrix n n ℝ) (i : n) : ℝ :=
  ∑ l, if l = i then 0 else |B i l|

omit [DecidableEq n] in
theorem quad_eq (B : Matrix n n ℝ) (x : n → ℝ) :
    star x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ l, x i * B i l * x l := by
  simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

omit [Fintype n] in
theorem term_ge (B : Matrix n n ℝ) (x : n → ℝ) (i l : n) :
    2 * (if l = i then B i i * x i ^ 2 else 0) -
        (if l = i then 0 else |B i l|) * x i ^ 2 - (if l = i then 0 else |B i l|) * x l ^ 2
      ≤ 2 * (x i * B i l * x l) := by
  by_cases h : l = i
  · subst h; simp only [ite_true]; nlinarith
  · simp only [h, ite_false, mul_zero, zero_sub]
    have h1 : -(|B i l| * |x i * x l|) ≤ B i l * (x i * x l) := by
      have := neg_abs_le (B i l * (x i * x l))
      rwa [abs_mul] at this
    have h2 : 2 * |x i * x l| ≤ x i ^ 2 + x l ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x i| - |x l|), sq_abs (x i), sq_abs (x l)]
    have h3 : 0 ≤ |B i l| := abs_nonneg _
    have e : x i * B i l * x l = B i l * (x i * x l) := by ring
    rw [e]; nlinarith

theorem posDef_of_diagDom {B : Matrix n n ℝ} (hs : Bᵀ = B)
    (h : ∀ i, offSum B i < B i i) : B.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hs
  rw [quad_eq]
  have hsym : ∀ i l, B l i = B i l := fun i l => by
    have := congrFun (congrFun hs i) l; simpa [transpose_apply] using this
  set c : n → n → ℝ := fun i l => if l = i then 0 else |B i l| with hc
  have S12 : ∑ i, ∑ l, c i l * x l ^ 2 = ∑ i, ∑ l, c i l * x i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hc]
    by_cases hil : i = l
    · subst hil; simp
    · simp only [hil, Ne.symm hil, ite_false]; rw [hsym]
  have E1 : ∑ i, ∑ l, (2 * (if l = i then B i i * x i ^ 2 else 0) - c i l * x i ^ 2 -
      c i l * x l ^ 2) = 2 * ∑ i, B i i * x i ^ 2 - ∑ i, ∑ l, c i l * x i ^ 2 -
        ∑ i, ∑ l, c i l * x l ^ 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  have E3 : ∑ i, (B i i - offSum B i) * x i ^ 2 = ∑ i, B i i * x i ^ 2 -
      ∑ i, ∑ l, c i l * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [offSum, sub_mul, Finset.sum_mul]
  have hle : ∑ i, ∑ l, (2 * (if l = i then B i i * x i ^ 2 else 0) - c i l * x i ^ 2 -
      c i l * x l ^ 2) ≤ ∑ i, ∑ l, 2 * (x i * B i l * x l) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => term_ge B x i l
  have E4 : ∑ i, ∑ l, 2 * (x i * B i l * x l) = 2 * ∑ i, ∑ l, x i * B i l * x l := by
    simp only [← Finset.mul_sum]
  have hlow : ∑ i, (B i i - offSum B i) * x i ^ 2 ≤ ∑ i, ∑ l, x i * B i l * x l := by
    linarith
  refine lt_of_lt_of_le ?_ hlow
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hx (funext hcon)
  have hpos : ∀ i, 0 ≤ (B i i - offSum B i) * x i ^ 2 := fun i =>
    mul_nonneg (sub_nonneg.2 (h i).le) (sq_nonneg _)
  calc (0:ℝ) < (B j j - offSum B j) * x j ^ 2 :=
        mul_pos (sub_pos.2 (h j)) (by positivity)
    _ ≤ _ := Finset.single_le_sum (fun i _ => hpos i) (mem_univ j)

/-- If `X A Xᵀ` is positive definite and `A` is symmetric, `A` is positive definite. -/
theorem posDef_of_posDef_congr {A X : Matrix n n ℝ}
    (hB : (X * A * Xᵀ).PosDef) : A.PosDef := by
  have hU : IsUnit X := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    rw [← det_transpose] at hdet
    obtain ⟨v, hv, hv0⟩ := (exists_mulVec_eq_zero_iff (M := Xᵀ)).2 hdet
    have := (posDef_iff_dotProduct_mulVec.1 hB).2 hv
    have e : star v ⬝ᵥ ((X * A * Xᵀ) *ᵥ v) = 0 := by
      rw [show (X * A * Xᵀ) *ᵥ v = (X * A) *ᵥ (Xᵀ *ᵥ v) from (mulVec_mulVec _ _ _).symm, hv0,
        mulVec_zero, dotProduct_zero]
    rw [e] at this; exact lt_irrefl _ this
  have : (X * A * star X).PosDef := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).1 this

end RealFP.Mat
