/-
Exact rational positive-definiteness certificate (`pos_def (precision := 128)`).

For a symmetric rational matrix `A` and any rational matrix `X` (an approximate inverse
Cholesky factor, computed natively), `B = X A Xᵀ` is computed exactly in `ℚ`; if `B` is strictly
diagonally dominant with positive diagonal, `A` is positive definite
(`RealFP.Mat.posDef_of_diagDom`, `RealFP.Mat.posDef_of_posDef_congr`). No rounding is involved,
so the only limit is the size of the rationals.
-/
import RealFPMathlib.MatrixPD

open Matrix Finset

namespace RealFP.PDQ

/-- Entry `(i, j)` of a list-of-rows rational matrix (0 outside). -/
def qg (L : List (List ℚ)) (i j : ℕ) : ℚ := (L.getD i []).getD j 0

def dotq (n : ℕ) (f g : ℕ → ℚ) : ℚ := ((List.range n).map fun k => f k * g k).sum

/-- `(X A)ᵢₖ`. -/
def tq (n : ℕ) (A X : ℕ → ℕ → ℚ) (i k : ℕ) : ℚ := dotq n (fun j => X i j) (fun j => A j k)

/-- `(X A Xᵀ)ᵢₗ`. -/
def bq (n : ℕ) (A X : ℕ → ℕ → ℚ) (i l : ℕ) : ℚ := dotq n (fun k => tq n A X i k) (fun k => X l k)

def offq (n : ℕ) (A X : ℕ → ℕ → ℚ) (i : ℕ) : ℚ :=
  ((List.range n).map fun l => if l = i then 0 else |bq n A X i l|).sum

/-- Strict diagonal dominance of `X A Xᵀ`, exactly. -/
def congrCheckQ (n : ℕ) (A X : ℕ → ℕ → ℚ) : Bool :=
  (List.range n).all fun i => decide (offq n A X i < bq n A X i i)

theorem lsum_cast (n : ℕ) (g : ℕ → ℚ) :
    ((((List.range n).map g).sum : ℚ) : ℝ) = ∑ k ∈ range n, (g k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, ih, Finset.sum_range_succ]
    simp

theorem sum_fin_range {n : ℕ} (g : ℕ → ℝ) : ∑ k : Fin n, g k = ∑ k ∈ range n, g k :=
  Fin.sum_univ_eq_sum_range g n

theorem posDef_of_congrQ {n : ℕ} {A X : ℕ → ℕ → ℚ} (h : congrCheckQ n A X = true)
    (hs : ∀ i j, i < n → j < n → A i j = A j i) :
    (Matrix.of fun i j : Fin n => (A i j : ℝ)).PosDef := by
  set Ar : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (A i j : ℝ)
  set Xr : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (X i j : ℝ)
  have hB : ∀ i l : Fin n, (Xr * Ar * Xrᵀ) i l = (bq n A X i l : ℝ) := by
    intro i l
    simp only [Matrix.mul_apply, transpose_apply, Ar, Xr, Matrix.of_apply, bq, dotq, tq,
      lsum_cast, Rat.cast_mul]
    rw [sum_fin_range (fun k => (∑ j : Fin n, (X i j : ℝ) * (A j k : ℝ)) * (X l k : ℝ))]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    rw [show (k : ℕ) = ((⟨k, hk'⟩ : Fin n) : ℕ) from rfl]
    congr 1
    exact sum_fin_range (fun j => (X i j : ℝ) * (A j k : ℝ))
  have hAs : Arᵀ = Ar := by
    ext i j; simp [Ar, hs i j i.2 j.2]
  refine RealFP.Mat.posDef_of_posDef_congr (X := Xr) (RealFP.Mat.posDef_of_diagDom ?_ ?_)
  · simp [transpose_mul, hAs, Matrix.mul_assoc]
  · intro i
    simp only [congrCheckQ, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    have hi := h i i.2
    have hr : ((offq n A X i : ℚ) : ℝ) < ((bq n A X i i : ℚ) : ℝ) := by exact_mod_cast hi
    rw [hB]
    refine lt_of_eq_of_lt ?_ hr
    rw [RealFP.Mat.offSum, offq, lsum_cast, ← sum_fin_range
      (fun l => (((if l = (i : ℕ) then 0 else |bq n A X i l|) : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp
    · have : (l : ℕ) ≠ i := fun e => hl (Fin.ext e)
      simp [hl, this, hB]

end RealFP.PDQ
