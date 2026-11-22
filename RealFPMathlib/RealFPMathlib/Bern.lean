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

end RealFP.Bern
