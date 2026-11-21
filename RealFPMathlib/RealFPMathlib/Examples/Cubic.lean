/-
Example 1: `f(x) = 6x - x³` satisfies `f(x) ≤ f(√2) + 0.001` for all real `x ≥ 0`.

Method:
* On `[0, 5/2]`, `x * (6 - x * x) ≤ c` (`c = 5.6578` as a double) is proved by the
  `interval` tactic (`bound_box`): bisection with Interval64 arithmetic, checked by one
  `decide +kernel` call — no `native_decide`, standard axioms only.
  (Earlier version: a fixed grid of `2^13 · 5/2 = 20480` boxes checked by `allOK` with
  `native_decide`; `allOK` / `allOK_sound` are kept as the hand-written method.)
* The tail `x ≥ 5/2` is algebra: `f(x) = x (6 - x²) ≤ 0`.
* `c ≤ 4√2 + 1/1000 = f(√2) + 0.001` is also closed by `interval` (no variables).
-/
import RealFPMathlib.Tight
import RealFPMathlib.Unbounded
import RealFPMathlib.IntervalTactic

open Interval64 Interval64.Spec

namespace RealFP.Examples.Cubic

/-- Interval extension of `x ↦ x * (6 - x * x)` (= `6x - x³`). -/
def G (X : Interval64) : Interval64 := X * (ofRat 6 - X * X)

/-- Box number `i` of width `2^-k`. -/
def box (k i : Nat) : Interval64 := ofRatInterval ((i : ℚ) / 2 ^ k) (((i : ℚ) + 1) / 2 ^ k)

/-- Checker for one box: the computed upper bound of `G X` is `≤ c`
    (`mem_toSet_mul` needs no finiteness side conditions). -/
def boxOK (c : Float) (X : Interval64) : Bool :=
  decide ((G X).hi ≤ c)

/-- Checker for all boxes `0 … n-1`. -/
def allOK (c : Float) (k n : Nat) : Bool := (List.range n).all fun i => boxOK c (box k i)

theorem boxOK_sound {c : Float} {q : ℚ} {X : Interval64} (h : boxOK c X = true)
    (hc : bitsToRat? c.toBits = some q) {x : ℝ} (hx : x ∈ X.toSet) :
    x * (6 - x * x) ≤ q := by
  simp only [boxOK, decide_eq_true_eq] at h
  have h6 : (6 : ℝ) ∈ (ofRat 6).toSet := by exact_mod_cast mem_toSet_ofRat 6
  have hy : 6 - x * x ∈ (ofRat 6 - X * X).toSet :=
    sub_mem_toSet h6 (mem_toSet_mul hx hx)
  have hG : x * (6 - x * x) ∈ (G X).toSet :=
    mem_toSet_mul hx hy
  exact le_of_mem_toSet_of_hi_le hG h hc

/-- The boxes `0 … n-1` cover `[0, n / 2^k]`. -/
theorem exists_box {k n : Nat} (hn : 0 < n) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ (n : ℝ) / 2 ^ k) :
    ∃ i < n, x ∈ (box k i).toSet := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  set m := ⌊x * 2 ^ k⌋₊ with hm
  have hfl : (m : ℝ) ≤ x * 2 ^ k := Nat.floor_le (by positivity)
  have hfl' : x * 2 ^ k < m + 1 := Nat.lt_floor_add_one _
  have hxn : x * 2 ^ k ≤ n := by rwa [le_div_iff₀ hp] at h1
  rcases le_total m (n - 1) with hmn | hmn
  · refine ⟨m, by omega, mem_toSet_ofRatInterval ?_ ?_⟩ <;> push_cast
    · rw [div_le_iff₀ hp]; exact hfl
    · rw [le_div_iff₀ hp]; exact hfl'.le
  · refine ⟨n - 1, by omega, mem_toSet_ofRatInterval ?_ ?_⟩
    · push_cast
      rw [div_le_iff₀ hp]
      exact le_trans (by exact_mod_cast hmn) hfl
    · have : (((n - 1 : ℕ) : ℚ) + 1 : ℚ) = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; push_cast; exact h1

theorem allOK_sound {c : Float} {q : ℚ} {k n : Nat} (h : allOK c k n = true) (hn : 0 < n)
    (hc : bitsToRat? c.toBits = some q) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ (n : ℝ) / 2 ^ k) :
    x * (6 - x * x) ≤ q := by
  obtain ⟨i, hi, hx⟩ := exists_box hn h0 h1
  exact boxOK_sound (List.all_eq_true.1 h i (List.mem_range.2 hi)) hc hx

/-- The certified computation on `[0, 5/2]` (kernel-checked bisection certificate). -/
theorem bound_box (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 5 / 2) :
    x * (6 - x * x) ≤ ((3185058246467099 / 562949953421312 : ℚ) : ℝ) := by
  push_cast; interval

/-- Exact value of the double `5.6578`. -/
theorem c_val : bitsToRat? (5.6578 : Float).toBits = some (3185058246467099 / 562949953421312) := by
  decide +kernel

theorem c_le : ((3185058246467099 / 562949953421312 : ℚ) : ℝ) ≤ 4 * Real.sqrt 2 + 1 / 1000 := by
  push_cast; interval

/-- `f(√2) = 4√2`. -/
theorem f_sqrt_two : 6 * Real.sqrt 2 - Real.sqrt 2 ^ 3 = 4 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h]
  rw [this]; ring

/-- **Example 1.** For all real `x ≥ 0`, `6x - x³ ≤ f(√2) + 0.001`. -/
theorem cubic_bound (x : ℝ) (hx : 0 ≤ x) :
    6 * x - x ^ 3 ≤ (6 * Real.sqrt 2 - Real.sqrt 2 ^ 3) + 0.001 := by
  rw [f_sqrt_two]
  have hc := c_le
  rcases le_or_gt x (5 / 2) with h | h
  · have hb := bound_box x hx h
    have : 6 * x - x ^ 3 = x * (6 - x * x) := by ring
    rw [this]; norm_num at hc hb ⊢; linarith
  · have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by nlinarith : (0:ℝ) < x * x - 6)]

end RealFP.Examples.Cubic
