/-
Example: interval Newton (slope form) with extended division locates both roots
of `x² = 2` in `[-2, 2]`.

Step 1 (split). For a root, `x = 2 / x` with `x ∈ X0 = [-2, 2] ∋ 0`, so
`x ∈ divSplit 2 X0 = [-∞, -1] ∪ [1, +∞]`: the box splits into `[-2, -1]` and `[1, 2]`.
Step 2 (one slope-Newton step per piece). On `[1, 2]`, `x = 1.5 - 0.25 / (x + 1.5)`;
on `[-2, -1]`, `x = 0.25 / (1.5 - x) - 1.5`. Evaluating these with `Interval64`
gives `x ∈ [1.39999…, 1.42858…]` resp. its negative.

All interval endpoints are computed by the Lean kernel (`decide +kernel`, the Lean
spec, no `native_decide`); the real-number steps use `mem_divSplit` and `Iv.*_mem` / `Iv.mem_*`.
-/
import RealFPMathlib.Split

open Interval64 Interval64.Spec RealFP

namespace RealFP.Examples.Split

def X0 : Interval64 := ofRatInterval (-2) 2
def X1 : Interval64 := ofRatInterval 1 2
def X2 : Interval64 := ofRatInterval (-2) (-1)
/-- Newton image of `[1, 2]`. -/
def N1 : Interval64 := 1.5 - 0.25 / (X1 + 1.5)
/-- Newton image of `[-2, -1]`. -/
def N2 : Interval64 := 0.25 / (1.5 - X2) - 1.5

theorem split_hi : bitsToRat? (divSplit 2 X0).piece1.hi.toBits = some (-1) := by decide +kernel
theorem split_lo : bitsToRat? (divSplit 2 X0).piece2.lo.toBits = some 1 := by decide +kernel
theorem N1_lo : bitsToRat? N1.lo.toBits = some (3152519739159347 / 2251799813685248) := by
  decide +kernel
theorem N1_hi : bitsToRat? N1.hi.toBits = some (6433713753386423 / 4503599627370496) := by
  decide +kernel
theorem N2_lo : bitsToRat? N2.lo.toBits = some (-6433713753386423 / 4503599627370496) := by
  decide +kernel
theorem N2_hi : bitsToRat? N2.hi.toBits = some (-3152519739159347 / 2251799813685248) := by
  decide +kernel

/-- Finite endpoints, by kernel evaluation. -/
theorem fin {b : UInt64} (h : (bitsToRat? b).isSome = true) : ∃ q, bitsToRat? b = some q :=
  Option.isSome_iff_exists.mp h

theorem mem_ofRatInterval {lo hi : ℚ} {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    x ∈ ofRatInterval lo hi := mem_toSet_ofRatInterval h1 h2

/-- Step 1: a root in `[-2, 2]` has `x ≤ -1` or `1 ≤ x` (extended division by `[-2, 2]`). -/
theorem step1 {x : ℝ} (h1 : -2 ≤ x) (h2 : x ≤ 2) (hr : x * x = 2) : x ≤ -1 ∨ 1 ≤ x := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hr
  have hx : x ∈ X0 := mem_ofRatInterval (by push_cast; linarith) (by push_cast; linarith)
  have hq : (2 : ℝ) / x = x := by field_simp; linarith
  have h := mem_divSplit (ofNat_mem 2) hx hx0
  rw [hq] at h
  rcases h with h | h
  · left
    have := h.2
    rw [Interval64Proofs.Value.bitsToEVal_rat_of_bitsToRat? split_hi] at this
    exact_mod_cast this
  · right
    have := h.1
    rw [Interval64Proofs.Value.bitsToEVal_rat_of_bitsToRat? split_lo] at this
    exact_mod_cast this

/-- Step 2 on `[1, 2]`. -/
theorem step2_pos {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) (hr : x * x = 2) : x ∈ N1 := by
  have hx : x ∈ X1 := mem_ofRatInterval (by push_cast; linarith) (by push_cast; linarith)
  have hne : x + 1.5 ≠ 0 := by norm_num; linarith
  have hN : x = 1.5 - 0.25 / (x + 1.5) := by field_simp; norm_num; nlinarith
  rw [hN]
  exact Iv.sub_mem (ofScientific_mem 15 true 1)
    (Iv.mem_div (ofScientific_mem 25 true 2) (Iv.add_mem hx (ofScientific_mem 15 true 1)) hne)

/-- Step 2 on `[-2, -1]`. -/
theorem step2_neg {x : ℝ} (h1 : -2 ≤ x) (h2 : x ≤ -1) (hr : x * x = 2) : x ∈ N2 := by
  have hx : x ∈ X2 := mem_ofRatInterval (by push_cast; linarith) (by push_cast; linarith)
  have hne : 1.5 - x ≠ 0 := by norm_num; linarith
  have hN : x = 0.25 / (1.5 - x) - 1.5 := by field_simp; norm_num; nlinarith
  rw [hN]
  exact Iv.sub_mem
    (Iv.mem_div (ofScientific_mem 25 true 2) (Iv.sub_mem (ofScientific_mem 15 true 1) hx) hne)
    (ofScientific_mem 15 true 1)

/-- Both roots of `x² = 2` in `[-2, 2]` are located to about `0.03`. -/
theorem sqrt_two_roots {x : ℝ} (h1 : -2 ≤ x) (h2 : x ≤ 2) (hr : x * x = 2) :
    (1.3999 ≤ x ∧ x ≤ 1.4286) ∨ (-1.4286 ≤ x ∧ x ≤ -1.3999) := by
  rcases step1 h1 h2 hr with hn | hp
  · right
    have h := step2_neg h1 hn hr
    rw [mem_iff, toSet_eq_Icc N2_lo N2_hi] at h
    obtain ⟨l, u⟩ := h
    push_cast at l u
    constructor <;> linarith
  · left
    have h := step2_pos hp h2 hr
    rw [mem_iff, toSet_eq_Icc N1_lo N1_hi] at h
    obtain ⟨l, u⟩ := h
    push_cast at l u
    constructor <;> linarith

end RealFP.Examples.Split
