/-
Dependency-aware squaring and the other `Interval64.Ops` operations, checked by
the kernel (`decide +kernel`, no `native_decide`).

`X * X` treats the two factors as independent, so on `X = [-1, 2]` it gives
`[-2, 4]`; `square X` knows they are equal and gives `[0, 4]`.
-/
import RealFPMathlib.Ops

open Interval64 Interval64.Spec

namespace RealFP.Examples.Ops

/-- `X = [-1, 2]`. -/
def X : Interval64 := ⟨-1, 2⟩

theorem X_lo : bitsToRat? X.lo.toBits = some (-1) := by decide +kernel
theorem X_hi : bitsToRat? X.hi.toBits = some 2 := by decide +kernel

/-- `square [-1, 2] = [0, 4]` … -/
theorem square_X_lo : bitsToRat? (square X).lo.toBits = some 0 := by decide +kernel
theorem square_X_hi : bitsToRat? (square X).hi.toBits = some 4 := by decide +kernel

/-- … whereas `[-1, 2] * [-1, 2] = [-2, 4]`. -/
theorem mul_X_lo : bitsToRat? (X * X).lo.toBits = some (-2) := by decide +kernel
theorem mul_X_hi : bitsToRat? (X * X).hi.toBits = some 4 := by decide +kernel

/-- Even powers are tight as well; odd powers use the monotone endpoint rule. -/
theorem pown_X_4 : bitsToRat? (pown X 4).lo.toBits = some 0 ∧
    bitsToRat? (pown X 4).hi.toBits = some 16 := by decide +kernel
theorem pown_X_3 : bitsToRat? (pown X 3).lo.toBits = some (-1) ∧
    bitsToRat? (pown X 3).hi.toBits = some 8 := by decide +kernel

theorem mem_X {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 2) : x ∈ X := by
  show x ∈ X.toSet
  rw [toSet_eq_Icc X_lo X_hi]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Real consequence: `0 ≤ x² ≤ 4` on `[-1, 2]` from one `square` evaluation. -/
theorem sq_bounds {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 2) : 0 ≤ x ^ 2 ∧ x ^ 2 ≤ 4 := by
  have h := mem_square (mem_X h1 h2)
  change x ^ 2 ∈ (square X).toSet at h
  rw [toSet_eq_Icc square_X_lo square_X_hi] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Other operations, evaluated in the kernel. -/
example : bitsToRat? (-X).lo.toBits = some (-2) := by decide +kernel
example : bitsToRat? (Interval64.abs X).lo.toBits = some 0 ∧
    bitsToRat? (Interval64.abs X).hi.toBits = some 2 := by decide +kernel
example : bitsToRat? (mid X).toBits = some (1 / 2) := by decide +kernel
example : bitsToRat? (width X).toBits = some 3 := by decide +kernel
example : bitsToRat? (mag X).toBits = some 2 := by decide +kernel
example : bitsToRat? (mig X).toBits = some 0 := by decide +kernel
example : subset ⟨0, 1⟩ X = true := by decide +kernel
example : contains X 0 = true := by decide +kernel
example : isInvalid (intersect X ⟨3, 4⟩) = true := by decide +kernel
example : bitsToRat? (hull X ⟨3, 4⟩).hi.toBits = some 4 := by decide +kernel
example : bitsToRat? (inv (⟨2, 4⟩ : Interval64)).lo.toBits = some (1 / 4) := by decide +kernel
example : isWhole (inv X) = true := by decide +kernel
example : bitsToRat? (mid whole).toBits = some 0 := by decide +kernel

end RealFP.Examples.Ops
