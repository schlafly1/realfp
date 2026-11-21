/-
Examples for the conversions: numeric literals, decimal literals, casts and
`x ∈ X` membership. Interval endpoints are checked by `decide +kernel` (the kernel
runs the Lean spec; no `native_decide` axiom).
-/
import RealFPMathlib.Conv

open Interval64 Interval64.Spec RealFP

namespace RealFP.Examples.Conv

/-- `[0, 1]`. -/
def X : Interval64 := ofRatInterval 0 1

/-- `X² − 0.1·X + 2` written with literals: `0.1` is the *exact* `1/10`, enclosed
    outward, and `2` is `ofRat 2`. -/
def P : Interval64 := X * X - 0.1 * X + 2

theorem X_lo : bitsToRat? X.lo.toBits = some 0 := by decide +kernel
theorem X_hi : bitsToRat? X.hi.toBits = some 1 := by decide +kernel
theorem tenth_lo : bitsToRat? (0.1 : Interval64).lo.toBits =
    some (7205759403792793 / 72057594037927936) := by decide +kernel
theorem tenth_hi : bitsToRat? (0.1 : Interval64).hi.toBits =
    some (3602879701896397 / 36028797018963968) := by decide +kernel
theorem P_hi : bitsToRat? P.hi.toBits = some 3 := by decide +kernel

theorem mem_X {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ∈ X :=
  mem_toSet_ofRatInterval (by push_cast; exact h0) (by push_cast; exact h1)

/-- The real polynomial (with the real decimal `0.1`) lies in `P` on `[0, 1]`. -/
theorem poly_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x - 0.1 * x + 2 ∈ P := by
  have hx := mem_X h0 h1
  exact Iv.add_mem
    (Iv.sub_mem (Iv.mem_mul hx hx) (Iv.mem_mul (ofScientific_mem 1 true 1) hx))
    (ofNat_mem 2)

/-- `x² − 0.1·x + 2 ≤ 3` on `[0, 1]`, from one interval evaluation. -/
theorem poly_le_three {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x - 0.1 * x + 2 ≤ 3 := by
  have h := (poly_mem h0 h1).2
  rw [Interval64Proofs.Value.bitsToEVal_rat_of_bitsToRat? P_hi] at h
  exact_mod_cast h

/-- A `Float` coerces to its point interval; `0.5` is exact in binary64. -/
theorem half_mem : (1 / 2 : ℝ) ∈ ((0.5 : Float) : Interval64) :=
  floatCoe_mem (toReal?_of_bitsToRat? (by decide +kernel : bitsToRat? (0.5 : Float).toBits = some (1 / 2)) |>.trans (by norm_num))

/-- Mixed expressions elaborate through the coercions. -/
def mixed (n : ℕ) (z : ℤ) (q : ℚ) (f : Float) : Interval64 := X + n + z + q + f + 2 + 0.5

end RealFP.Examples.Conv
