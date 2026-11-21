/-
Examples for the Mathlib layer. Run from `RealFPMathlib/`:

    lake lean Examples.lean

(`lake lean` loads the compiled C kernels; plain `lean` does not.)
-/
import RealFPMathlib
import RealFPMathlib.Demo
import RealFPMathlib.Examples.Cubic
import RealFPMathlib.Examples.Jacobian
import RealFPMathlib.Examples.Transc

open Interval64 Interval64.Directed Interval64.Spec RealFP

/-! ## 1. Exact real values of doubles -/
#eval (0.1 : Float).toReal? |>.isSome           -- true (the value is a real, not printable)
example : (0.5 : Float).toReal? = some (1/2 : ℝ) := by
  rw [toReal?_of_bitsToRat? (q := 1/2) (by decide +kernel)]; norm_num

/-! ## 2. Intervals as sets of reals -/
-- `[1/10, 3/10]` rounded outward contains the real interval `[1/10, 3/10]`.
example : Set.Icc (1/10 : ℝ) (3/10) ⊆ (ofRatInterval (1/10) (3/10)).toSet := by
  simpa using Icc_subset_toSet_ofRatInterval (1/10) (3/10)

-- Real enclosure: any reals in X and Y have their sum in X + Y (no finiteness needed).
example (X Y : Interval64) (x y : ℝ) (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    x + y ∈ (X + Y).toSet := add_mem_toSet hx hy

/-! ## 3. Tightness over ℝ: no double strictly between `addDown` and the exact sum -/
example (a b : Float) (x y : ℝ) (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundDownR (x + y) (Interval64Proofs.Value.bitsToEVal (addDown a b).toBits) :=
  addDown_isRoundDownR ha hb

example (a : Float) (x : ℝ) (ha : a.toReal? = some x) (hx : 0 ≤ x) :
    IsRoundUpR (Real.sqrt x) (Interval64Proofs.Value.bitsToEVal (sqrtUp a).toBits) :=
  sqrtUp_isRoundUpR ha hx

/-! ## 4. Real theorems proved by running interval arithmetic (`native_decide`) -/
#eval Demo.J                                    -- ≈ [0.11, 0.39]
#check @Demo.sq_add_le      -- ∀ x ∈ [1/10, 3/10], x * x + x ≤ 13/32
#eval Demo.S                                    -- √2 between adjacent doubles
#check @Demo.sqrt_two_bounds -- 1.41421356 < √2 < 1.41421357
#check @Demo.sqrt_le_on      -- ∀ x ∈ [2, 3], √x ≤ 111/64

-- Your own: ∀ x ∈ [1, 2], x * x - x ≤ 2.
def X12 : Interval64 := ofRatInterval 1 2
theorem my_hi_le : (X12 * X12 - X12).hi ≤ 3.0 := by native_decide

example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : x * x - x ≤ 3 := by
  have hxI : x ∈ X12.toSet :=
    mem_toSet_ofRatInterval (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  have hlo : ∃ q, bitsToRat? X12.lo.toBits = some q := Option.isSome_iff_exists.mp (by decide +kernel)
  have hhi : ∃ q, bitsToRat? X12.hi.toBits = some q := Option.isSome_iff_exists.mp (by decide +kernel)
  have h := le_of_mem_toSet_of_hi_le (q := 3)
    (sub_mem_toSet (mul_mem_toSet hxI hxI hlo hhi hlo hhi) hxI) my_hi_le (by decide +kernel)
  exact_mod_cast h

#print axioms Demo.sq_add_le

/-! ## 5. Worked examples (`RealFPMathlib/Examples/`) -/

-- Example 1: 6x - x³ ≤ f(√2) + 0.001 for all x ≥ 0, by 20480 Interval64 boxes on [0, 5/2]
-- plus algebra for x ≥ 5/2.
#check @RealFP.Examples.Cubic.cubic_bound
#eval RealFP.Examples.Cubic.allOK 5.6578 13 20480   -- true  (box width 2^-13)
#eval RealFP.Examples.Cubic.allOK 5.6578 12 10240   -- false (2^-12 is too coarse)

-- Example 2: constant Jacobian determinant -2, but F is not injective.
#check @RealFP.Examples.Jacobian.jac_det
#check @RealFP.Examples.Jacobian.F_not_injective
#check @RealFP.Examples.Jacobian.solutions_quarter      -- exactly the 3 given points
#check @RealFP.Examples.Jacobian.ncard_solutions_026    -- 3 solutions for (-0.26, 0, 0)
#check @RealFP.Examples.Jacobian.s_bounds               -- 0.9805806756 < s < 0.9805806757
#check @RealFP.Examples.Jacobian.y_bounds
#eval (RealFP.Examples.Jacobian.S, RealFP.Examples.Jacobian.Y)
-- Interval residual check: F evaluated on the box (S, Y, 169/25) contains (-0.26, 0, 0).
open RealFP.Examples.Jacobian in
#eval
  let X := S; let Yb := Y; let Z := ofRat (169/25)
  let one := ofRat 1; let three := ofRat 3; let four := ofRat 4
  let u := one + X * Yb; let w := four + three * X * Yb
  (u * u * u * Z + Yb * Yb * u * w,
   Yb + three * X * (u * u) * Z + three * X * (Yb * Yb) * w,
   ofRat 2 * X - three * (X * X) * Yb - X * X * X * Z)


/-! ## 6. exp / log: CORE-MATH under RD/RU at runtime, rational Ziv spec for proofs -/
#eval Interval64.exp (ofRat 1)        -- ≈ [2.718282, 2.718282] (adjacent doubles)
#eval Interval64.log (ofRat 2)        -- ≈ [0.693147, 0.693147] (adjacent doubles)
#eval Interval64.log ⟨-1.0, 2.0⟩      -- lower end -inf (lo ≤ 0 policy)
#eval Interval64.exp ⟨-1000.0, 1000.0⟩ -- [0, inf]

-- `e` and `log 2` between adjacent doubles, proved by kernel evaluation of the
-- Lean spec (`decide +kernel`; no native_decide axiom):
#check RealFP.Examples.Transc.exp_one_bounds
#check RealFP.Examples.Transc.log_two_bounds

-- Real enclosure for any interval (exp) / any positive member (log):
example (X : Interval64) (x : ℝ) (hx : x ∈ X.toSet) :
    Real.exp x ∈ (Interval64.exp X).toSet := RealFP.Transc.exp_mem_toSet hx
example (X : Interval64) (x : ℝ) (hx : x ∈ X.toSet) (h0 : 0 < x) :
    Real.log x ∈ (Interval64.log X).toSet := RealFP.Transc.log_mem_toSet hx h0
