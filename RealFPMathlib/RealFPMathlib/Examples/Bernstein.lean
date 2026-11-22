/-
Bernstein sign certificates, checked by the kernel (`decide +kernel` on the Lean specification;
standard axioms only).

* `taylor_exp_pos_bern` : `0 < 1 - x + x²/2 - x³/6 + x⁴/24` on `[0, 4]` (degree 4, 2 boxes).
* `bilinear_pos` : `0 < 1 - x/2 - y/2 + x y` on `[0, 1]²` (tensor Bernstein, one box).
-/
import RealFPMathlib.Bern

open Interval64 RealFP RealFP.Poly RealFP.Bern Polynomial

namespace RealFP.Examples.Bernstein

def e4 : Array ℚ := #[1, -1, 1/2, -1/6, 1/24]

theorem e4_checkB : (IPoly.ofRats e4).checkGtB 0 (ofRatInterval 0 4) 4 1 = true := by
  decide +kernel

theorem toReal_zero : (0 : Float).toReal = 0 := by
  rw [toReal_of_bitsToRat? (q := 0) (by decide +kernel)]; simp

theorem taylor_exp_pos_bern {x : ℝ} (h0 : 0 ≤ x) (h4 : x ≤ 4) :
    0 < 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  have hx : x ∈ ofRatInterval 0 4 :=
    mem_toSet_ofRatInterval (by push_cast; exact h0) (by push_cast; exact h4)
  have h := lt_of_checkGtB (contains_ofRats e4) e4_checkB hx
  rw [toReal_zero, eval_ratPoly] at h
  simp [e4, Finset.sum_range_succ] at h
  linarith

/-- `1 - x/2 + (-1/2 + x) y`. -/
def q2 : IPoly2 := #[IPoly.ofRats #[1, -1/2], IPoly.ofRats #[-1/2, 1]]

noncomputable def p2 : ℝ[X][X] := C (ratPoly #[1, -1/2]) + C (ratPoly #[-1/2, 1]) * X

theorem contains_q2 : Contains2 q2 p2 := by
  intro j
  rcases j with _ | _ | j
  · simpa [p2, q2, IPoly2.coeff] using contains_ofRats #[1, -1/2]
  · simpa [p2, q2, IPoly2.coeff] using contains_ofRats #[-1/2, 1]
  · have : p2.coeff (j + 2) = 0 := by simp [p2, coeff_C, coeff_X]
    rw [this]
    simpa [q2, IPoly2.coeff] using contains_empty

theorem q2_check : q2.checkGt2B 0 (ofRatInterval 0 1) (ofRatInterval 0 1) 1 1 0 = true := by
  decide +kernel

theorem bilinear_pos {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < 1 - x / 2 - y / 2 + x * y := by
  have hx : x ∈ ofRatInterval 0 1 :=
    mem_toSet_ofRatInterval (by push_cast; exact hx0) (by push_cast; exact hx1)
  have hy : y ∈ ofRatInterval 0 1 :=
    mem_toSet_ofRatInterval (by push_cast; exact hy0) (by push_cast; exact hy1)
  have h := lt_of_checkGt2B contains_q2 q2_check hx hy
  rw [toReal_zero] at h
  simp [eval2R, p2, eval_ratPoly, Finset.sum_range_succ] at h
  linarith

end RealFP.Examples.Bernstein
