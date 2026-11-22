/-
2D quadrature over a rectangle, checked by the kernel (`decide +kernel` on the Lean spec).

* `xy_rect_bounds` : `1/8 ≤ ∫_{[0,1]²} x y ≤ 1/2` (zeroth-order cells, 4×4 grid), via Fubini.
-/
import RealFPMathlib.Quad2

open Interval64 Interval64.Quad Interval64.KF RealFP RealFP.Poly RealFP.Quad RealFP.Quad2
open MeasureTheory Set

namespace RealFP.Examples.Quad2

def xy : IExpr := .mul (.var 0) (.var 1)

def R : Interval64 := integrate2E0 xy 0 1 0 1 0 2

theorem R_ok : (0.125 : Float) ≤ R.lo ∧ R.hi ≤ (0.5 : Float) := by decide +kernel

theorem toReal_zero : (0 : Float).toReal = 0 := by
  rw [toReal_of_bitsToRat? (q := 0) (by decide +kernel)]; simp

theorem toReal_one : (1 : Float).toReal = 1 := by
  rw [toReal_of_bitsToRat? (q := 1) (by decide +kernel)]; simp

theorem c_lo : (0.125 : Float).toReal = 1 / 8 := by
  rw [toReal_of_bitsToRat? (q := 1 / 8) (by decide +kernel)]; norm_num

theorem c_hi : (0.5 : Float).toReal = 1 / 2 := by
  rw [toReal_of_bitsToRat? (q := 1 / 2) (by decide +kernel)]; norm_num

/-- **`1/8 ≤ ∫_{[0,1]²} x y ≤ 1/2`** (true value `1/4`). -/
theorem xy_rect_bounds :
    (1 / 8 : ℝ) ≤ ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, p.1 * p.2 ∧
      (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, p.1 * p.2) ≤ 1 / 2 := by
  have hf : ContinuousOn (Function.uncurry fun x y : ℝ => x * y) (Icc 0 1 ×ˢ Icc 0 1) :=
    (continuous_fst.mul continuous_snd).continuousOn
  rw [show (fun p : ℝ × ℝ => p.1 * p.2) = fun p => (fun x y : ℝ => x * y) p.1 p.2 from rfl,
    setIntegral_rect_eq zero_le_one zero_le_one hf]
  have e : ∀ x y : ℝ, xy.denote [x, y] = x * y := fun x y => by simp [xy, IExpr.denote]
  have hc : ContinuousOn (fun p : ℝ × ℝ => xy.denote [p.1, p.2]) (uIcc (0 : Float).toReal
      (1 : Float).toReal ×ˢ uIcc (0 : Float).toReal (1 : Float).toReal) := by
    simp only [e]; exact (continuous_fst.mul continuous_snd).continuousOn
  have h := integral2_mem_integrate2E0 xy (a := 0) (b := 1) (c := 0) (d := 1) hc 0 2
  rw [toReal_zero, toReal_one] at h
  simp only [e] at h
  have hcn : (0.125 : Float).isNaN = false := by decide +kernel
  have hci : (0.125 : Float).isInf = false := by decide +kernel
  have hdn : (0.5 : Float).isNaN = false := by decide +kernel
  have hdi : (0.5 : Float).isInf = false := by decide +kernel
  constructor
  · have := le_of_lo hcn hci h R_ok.1; rwa [c_lo] at this
  · have := ge_of_hi hdn hdi h R_ok.2; rwa [c_hi] at this

end RealFP.Examples.Quad2
