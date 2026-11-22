/-
Polynomial sign certificates and rigorous quadrature, checked by the kernel
(`decide +kernel` on the Lean specification; no `native_decide`, standard axioms only).

The slow first-round Float-spec examples (`taylor_exp_pos`, `gauss_integral_bounds`, ≈75 s and
≈6 GB) are in the optional library `RealFPMathlibSlow/PolyQuad.lean`, which is not built by
default (`lake build RealFPMathlibSlow`).

Fast kernel path (`KF`/`KI` bit patterns):
* `taylor_exp_pos'` : the same polynomial positivity, by the `interval` tactic.
* `gauss_integral_bounds_kq` : `0.7468 ≤ ∫₀¹ e^{-x²} dx ≤ 0.7469` by order-4 Taylor quadrature
  (`quadBound`, 4 cells; ~5 s beyond the import vs ~47 s for the second-order Float-spec rule).
-/
import RealFPMathlib.Quad
import RealFPMathlib.KQuad
import RealFPMathlib.IntervalTactic
import Interval64.Kernel.QuadCert

open Interval64 Interval64.Quad Interval64.KF RealFP RealFP.Poly RealFP.Quad Polynomial

namespace RealFP.Examples.PolyQuad

/-! ### `∫₀¹ e^{-x²}` -/

/-- `e^{-x²}` as a reflected expression in variable `0`. -/
def g : IExpr := .exp (.neg (.mul (.var 0) (.var 0)))

/-! ### Kernel fast path -/

theorem taylor_exp_pos' {x : ℝ} (h0 : 0 ≤ x) (h4 : x ≤ 4) :
    0 < 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
  interval

open Interval64.KF.KQ RealFP.KQ in
/-- **`0.7468 ≤ ∫₀¹ e^{-x²} dx ≤ 0.7469`** (order-4 Taylor cells, kernel-checked). -/
theorem gauss_integral_bounds_kq :
    (7468 / 10000 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 7469 / 10000 := by
  have h := integral_bounds_of_quadBound (e := g) (K := 4) (a := bits% 0) (b := bits% 1)
    (cs := cells% 0 1 4) (qa := 0) (qb := 1) (ql := 7468 / 10000) (qh := 7469 / 10000)
    (by decide +kernel)
  have e : ∀ x : ℝ, g.denote [x] = Real.exp (-x ^ 2) := fun x => by simp [g, IExpr.denote, sq]
  simp only [e] at h
  push_cast at h
  exact h

end RealFP.Examples.PolyQuad
