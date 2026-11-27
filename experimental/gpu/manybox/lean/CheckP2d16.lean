import ManyBoxCert
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 100

set_option maxHeartbeats 0 in
/-- `native_decide` on `checkF` (leaves evaluated by realfp's C runtime); certificate `../certs/p2_d16.cert` from the GPU search. -/
theorem p2_d16_nativeF (x y z w : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (hz : -1 ≤ z ∧ z ≤ 1) (hw : -1 ≤ w ∧ w ≤ 1) :
    -1/16 ≤ x^2*y^2 + y^2*z^2 + z^2*x^2 + w^4 - 4*(x*y)*(z*w) := by
  have h : ((-1/16 : ℚ) : ℝ) ≤ eP2.denote [x, y, z, w] :=
    proveF_ge eP2 box2 (-1/16) (decodeCert 4 (mb_cert% "../certs/p2_d16.cert")) (by native_decide)
      [x, y, z, w] (by simp only [box2]; mb_inboxes)
  simpa [eP2, x2, Interval64.KF.IExpr.denote] using h

#print axioms p2_d16_nativeF
