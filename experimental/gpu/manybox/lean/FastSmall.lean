import ManyBoxCert
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 50

set_option maxHeartbeats 0 in
/-- `native_decide` on the precompiled `checkC3`; certificate `../certs/p1_d4.cert` from the GPU search. -/
theorem p1_d4_fast (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
    ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 6 := by
  have h : eP1.denote [x, y] ≤ ((6 : ℚ) : ℝ) :=
    proveC3_le eP1 box1 (6) (decodeCertC 2 (mb_cert% "../certs/p1_d4.cert"))
      (by native_decide) [x, y] (by simp only [box1]; mb_inboxes)
  simpa [eP1, t8, x2, Interval64.KF.IExpr.denote] using h

#print axioms p1_d4_fast

set_option maxHeartbeats 0 in
/-- `native_decide` on the precompiled `checkC3`; certificate `../certs/p2_d1.cert` from the GPU search. -/
theorem p2_d1_fast (x y z w : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (hz : -1 ≤ z ∧ z ≤ 1) (hw : -1 ≤ w ∧ w ≤ 1) :
    -1 ≤ x^2*y^2 + y^2*z^2 + z^2*x^2 + w^4 - 4*(x*y)*(z*w) := by
  have h : ((-1 : ℚ) : ℝ) ≤ eP2.denote [x, y, z, w] :=
    proveC3_ge eP2 box2 (-1) (decodeCertC 4 (mb_cert% "../certs/p2_d1.cert"))
      (by native_decide) [x, y, z, w] (by simp only [box2]; mb_inboxes)
  simpa [eP2, x2, Interval64.KF.IExpr.denote] using h

#print axioms p2_d1_fast

set_option maxHeartbeats 0 in
/-- `native_decide` on the precompiled `checkC3`; certificate `../certs/p1_d1.cert` from the GPU search. -/
theorem p1_d1_fast (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
    ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 3 := by
  have h : eP1.denote [x, y] ≤ ((3 : ℚ) : ℝ) :=
    proveC3_le eP1 box1 (3) (decodeCertC 2 (mb_cert% "../certs/p1_d1.cert"))
      (by native_decide) [x, y] (by simp only [box1]; mb_inboxes)
  simpa [eP1, t8, x2, Interval64.KF.IExpr.denote] using h

#print axioms p1_d1_fast
