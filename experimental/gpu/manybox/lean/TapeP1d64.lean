import ManyBoxCert
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 50

set_option maxHeartbeats 0 in
/-- `native_decide` on the C batch checker `checkHex`; certificate `../certs/p1_d64.cert` from the GPU search. -/
theorem p1_d64_tape (x y : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) :
    ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
    ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 2 + 1/64 := by
  have h : eP1.denote [x, y] ≤ ((2 + 1/64 : ℚ) : ℝ) :=
    proveT_le eP1 box1 (2 + 1/64) 2 (mb_cert% "../certs/p1_d64.cert")
      (by native_decide) [x, y] (by simp only [box1]; mb_inboxes)
  simpa [eP1, t8, x2, Interval64.KF.IExpr.denote] using h

#print axioms p1_d64_tape
