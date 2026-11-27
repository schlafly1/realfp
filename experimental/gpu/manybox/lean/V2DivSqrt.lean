import ManyBoxCert
import ManyBoxProbs
open Interval64.KF ManyBox ManyBox.V2
set_option profiler true
set_option profiler.threshold 50

/-! Division and square roots in the C checker (tape ops 7, 8): Nesbitt's inequality and the
power-mean inequality with margin 1/64, certificates from the v2 GPU search (fp64 and fp32). -/

set_option maxHeartbeats 0 in
theorem nesbitt_d64 (x y z : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) (hz : -1 ≤ z ∧ z ≤ 1) :
    3/2 - 1/64 ≤ (2 + x) / ((2 + y) + (2 + z)) + (2 + y) / ((2 + z) + (2 + x)) +
      (2 + z) / ((2 + x) + (2 + y)) := by
  have h : ((3/2 - 1/64 : ℚ) : ℝ) ≤ eNES.denote [x, y, z] :=
    proveT_ge eNES (cube 3) (3/2 - 1/64) 3 (mb_cert% "../certs/v2/nes_0.015625.cert")
      (by native_decide) [x, y, z] (by simp only [cube, List.replicate]; mb_inboxes)
  simpa [eNES, sh, Interval64.KF.IExpr.denote] using h

#print axioms nesbitt_d64

set_option maxHeartbeats 0 in
/-- Same claim, certificate from the fp32 GPU search (checked in fp64 as always). -/
theorem nesbitt_d64_f32 (x y z : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) (hz : -1 ≤ z ∧ z ≤ 1) :
    3/2 - 1/64 ≤ (2 + x) / ((2 + y) + (2 + z)) + (2 + y) / ((2 + z) + (2 + x)) +
      (2 + z) / ((2 + x) + (2 + y)) := by
  have h : ((3/2 - 1/64 : ℚ) : ℝ) ≤ eNES.denote [x, y, z] :=
    proveT_ge eNES (cube 3) (3/2 - 1/64) 3 (mb_cert% "../certs/v2/nes_0.015625_f32.cert")
      (by native_decide) [x, y, z] (by simp only [cube, List.replicate]; mb_inboxes)
  simpa [eNES, sh, Interval64.KF.IExpr.denote] using h

set_option maxHeartbeats 0 in
theorem powermean_d64 (x y z : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (2 + x) + Real.sqrt (2 + y) + Real.sqrt (2 + z) -
      Real.sqrt (3 * ((2 + x) + (2 + y) + (2 + z))) ≤ 1/64 := by
  have h : ePM.denote [x, y, z] ≤ ((1/64 : ℚ) : ℝ) :=
    proveT_le ePM (cube 3) (1/64) 3 (mb_cert% "../certs/v2/pm_0.015625.cert")
      (by native_decide) [x, y, z] (by simp only [cube, List.replicate]; mb_inboxes)
  simpa [ePM, sh, Interval64.KF.IExpr.denote] using h

#print axioms powermean_d64

set_option maxHeartbeats 0 in
theorem powermean_d64_f32 (x y z : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1) (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (2 + x) + Real.sqrt (2 + y) + Real.sqrt (2 + z) -
      Real.sqrt (3 * ((2 + x) + (2 + y) + (2 + z))) ≤ 1/64 := by
  have h : ePM.denote [x, y, z] ≤ ((1/64 : ℚ) : ℝ) :=
    proveT_le ePM (cube 3) (1/64) 3 (mb_cert% "../certs/v2/pm_0.015625_f32.cert")
      (by native_decide) [x, y, z] (by simp only [cube, List.replicate]; mb_inboxes)
  simpa [ePM, sh, Interval64.KF.IExpr.denote] using h
