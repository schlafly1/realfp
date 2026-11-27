import ManyBoxCert
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 50

/-! "Weaker than proof" demo (a): a *counterexample* found by the GPU.

`v2/build/mb2 refute P1 64 1.9921875` (fp64 or fp32, 0.3 s on the GB10) reports a box on which
the interval enclosure of `T8(x) + T8(y)` lies entirely above `2 - 1/128`:
`refuted box level 16 coords 127 127`, box `[-1/128, 0] × [-1/128, 0]`.
One box, no certificate: Lean re-checks that single box with realfp's kernel checker
(`decide +kernel`, standard axioms only) and so refutes the claim `T8(x) + T8(y) ≤ 2 - 1/64` on
`[-1,1]²`. Refutations need one box, so they are always cheap to verify. -/

set_option maxHeartbeats 0 in
theorem p1_box_gt (x y : ℝ) (hx : -1/128 ≤ x ∧ x ≤ 0) (hy : -1/128 ≤ y ∧ y ≤ 0) :
    ((2 - 1/64 : ℚ) : ℝ) < eP1.denote [x, y] := by
  refine RealFP.prove_gt eP1 [(-1/128, 0), (-1/128, 0)] (2 - 1/64) .leaf (by decide +kernel) [x, y] ?_
  mb_inboxes

theorem p1_not_le :
    ¬ ∀ x y : ℝ, -1 ≤ x ∧ x ≤ 1 → -1 ≤ y ∧ y ≤ 1 →
      ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
      ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 2 - 1/64 := by
  intro h
  have h1 := p1_box_gt (-1/128) (-1/128) (by norm_num) (by norm_num)
  have h2 := h (-1/128) (-1/128) (by norm_num) (by norm_num)
  simp only [eP1, t8, x2, Interval64.KF.IExpr.denote] at h1
  push_cast at h1
  linarith

#print axioms p1_not_le
