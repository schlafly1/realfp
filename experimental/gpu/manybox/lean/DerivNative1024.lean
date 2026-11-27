import ManyBoxCert
set_option profiler true
set_option profiler.threshold 1000
/-! P1 δ=1/1024 by realfp's `interval` tactic (derivative search + check), `(trust := native)`. -/
set_option maxHeartbeats 0 in
theorem p1_d1024_interval_native (x y : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) +
    ((((128*y^2 - 256)*y^2 + 160)*y^2 - 32)*y^2 + 1) ≤ 2 + 1/1024 := by
  interval (depth := 60) (maxBoxes := 10000000) (trust := native)

#print axioms p1_d1024_interval_native
