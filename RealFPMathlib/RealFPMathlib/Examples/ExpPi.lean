/-
A classical comparison of two famous constants:

    e^π > π^e

(equivalently `π > e log π`, or `log π / π < 1/e`). The inequality is
proved with `realfp` in the default kernel-checked mode (Lean's standard
axioms only). Binary64 intervals are already more than enough: the two
sides differ in the second decimal place (`e^π ≈ 23.14`, `π^e ≈ 22.46`).

Copy this file into a Mathlib project that requires `realfp_mathlib`, or run
it from a checkout of realfp:

    cd RealFPMathlib && lake lean RealFPMathlib/Examples/ExpPi.lean
-/
import RealFPMathlib

namespace RealFP.Examples.ExpPi

/-- `e^π > π^e`, written as `π > e log π`. -/
theorem exp_pi_gt_pi_exp : Real.exp 1 * Real.log Real.pi < Real.pi := by
  realfp

/-- The same comparison, in exponential form. -/
theorem exp_pi_gt_pi_exp' : Real.exp (Real.exp 1 * Real.log Real.pi) < Real.exp Real.pi := by
  realfp

end RealFP.Examples.ExpPi
