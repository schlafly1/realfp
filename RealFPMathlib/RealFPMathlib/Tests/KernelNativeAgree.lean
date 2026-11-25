/-
Regression: the kernel and compiled (native) evaluation of the precision-128 quadrature check
agree, and no tactic proves a false integral bound.

Background (2026-11-24): a 30-digit `quadBoundQ` run for `∫₀¹ e^(-x²)` (bounds
`…131e-30 ≤ ∫ ≤ …132e-30`, mathematically true: `∫ = 0.746824132812427025399467436131853…`)
looked accepted by the kernel. Re-run to completion it is **rejected** by the kernel
(7 min) and `false` natively: the enclosure's upper end is `…1320029e-30 > qh`. The earlier
run had been killed by the OOM killer without output. Below, the same check at order 6 with
the upper bound at the enclosure's end (true in both modes) and one unit of `10^-40` lower
(false in both modes).
-/
import RealFPMathlib.IntegralTactic

open Interval64.KF

set_option maxRecDepth 100000

namespace RealFP.KernelNativeAgree

theorem agree_true : Interval128.Dy.quadBoundQ 6 (.exp (.neg (.pow (.var 0) 2))) 0 1 [1]
    (mkRat 7465677533538126874211951883031141518612 (10 ^ 40))
    (mkRat 7479928639856910560449594711780684619719 (10 ^ 40)) = true := by
  decide +kernel

theorem agree_false : Interval128.Dy.quadBoundQ 6 (.exp (.neg (.pow (.var 0) 2))) 0 1 [1]
    (mkRat 7465677533538126874211951883031141518612 (10 ^ 40))
    (mkRat 7479928639856910560449594711780684619718 (10 ^ 40)) = false := by
  decide +kernel

-- compiled evaluation gives the same answers
#guard Interval128.Dy.quadBoundQ 6 (.exp (.neg (.pow (.var 0) 2))) 0 1 [1]
    (mkRat 7465677533538126874211951883031141518612 (10 ^ 40))
    (mkRat 7479928639856910560449594711780684619719 (10 ^ 40))
#guard !Interval128.Dy.quadBoundQ 6 (.exp (.neg (.pow (.var 0) 2))) 0 1 [1]
    (mkRat 7465677533538126874211951883031141518612 (10 ^ 40))
    (mkRat 7479928639856910560449594711780684619718 (10 ^ 40))

-- false bounds (true value 0.7468241328124270253994674361318…) are refused at both precisions
example : True := by
  fail_if_success (have : (∫ x in (0:ℝ)..1, Real.exp (-x^2)) ≤ 0.7468241328124 := by integral_bound)
  trivial

example : True := by
  fail_if_success (have : (∫ x in (0:ℝ)..1, Real.exp (-x^2)) ≤ 0.74682413281242702539946743613 := by integral_bound (precision := 128))
  trivial

end RealFP.KernelNativeAgree
