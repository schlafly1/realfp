/-
Kernel-checked replacement for the `native_decide` fact `demoHi ≤ 3.75`
(`Interval64.NativeDecide.demoHi_le`): the Lean interval evaluation is rewritten to
the Nat mirror `KI` (`mul_toI`, `add_toI`) and the comparison to `KF.le` (`le_toF`),
which the kernel evaluates directly (`decide +kernel`).
-/
import Interval64Proofs.KernelInterval
import Interval64.NativeDecide

namespace Interval64.KF

open Interval64.NativeDecide

/-- `demoIv = [0.5, 1.5]` as bit patterns. -/
def demoK : KI := ⟨0x3FE0000000000000, 0x3FF8000000000000⟩

theorem demoK_wf : WF demoK := ⟨by decide, by decide⟩

theorem demoIv_eq : demoIv = toI demoK := by
  have h1 : toF 0x3FE0000000000000 = 0.5 := by decide +kernel
  have h2 : toF 0x3FF8000000000000 = 1.5 := by decide +kernel
  simp only [demoIv, toI, demoK, h1, h2]

/-- `demoHi ≤ 3.75`, checked by the kernel (no `native_decide`). -/
theorem demoHi_le_kernel : demoHi ≤ 3.75 := by
  have hm := mul_wf demoK_wf demoK_wf
  have e : demoHi = toF (KI.add (KI.mul demoK demoK) demoK).hi := by
    rw [show demoHi = (demoIv * demoIv + demoIv).hi from rfl, demoIv_eq,
      ← mul_toI demoK_wf demoK_wf, ← add_toI hm demoK_wf]
    rfl
  have h3 : (3.75 : Float) = toF 0x400E000000000000 := by decide +kernel
  rw [e, h3]
  have hl := le_toF (add_wf hm demoK_wf).2 (show 0x400E000000000000 < 2 ^ 64 by decide)
  have hk : le (KI.add (KI.mul demoK demoK) demoK).hi 0x400E000000000000 = true := by decide +kernel
  rw [hk] at hl
  exact of_decide_eq_true hl

/-- Generic kernel route for `X.hi ≤ c`: rewrite `X` to a `KI` term and compare bits. -/
theorem hi_le_of_KI {a : KI} (ha : WF a) {X : Interval64} (hX : X = toI a) {c : Float} {n : Nat}
    (hn : n < 2 ^ 64) (hc : c = toF n) (h : le a.hi n = true) : X.hi ≤ c := by
  subst hX hc
  have hl := le_toF ha.2 hn
  rw [h] at hl
  exact of_decide_eq_true hl

end Interval64.KF
