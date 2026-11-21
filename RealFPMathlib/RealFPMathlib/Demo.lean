/-
Demo: facts about *real* numbers proved by running the interval code.

The numeric facts are checked by `native_decide` (compiled code, which calls
the C kernels through `@[implemented_by]`); the lifted theorems
(`add_mem_toSet`, `mem_toSet_mul`, `mem_toSet_sqrt`, …) do the rest.
`native_decide` adds one axiom per use, so these theorems are fine in your own
projects but would not be accepted in Mathlib itself.

Not imported by `RealFPMathlib`; it is built as part of the library so the
demo is checked on every `lake build`.
-/
import RealFPMathlib.Tight
import RealFPMathlib.Unbounded

open Interval64 Interval64.Spec Interval64Proofs.FloatBits

namespace RealFP.Demo

/-- `[1/10, 3/10]`, rounded outward. -/
def I : Interval64 := ofRatInterval (1/10) (3/10)
/-- `I * I + I`, evaluated with directed rounding. -/
def J : Interval64 := I * I + I

theorem I_lo_fin : ∃ q, bitsToRat? I.lo.toBits = some q :=
  Option.isSome_iff_exists.mp (by decide +kernel)
theorem I_hi_fin : ∃ q, bitsToRat? I.hi.toBits = some q :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- The only numeric fact: compiled interval evaluation. -/
theorem J_hi_le : J.hi ≤ 0.40625 := by native_decide

/-- **Real** statement: `∀ x ∈ [1/10, 3/10], x² + x ≤ 13/32`. -/
theorem sq_add_le (x : ℝ) (hx : x ∈ Set.Icc (1/10 : ℝ) (3/10)) : x * x + x ≤ 13/32 := by
  have hxI : x ∈ I.toSet :=
    mem_toSet_ofRatInterval (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  have hJ : x * x + x ∈ J.toSet :=
    add_mem_toSet (mem_toSet_mul hxI hxI) hxI
  have h := le_of_mem_toSet_of_hi_le (q := 13/32) hJ J_hi_le (by decide +kernel)
  push_cast at h
  linarith

/-- `√2` enclosed between two adjacent doubles. -/
def S : Interval64 := Interval64.sqrt (ofRat 2)

theorem S_lo : bitsToRat? S.lo.toBits = some (1592262918131443 / 1125899906842624) := by
  native_decide
theorem S_hi : bitsToRat? S.hi.toBits = some (6369051672525773 / 4503599627370496) := by
  native_decide

theorem sqrt_two_mem :
    Real.sqrt 2 ∈ Set.Icc (1592262918131443 / 1125899906842624 : ℝ)
      (6369051672525773 / 4503599627370496) := by
  have h2 : ((2 : ℚ) : ℝ) ∈ (ofRat 2).toSet := mem_toSet_ofRat 2
  have h := mem_toSet_sqrt h2 (by norm_num)
  rw [show Interval64.sqrt (ofRat 2) = S from rfl, toSet_eq_Icc S_lo S_hi] at h
  push_cast at h
  simpa using h

theorem sqrt_two_bounds : (1.41421356 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421357 := by
  obtain ⟨h1, h2⟩ := sqrt_two_mem
  exact ⟨lt_of_lt_of_le (by norm_num) h1, lt_of_le_of_lt h2 (by norm_num)⟩

/-- `√x ≤ 111/64` for every real `x ∈ [2, 3]`. -/
def K : Interval64 := Interval64.sqrt (ofRatInterval 2 3)

theorem K_hi_le : K.hi ≤ 1.734375 := by native_decide

theorem sqrt_le_on (x : ℝ) (hx : x ∈ Set.Icc (2 : ℝ) 3) : Real.sqrt x ≤ 111/64 := by
  have hxI : x ∈ (ofRatInterval 2 3).toSet :=
    mem_toSet_ofRatInterval (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  have hK : Real.sqrt x ∈ K.toSet := mem_toSet_sqrt hxI (by linarith [hx.1])
  have h := le_of_mem_toSet_of_hi_le (q := 111/64) hK K_hi_le (by decide +kernel)
  push_cast at h
  linarith

end RealFP.Demo
