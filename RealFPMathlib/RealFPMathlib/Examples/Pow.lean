/-
Example: `2 ^ (1/2 : ℝ)` (`Real.rpow`) enclosed between adjacent doubles by
`Interval64.rpow = exp (Y * log X)`, endpoints checked by `decide +kernel` (no `native_decide`).
-/
import RealFPMathlib.Pow

open Interval64 Interval64.Spec RealFP RealFP.Pow

namespace RealFP.Examples.Pow

/-- `rpow [2, 2] [1/2, 1/2]`. -/
def R : Interval64 := Interval64.rpow (ofRat 2) (ofRat (1/2))

theorem R_lo : bitsToRat? R.lo.toBits = some (1592262918131443 / 1125899906842624) := by
  decide +kernel
theorem R_hi : bitsToRat? R.hi.toBits = some (6369051672525773 / 4503599627370496) := by
  decide +kernel

theorem rpow_two_half_mem :
    (2 : ℝ) ^ (1/2 : ℝ) ∈ Set.Icc (1592262918131443 / 1125899906842624 : ℝ)
      (6369051672525773 / 4503599627370496) := by
  have h := rpow_mem_toSet (mem_toSet_ofRat 2) (mem_toSet_ofRat (1/2)) (by norm_num)
  rw [show Interval64.rpow (ofRat 2) (ofRat (1/2)) = R from rfl, toSet_eq_Icc R_lo R_hi] at h
  push_cast at h
  exact h

theorem rpow_two_half_bounds :
    (1.4142135623 : ℝ) < (2 : ℝ) ^ (1/2 : ℝ) ∧ (2 : ℝ) ^ (1/2 : ℝ) < 1.4142135624 := by
  obtain ⟨h1, h2⟩ := rpow_two_half_mem
  exact ⟨lt_of_lt_of_le (by norm_num) h1, lt_of_le_of_lt h2 (by norm_num)⟩

end RealFP.Examples.Pow
