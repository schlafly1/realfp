/-
Examples: `exp 1` and `log 2` enclosed between adjacent doubles.

`E_lo` … `L_hi` are checked by `decide +kernel`, i.e. the Lean kernel runs
the *rational Ziv specification* (`Interval64.Transc`), not the C code, so these
theorems use no `native_decide` axiom. `exp_mem_toSet` / `log_mem_toSet`
transfer the enclosure to `Real.exp` / `Real.log`.
-/
import RealFPMathlib.Transc

open Interval64 Interval64.Spec RealFP RealFP.Transc

namespace RealFP.Examples.Transc

/-- `exp [1, 1]`. -/
def E : Interval64 := Interval64.exp (ofRat 1)
/-- `log [2, 2]`. -/
def L : Interval64 := Interval64.log (ofRat 2)

theorem E_lo : bitsToRat? E.lo.toBits = some (6121026514868073 / 2251799813685248) := by
  decide +kernel
theorem E_hi : bitsToRat? E.hi.toBits = some (3060513257434037 / 1125899906842624) := by
  decide +kernel

theorem exp_one_mem :
    Real.exp 1 ∈ Set.Icc (6121026514868073 / 2251799813685248 : ℝ)
      (3060513257434037 / 1125899906842624) := by
  have h := exp_mem_toSet (mem_toSet_ofRat 1)
  rw [show Interval64.exp (ofRat 1) = E from rfl, toSet_eq_Icc E_lo E_hi] at h
  push_cast at h
  exact h

/-- `e` to 16 significant digits, via adjacent doubles. -/
theorem exp_one_bounds : (2.718281828459045 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 2.7182818284590456 := by
  obtain ⟨h1, h2⟩ := exp_one_mem
  exact ⟨lt_of_lt_of_le (by norm_num) h1, lt_of_le_of_lt h2 (by norm_num)⟩

theorem L_lo : bitsToRat? L.lo.toBits = some (6243314768165359 / 9007199254740992) := by
  decide +kernel
theorem L_hi : bitsToRat? L.hi.toBits = some (390207173010335 / 562949953421312) := by
  decide +kernel

theorem log_two_mem :
    Real.log 2 ∈ Set.Icc (6243314768165359 / 9007199254740992 : ℝ)
      (390207173010335 / 562949953421312) := by
  have h := log_mem_toSet (mem_toSet_ofRat 2) (by norm_num)
  rw [show Interval64.log (ofRat 2) = L from rfl, toSet_eq_Icc L_lo L_hi] at h
  push_cast at h
  exact h

theorem log_two_bounds :
    (0.6931471805599452 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931471805599455 := by
  obtain ⟨h1, h2⟩ := log_two_mem
  exact ⟨lt_of_lt_of_le (by norm_num) h1, lt_of_le_of_lt h2 (by norm_num)⟩

end RealFP.Examples.Transc
