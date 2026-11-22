/-
Positive-definiteness certificates, checked by the kernel (`decide +kernel` runs the
Lean specification of `isPD`; no `native_decide`, standard axioms only).

* `hilbert_posDef` : the 6×6 Hilbert matrix `1 / (i + j + 1)` is positive definite.
* `hilbert3_eigen_gt` : every eigenvalue of the 3×3 Hilbert matrix exceeds `0.0026`
  (`λ_min ≈ 0.002687`).
-/
import RealFPMathlib.Matrix

open Interval64 Interval64.Mat RealFP RealFP.Mat Matrix

namespace RealFP.Examples.MatrixPD

/-- Interval enclosure of the `n × n` Hilbert matrix (outward-rounded rationals). -/
def hilbI (n : ℕ) : IMat := IMat.ofFn n fun i j => ((1 / ((i : ℚ) + j + 1) : ℚ) : Interval64)

/-- The real Hilbert matrix. -/
noncomputable def hilbert (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 1 / ((i : ℝ) + j + 1)

theorem hilbert_symm (n : ℕ) : (hilbert n)ᵀ = hilbert n := by
  ext i j; simp [hilbert, add_comm]

theorem hilbert_mem (n : ℕ) : (hilbI n).Mem (hilbert n) := by
  intro i j
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  change i < n at hi
  change j < n at hj
  show hilbert n ⟨i, hi⟩ ⟨j, hj⟩ ∈ (IMat.ofFn n _).get i j
  rw [get_ofFn hi hj]
  have := ratCoe_mem (1 / ((i : ℚ) + j + 1))
  push_cast at this
  simpa [hilbert] using this

theorem isPD_hilbI6 : isPD (hilbI 6) = true := by decide +kernel

/-- **The 6×6 Hilbert matrix is positive definite.** -/
theorem hilbert_posDef : (hilbert 6).PosDef :=
  posDef_of_isPD isPD_hilbI6 (hilbert_symm 6) (hilbert_mem 6)

theorem lamMinGt_hilbI3 : lamMinGt (hilbI 3) 0.0026 = true := by decide +kernel

/-- `H₃ − 0.0026 · I` is positive definite. -/
theorem hilbert3_sub_posDef :
    (hilbert 3 - (0.0026 : Float).toReal • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  posDef_sub_of_lamMinGt lamMinGt_hilbI3 (hilbert_symm 3) (hilbert_mem 3)

/-- Every eigenvalue of `H₃` exceeds `0.0026`. -/
theorem hilbert3_eigen_gt {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' (hilbert 3)) μ) :
    (0.0026 : Float).toReal < μ :=
  lt_eigenvalue_of_lamMinCheck lamMinGt_hilbI3 (hilbert_symm 3) (hilbert_mem 3) hμ

end RealFP.Examples.MatrixPD
