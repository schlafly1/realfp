/-
Positive-definiteness certificates, checked by the kernel (no `native_decide`, standard axioms
only).

* `hilbert_posDef` (6×6) uses the Float-spec check `isPD` (`decide +kernel` on the Lean spec).
* `hilbert10_posDef` uses the kernel fast path: `ki_lit%` (rational entries rounded natively
  to bit patterns), `pd_certs%` (congruence `X` and the intermediate `T`, `B`, computed natively),
  `ratMatOK` (each entry contains its rational) and `pdCheckL`, both by `decide +kernel`.
* `hilbert3_eigen_gt` : every eigenvalue of `H₃` exceeds `0.0026` (Float-spec `lamMinGt`).
* `hilbert8_eigen_gt` : every eigenvalue of `H₈` exceeds `10⁻¹⁰` (`λ_min ≈ 1.11·10⁻¹⁰`).
-/
import RealFPMathlib.KMatrix

open Interval64 Interval64.Mat RealFP RealFP.Mat Matrix Interval64.KF Interval64.KF.KM RealFP.KM

namespace RealFP.Examples.MatrixPD

/-! ### Float-spec path -/

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

/-- The 6×6 Hilbert matrix is positive definite (Float-spec path). -/
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

/-! ### Kernel fast path -/

def hq (i j : ℕ) : ℚ := 1 / ((i : ℚ) + j + 1)

theorem hilbert_eq (n : ℕ) : hilbert n = Matrix.of fun i j : Fin n => ((hq i j : ℚ) : ℝ) := by
  ext i j; simp [hilbert, hq]

def H10 : Array KI := ki_lit% (ofRatFn 10 hq)

/-- **The 10×10 Hilbert matrix is positive definite** (condition number ≈ 1.6·10¹³). -/
theorem hilbert10_posDef : (hilbert 10).PosDef := by
  rw [hilbert_eq]
  exact posDef_of_ratMat (A := H10) (c := pd_certs% 10 H10) (by decide +kernel)
    (by decide +kernel) (fun i j _ _ => by simp [hq, add_comm])

/-- `H₈ - 10⁻¹⁰ I`, entrywise. -/
def hs8 (i j : ℕ) : ℚ := hq i j - if i = j then 1 / 10 ^ 10 else 0

def H8s : Array KI := ki_lit% (ofRatFn 8 hs8)

theorem hilbert8_sub_posDef :
    (hilbert 8 - ((1 / 10 ^ 10 : ℚ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)).PosDef := by
  have e : hilbert 8 - ((1 / 10 ^ 10 : ℚ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) =
      Matrix.of fun i j : Fin 8 => ((hs8 i j : ℚ) : ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hilbert, hs8, hq]
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
      simp [hilbert, hs8, hq, h, h', Matrix.one_apply_ne h]
  rw [e]
  exact posDef_of_ratMat (A := H8s) (c := pd_certs% 8 H8s) (by decide +kernel)
    (by decide +kernel) (fun i j _ _ => by simp only [hs8, hq, eq_comm (a := i)]; ring_nf)

/-- Every eigenvalue of `H₈` exceeds `10⁻¹⁰`. -/
theorem hilbert8_eigen_gt {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' (hilbert 8)) μ) :
    ((1 / 10 ^ 10 : ℚ) : ℝ) < μ :=
  lt_eigenvalue_of_posDef_sub hilbert8_sub_posDef hμ

end RealFP.Examples.MatrixPD
