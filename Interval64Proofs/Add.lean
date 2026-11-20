/-
Scalar addition encloses the exact rational sum, including overflow.
-/
import Interval64Proofs.RoundDirected

namespace Interval64Proofs.Add

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Float.Model
open Float.Model.UnpackedFloat

theorem toEVal_addU_zero_zero (s₁ s₂ : Sign) (up : Bool) :
    toEVal (addU (.zero s₁) (.zero s₂) up) = some (.rat 0) := by
  simp [addU]
  split <;> simp

theorem decreaseExponent_snd_of_le (m : Nat) {e t : Int} (h : t ≤ e) :
    (decreaseExponent m e t).2 = t := by
  simp only [decreaseExponent]
  have : 0 ≤ e - t := Int.sub_nonneg_of_le h
  have htn : ((e - t).toNat : Int) = e - t := Int.toNat_of_nonneg this
  omega

/-- Finite addends: after alignment, the integer mantissa is the exact
    signed sum at the common exponent. -/
theorem aligned_sum_eq (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    ((s₁.apply ((decreaseExponent m₁ e₁ (min e₁ e₂)).1 : Int) +
        s₂.apply ((decreaseExponent m₂ e₂ (min e₁ e₂)).1 : Int) : Int) : Rat) *
      pow2 (min e₁ e₂) =
      signedVal s₁ m₁ e₁ + signedVal s₂ m₂ e₂ := by
  have he1 : (decreaseExponent m₁ e₁ (min e₁ e₂)).2 = min e₁ e₂ :=
    decreaseExponent_snd_of_le m₁ (Int.min_le_left _ _)
  have he2 : (decreaseExponent m₂ e₂ (min e₁ e₂)).2 = min e₁ e₂ :=
    decreaseExponent_snd_of_le m₂ (Int.min_le_right _ _)
  have h1 : signedVal s₁ (decreaseExponent m₁ e₁ (min e₁ e₂)).1 (min e₁ e₂) =
      signedVal s₁ m₁ e₁ := by
    have := decreaseExponent_signedVal s₁ m₁ e₁ (min e₁ e₂)
    rwa [he1] at this
  have h2 : signedVal s₂ (decreaseExponent m₂ e₂ (min e₁ e₂)).1 (min e₁ e₂) =
      signedVal s₂ m₂ e₂ := by
    have := decreaseExponent_signedVal s₂ m₂ e₂ (min e₁ e₂)
    rwa [he2] at this
  rw [signedVal_add_aligned, h1, h2]

theorem addU_finite_lo {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    loEncloses? (toEVal (addU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) false))
      (signedVal s₁ m₁ e₁ + signedVal s₂ m₂ e₂) := by
  simp only [addU]
  have hv := aligned_sum_eq s₁ s₂ m₁ m₂ e₁ e₂
  have hnorm := normalizeDirected_lo
    (s₁.apply (decreaseExponent m₁ e₁ (min e₁ e₂)).1 +
      s₂.apply (decreaseExponent m₂ e₂ (min e₁ e₂)).1)
    (min e₁ e₂) (cancelZero false)
  rw [hv] at hnorm
  exact hnorm

theorem addU_finite_hi {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    hiEncloses? (toEVal (addU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) true))
      (signedVal s₁ m₁ e₁ + signedVal s₂ m₂ e₂) := by
  simp only [addU]
  have hv := aligned_sum_eq s₁ s₂ m₁ m₂ e₁ e₂
  have hnorm := normalizeDirected_hi
    (s₁.apply (decreaseExponent m₁ e₁ (min e₁ e₂)).1 +
      s₂.apply (decreaseExponent m₂ e₂ (min e₁ e₂)).1)
    (min e₁ e₂) (cancelZero true)
  rw [hv] at hnorm
  exact hnorm

end Interval64Proofs.Add
