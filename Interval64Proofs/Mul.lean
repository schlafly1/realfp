/-
Bits-level directed multiplication enclosure, and interval membership
for finite endpoints via the four-corner rule.
-/
import Interval64Proofs.AddBits
import Interval64Proofs.ExactAdd

namespace Interval64Proofs.Mul

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.ExactAdd
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Algebra of signed products -/

theorem mag_mul (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    mag (m₁ * m₂) (e₁ + e₂) = mag m₁ e₁ * mag m₂ e₂ := by
  unfold mag
  rw [Rat.natCast_mul, pow2_add, Rat.mul_assoc]
  have : (m₂ : Rat) * (pow2 e₁ * pow2 e₂) = pow2 e₁ * ((m₂ : Rat) * pow2 e₂) := by
    rw [← Rat.mul_assoc, Rat.mul_comm (m₂ : Rat) (pow2 e₁), Rat.mul_assoc]
  rw [this, ← Rat.mul_assoc]

theorem signedVal_mul (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    signedVal (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) =
      signedVal s₁ m₁ e₁ * signedVal s₂ m₂ e₂ := by
  cases s₁ <;> cases s₂ <;> simp [signedVal, mag_mul, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem mul_le_mul_nonneg {a b c d : Rat}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hab hc)
    (Rat.mul_le_mul_of_nonneg_left hcd (Rat.le_trans ha hab))

theorem neg_nonneg_of_nonpos {a : Rat} (h : a ≤ 0) : (0 : Rat) ≤ -a := by
  have : -(0 : Rat) ≤ -a := Rat.neg_le_neg h
  simpa [Rat.neg_zero] using this

theorem mul_le_mul_nonpos {a b c d : Rat}
    (hb : b ≤ 0) (hd : d ≤ 0) (hab : a ≤ b) (hcd : c ≤ d) : b * d ≤ a * c := by
  have ha : a ≤ 0 := Rat.le_trans hab hb
  have hc : c ≤ 0 := Rat.le_trans hcd hd
  have h0b : 0 ≤ -b := neg_nonneg_of_nonpos hb
  have h0d : 0 ≤ -d := neg_nonneg_of_nonpos hd
  have hba : -b ≤ -a := (Rat.neg_le_neg_iff).mpr hab
  have hdc : -d ≤ -c := (Rat.neg_le_neg_iff).mpr hcd
  have : (-b) * (-d) ≤ (-a) * (-c) := mul_le_mul_nonneg h0b h0d hba hdc
  simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using this

/-! ### Unpacked finite multiplication encloses the exact product -/

theorem mulU_finite_lo {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    loEncloses? (toEVal (mulU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) false))
      (signedVal s₁ m₁ e₁ * signedVal s₂ m₂ e₂) := by
  simp only [mulU]
  have h := roundDirected_lo (s₁ * s₂) (m₁ * m₂) (e₁ + e₂)
  rwa [signedVal_mul] at h

theorem mulU_finite_hi {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    hiEncloses? (toEVal (mulU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) true))
      (signedVal s₁ m₁ e₁ * signedVal s₂ m₂ e₂) := by
  simp only [mulU]
  have h := roundDirected_hi (s₁ * s₂) (m₁ * m₂) (e₁ + e₂)
  rwa [signedVal_mul] at h

/-! ### Bits-level enclosure of directed mul -/

theorem mul_encloses_lo {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (mulDown a b)) (qa * qb) := by
  simp only [mulDown, Interval64.Spec.mul]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, Rat.zero_mul])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, Rat.zero_mul])
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, _⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, Rat.mul_zero])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      have hlo := mulU_finite_lo (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape := roundDirected_zero_or_shaped (s1 * s2) (m1 * m2) (e1 + e2) false
      have hmul :
          mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
            roundDirected (s1 * s2) (m1 * m2) (e1 + e2) Accuracy.exact false :=
        rfl
      rw [hmul] at hlo ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨m, e, h, heq, hsh⟩
      · rw [heq]
        exact loEncloses_packDirected_zero_val _ _ _ (heq ▸ hlo)
      · rw [heq]
        exact loEncloses_packDirected_of_shaped (s1 * s2) h hsh _ (heq ▸ hlo)

theorem mul_encloses_hi {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    hiEncloses? (bitsToEVal (mulUp a b)) (qa * qb) := by
  simp only [mulUp, Interval64.Spec.mul]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, Rat.zero_mul])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, Rat.zero_mul])
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, _⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [mulU]
      exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, Rat.mul_zero])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
      rw [hu1, hu2]
      have hhi := mulU_finite_hi (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape := roundDirected_zero_or_shaped (s1 * s2) (m1 * m2) (e1 + e2) true
      have hmul :
          mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
            roundDirected (s1 * s2) (m1 * m2) (e1 + e2) Accuracy.exact true :=
        rfl
      rw [hmul] at hhi ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨m, e, h, heq, hsh⟩
      · rw [heq]
        exact hiEncloses_packDirected_zero_val _ _ _ (heq ▸ hhi)
      · rw [heq]
        exact hiEncloses_packDirected_of_shaped (s1 * s2) h hsh _ (heq ▸ hhi)

theorem mul_encloses {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (mulDown a b)) (qa * qb) ∧
    hiEncloses? (bitsToEVal (mulUp a b)) (qa * qb) :=
  ⟨mul_encloses_lo ha hb, mul_encloses_hi ha hb⟩

/-! ### Interval membership: four-corner cases with finite endpoints -/

/-- Both intervals nonnegative: the product sits in `[loX·loY, hiX·hiY]`
    after directed rounding of those two corners. -/
theorem mul_mem_nonneg {x y : Rat} {loX hiX loY hiY : UInt64}
    (hx : Mem x loX hiX) (hy : Mem y loY hiY)
    {qx qy rx ry : Rat}
    (hloX : bitsToRat? loX = some qx) (hloY : bitsToRat? loY = some qy)
    (hhiX : bitsToRat? hiX = some rx) (hhiY : bitsToRat? hiY = some ry)
    (hqx : 0 ≤ qx) (hqy : 0 ≤ qy) :
    Mem (x * y) (mulDown loX loY) (mulUp hiX hiY) := by
  have hlex : qx ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloX] at this
    exact this
  have hley : qy ≤ y := by
    have := hy.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloY] at this
    exact this
  have hgex : x ≤ rx := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiX] at this
    exact this
  have hgey : y ≤ ry := by
    have := hy.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiY] at this
    exact this
  have hx0 : 0 ≤ x := Rat.le_trans hqx hlex
  have hy0 : 0 ≤ y := Rat.le_trans hqy hley
  have hle : qx * qy ≤ x * y := mul_le_mul_nonneg hqx hqy hlex hley
  have hge : x * y ≤ rx * ry := mul_le_mul_nonneg hx0 hy0 hgex hgey
  exact ⟨loEncloses_trans (mul_encloses_lo hloX hloY) hle,
         hiEncloses_trans (mul_encloses_hi hhiX hhiY) hge⟩

/-- Both intervals nonpositive: the product sits in `[hiX·hiY, loX·loY]`. -/
theorem mul_mem_nonpos {x y : Rat} {loX hiX loY hiY : UInt64}
    (hx : Mem x loX hiX) (hy : Mem y loY hiY)
    {qx qy rx ry : Rat}
    (hloX : bitsToRat? loX = some qx) (hloY : bitsToRat? loY = some qy)
    (hhiX : bitsToRat? hiX = some rx) (hhiY : bitsToRat? hiY = some ry)
    (hrx : rx ≤ 0) (hry : ry ≤ 0) :
    Mem (x * y) (mulDown hiX hiY) (mulUp loX loY) := by
  have hlex : qx ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloX] at this
    exact this
  have hley : qy ≤ y := by
    have := hy.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloY] at this
    exact this
  have hgex : x ≤ rx := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiX] at this
    exact this
  have hgey : y ≤ ry := by
    have := hy.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiY] at this
    exact this
  have hx0 : x ≤ 0 := Rat.le_trans hgex hrx
  have hy0 : y ≤ 0 := Rat.le_trans hgey hry
  have hle : rx * ry ≤ x * y := mul_le_mul_nonpos hrx hry hgex hgey
  have hge : x * y ≤ qx * qy := mul_le_mul_nonpos hx0 hy0 hlex hley
  exact ⟨loEncloses_trans (mul_encloses_lo hhiX hhiY) hle,
         hiEncloses_trans (mul_encloses_hi hloX hloY) hge⟩

/-- `X` nonnegative and `Y` nonpositive: the product sits in `[hiX·loY, loX·hiY]`. -/
theorem mul_mem_nonneg_nonpos {x y : Rat} {loX hiX loY hiY : UInt64}
    (hx : Mem x loX hiX) (hy : Mem y loY hiY)
    {qx qy rx ry : Rat}
    (hloX : bitsToRat? loX = some qx) (hloY : bitsToRat? loY = some qy)
    (hhiX : bitsToRat? hiX = some rx) (hhiY : bitsToRat? hiY = some ry)
    (hqx : 0 ≤ qx) (hry : ry ≤ 0) :
    Mem (x * y) (mulDown hiX loY) (mulUp loX hiY) := by
  have hlex : qx ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloX] at this
    exact this
  have hley : qy ≤ y := by
    have := hy.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloY] at this
    exact this
  have hgex : x ≤ rx := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiX] at this
    exact this
  have hgey : y ≤ ry := by
    have := hy.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiY] at this
    exact this
  have hx0 : 0 ≤ x := Rat.le_trans hqx hlex
  have hy0 : y ≤ 0 := Rat.le_trans hgey hry
  -- rx*qy ≤ x*y ≤ qx*ry
  have hle : rx * qy ≤ x * y := by
    have h1 : rx * qy ≤ rx * y := by
      have : qy ≤ y := hley
      have hr0 : 0 ≤ rx := Rat.le_trans hx0 hgex
      exact Rat.mul_le_mul_of_nonneg_left this hr0
    have h2 : rx * y ≤ x * y := by
      have : y ≤ 0 := hy0
      have hxr : x ≤ rx := hgex
      have := Rat.mul_le_mul_of_nonneg_right (c := -y) hxr (neg_nonneg_of_nonpos this)
      simpa [Rat.mul_neg, Rat.neg_le_neg_iff] using this
    exact Rat.le_trans h1 h2
  have hge : x * y ≤ qx * ry := by
    have h1 : x * y ≤ qx * y := by
      have := Rat.mul_le_mul_of_nonneg_right (c := -y) hlex (neg_nonneg_of_nonpos hy0)
      simpa [Rat.mul_neg, Rat.neg_le_neg_iff] using this
    have h2 : qx * y ≤ qx * ry :=
      Rat.mul_le_mul_of_nonneg_left hgey hqx
    exact Rat.le_trans h1 h2
  exact ⟨loEncloses_trans (mul_encloses_lo hhiX hloY) hle,
         hiEncloses_trans (mul_encloses_hi hloX hhiY) hge⟩

/-- `X` nonpositive and `Y` nonnegative: the product sits in `[loX·hiY, hiX·loY]`. -/
theorem mul_mem_nonpos_nonneg {x y : Rat} {loX hiX loY hiY : UInt64}
    (hx : Mem x loX hiX) (hy : Mem y loY hiY)
    {qx qy rx ry : Rat}
    (hloX : bitsToRat? loX = some qx) (hloY : bitsToRat? loY = some qy)
    (hhiX : bitsToRat? hiX = some rx) (hhiY : bitsToRat? hiY = some ry)
    (hrx : rx ≤ 0) (hqy : 0 ≤ qy) :
    Mem (x * y) (mulDown loX hiY) (mulUp hiX loY) := by
  have hlex : qx ≤ x := by
    have := hx.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloX] at this
    exact this
  have hley : qy ≤ y := by
    have := hy.1
    simp [loEncloses?, loEncloses, bitsToEVal_rat_of_bitsToRat? hloY] at this
    exact this
  have hgex : x ≤ rx := by
    have := hx.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiX] at this
    exact this
  have hgey : y ≤ ry := by
    have := hy.2
    simp [hiEncloses?, hiEncloses, bitsToEVal_rat_of_bitsToRat? hhiY] at this
    exact this
  have hx0 : x ≤ 0 := Rat.le_trans hgex hrx
  have hy0 : 0 ≤ y := Rat.le_trans hqy hley
  have hle : qx * ry ≤ x * y := by
    have hry0 : 0 ≤ ry := Rat.le_trans hy0 hgey
    have h1 : qx * ry ≤ x * ry :=
      Rat.mul_le_mul_of_nonneg_right hlex hry0
    have h2 : x * ry ≤ x * y := by
      have := Rat.mul_le_mul_of_nonneg_right (c := -x) hgey (neg_nonneg_of_nonpos hx0)
      simpa [Rat.mul_comm, Rat.mul_neg, Rat.neg_le_neg_iff] using this
    exact Rat.le_trans h1 h2
  have hge : x * y ≤ rx * qy := by
    have h1 : x * y ≤ rx * y :=
      Rat.mul_le_mul_of_nonneg_right hgex hy0
    have h2 : rx * y ≤ rx * qy := by
      have := Rat.mul_le_mul_of_nonneg_right (c := -rx) hley (neg_nonneg_of_nonpos hrx)
      simpa [Rat.mul_comm, Rat.mul_neg, Rat.neg_le_neg_iff] using this
    exact Rat.le_trans h1 h2
  exact ⟨loEncloses_trans (mul_encloses_lo hloX hhiY) hle,
         hiEncloses_trans (mul_encloses_hi hhiX hloY) hge⟩


/-! ### Exactness when the product is a representable binary64 value -/

theorem signedVal_mul_ne_zero {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    signedVal s₁ m₁ e₁ * signedVal s₂ m₂ e₂ ≠ 0 := by
  rw [← signedVal_mul]
  exact signedVal_ne_zero_of_pos (Nat.mul_pos h₁ h₂)



theorem mul_exact {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hrep : ∃ c, bitsToRat? c = some (qa * qb)) :
    bitsToRat? (mulDown a b) = some (qa * qb) ∧
    bitsToRat? (mulUp a b) = some (qa * qb) := by
  rcases representable_cases hrep with hq0 | hqf
  · have hboth : bitsToRat? (mulDown a b) = some 0 ∧
        bitsToRat? (mulUp a b) = some 0 := by
      simp only [mulDown, mulUp, Interval64.Spec.mul]
      rcases bitsToRat?_cases ha with hza | hfa
      · rcases hza with ⟨s1, hu1, rfl⟩
        rcases bitsToRat?_cases hb with hzb | hfb
        · rcases hzb with ⟨s2, hu2, rfl⟩
          rw [hu1, hu2]
          simp only [mulU]
          constructor <;> exact bitsToRat?_packDirected_zero _ _
        · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
          rw [hu1, hu2]
          simp only [mulU]
          constructor <;> exact bitsToRat?_packDirected_zero _ _
      · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, _⟩
        rcases bitsToRat?_cases hb with hzb | hfb
        · rcases hzb with ⟨s2, hu2, rfl⟩
          rw [hu1, hu2]
          simp only [mulU]
          constructor <;> exact bitsToRat?_packDirected_zero _ _
        · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
          exact (signedVal_mul_ne_zero h1 h2 hq0).elim
    rw [hq0]
    exact hboth
  · rcases hqf with ⟨sCan, m', e', h', hc, hvq⟩
    simp only [mulDown, mulUp, Interval64.Spec.mul]
    rcases bitsToRat?_cases ha with hza | hfa
    · rcases hza with ⟨s1, hu1, rfl⟩
      have : (0 : Rat) * qb = signedVal sCan m' e' := hvq
      rw [Rat.zero_mul] at this
      exact (signedVal_ne_zero_of_pos h' this.symm).elim
    · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, _⟩
      rcases bitsToRat?_cases hb with hzb | hfb
      · rcases hzb with ⟨s2, hu2, rfl⟩
        have : signedVal s1 m1 e1 * 0 = signedVal sCan m' e' := hvq
        rw [Rat.mul_zero] at this
        exact (signedVal_ne_zero_of_pos h' this.symm).elim
      · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, _⟩
        rw [hu1, hu2]
        have hvprod :
            signedVal (s1 * s2) (m1 * m2) (e1 + e2) = signedVal sCan m' e' := by
          rw [signedVal_mul, hvq]
        have hs : s1 * s2 = sCan := by
          cases sCan with
          | positive =>
            cases hdir : (s1 * s2) with
            | positive => rfl
            | negative =>
              rw [hdir] at hvprod
              simp [signedVal] at hvprod
              have hp : (0 : Rat) < -mag (m1 * m2) (e1 + e2) :=
                hvprod.symm ▸ mag_pos h'
              have hn : mag (m1 * m2) (e1 + e2) < 0 := by
                have := Rat.neg_lt_neg hp
                simpa [Rat.neg_neg, Rat.neg_zero] using this
              exact ((Rat.lt_iff_le_and_not_ge.mp hn).2
                (Rat.le_of_lt (mag_pos (Nat.mul_pos h1 h2)))).elim
          | negative =>
            cases hdir : (s1 * s2) with
            | negative => rfl
            | positive =>
              rw [hdir] at hvprod
              simp [signedVal] at hvprod
              have hp : (0 : Rat) < -mag m' e' :=
                hvprod ▸ mag_pos (Nat.mul_pos h1 h2)
              have hn : mag m' e' < 0 := by
                have := Rat.neg_lt_neg hp
                simpa [Rat.neg_neg, Rat.neg_zero] using this
              exact ((Rat.lt_iff_le_and_not_ge.mp hn).2
                (Rat.le_of_lt (mag_pos h'))).elim
        have hvprod' : signedVal sCan (m1 * m2) (e1 + e2) = signedVal sCan m' e' := by
          rw [hs] at hvprod
          exact hvprod
        constructor
        · have heq :=
            roundDirected_eq_of_canonical sCan (m1 * m2) (e1 + e2) false h' hc hvprod'
          have hmul :
              mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
                roundDirected (s1 * s2) (m1 * m2) (e1 + e2) Accuracy.exact false :=
            rfl
          rw [hmul, hs, heq]
          simpa [hvq] using bitsToRat?_packDirected_canonical false sCan h' hc
        · have heq :=
            roundDirected_eq_of_canonical sCan (m1 * m2) (e1 + e2) true h' hc hvprod'
          have hmul :
              mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
                roundDirected (s1 * s2) (m1 * m2) (e1 + e2) Accuracy.exact true :=
            rfl
          rw [hmul, hs, heq]
          simpa [hvq] using bitsToRat?_packDirected_canonical true sCan h' hc

theorem mul_exact_int {a b : UInt64} {na nb : Int}
    (ha : bitsToRat? a = some (na : Rat)) (hb : bitsToRat? b = some (nb : Rat))
    (_hna : na.natAbs ≤ 2 ^ 53) (_hnb : nb.natAbs ≤ 2 ^ 53)
    (hprod : (na * nb).natAbs ≤ 2 ^ 53) :
    bitsToRat? (mulDown a b) = some ((na * nb : Int) : Rat) ∧
    bitsToRat? (mulUp a b) = some ((na * nb : Int) : Rat) := by
  rcases int_le_pow53_representable (na * nb) hprod with ⟨c, hc⟩
  have hcast : ((na : Rat) * (nb : Rat)) = ((na * nb : Int) : Rat) :=
    (Rat.intCast_mul na nb).symm
  have hrep : ∃ c, bitsToRat? c = some ((na : Rat) * (nb : Rat)) :=
    ⟨c, hc.trans (congrArg some hcast.symm)⟩
  have hmul := mul_exact ha hb hrep
  rw [hcast] at hmul
  exact hmul

end Interval64Proofs.Mul

