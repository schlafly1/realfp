/-
Interval128 proofs, part 1: one-sided facts about the binary64 operations used
by the double-double kernels, in the form the kernel proofs need:

  "if the directed result is finite, every operand is finite and the result
   is a one-sided bound of the exact real operation".

* `addDown_fin`, `addUp_fin`, `subDown_fin`, `subUp_fin`, `mulDown_fin`,
  `mulUp_fin`, `fmaDown_fin`, `fmaUp_fin` (new: directed FMA), `divDown_fin`,
  `divUp_fin` (finite non-zero divisor), `sqrtDown_fin`, `sqrtUp_fin`.
* `fv_neg` : negation is exact.
* Float comparisons of finite values are real comparisons.
-/
import RealFPMathlib.Ops
import RealFPMathlib.Tight
import Interval128

open Interval64 Interval64.Spec Interval64.Directed
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pack Interval64Proofs.PackFinite Interval64Proofs.RoundDirected
open Interval64Proofs.Add Interval64Proofs.Mul Interval64Proofs.Pow2
open Float.Model Float.Model.UnpackedFloat

namespace RealFP.I128

/-! ### Finite values -/

/-- `f` is finite with exact value `x`. -/
abbrev Fv (f : Float) (x : ℝ) : Prop := f.toReal? = some x

theorem fv_unique {f : Float} {x y : ℝ} (hx : Fv f x) (hy : Fv f y) : x = y := by
  unfold Fv at hx hy; rw [hx] at hy; exact Option.some.inj hy

/-- Not a finite value: NaN or an infinity. -/
def NF (u : UnpackedFloat) : Prop := u = .notANumber ∨ ∃ s, u = .infinity s

theorem toReal?_of_NF {f : Float} (h : NF (unpackBits f.toBits)) : f.toReal? = none := by
  rcases h with h | ⟨s, h⟩ <;> simp [Float.toReal?, bitsToRat?, h, toRat?]

theorem fin_or_NF (f : Float) : (∃ x, Fv f x) ∨ NF (unpackBits f.toBits) := by
  cases hu : unpackBits f.toBits with
  | notANumber => exact Or.inr (Or.inl rfl)
  | infinity s => exact Or.inr (Or.inr ⟨s, rfl⟩)
  | zero s => exact Or.inl ⟨0, by unfold Fv; simp [Float.toReal?, bitsToRat?, hu, toRat?]⟩
  | finite s m e hm =>
    exact Or.inl ⟨_, by unfold Fv; simp only [Float.toReal?, bitsToRat?, hu]; rfl⟩

theorem unpackBits_nan : unpackBits (packBits .notANumber) = .notANumber := by
  rw [unpackBits_packBits]; rfl

theorem unpack_ofBits_packDirected_NF {u : UnpackedFloat} (up : Bool) (h : NF u) :
    NF (unpackBits (Float.ofBits (packDirected up u)).toBits) := by
  rw [toBits_ofBits]
  rcases h with rfl | ⟨s, rfl⟩
  · left
    show unpackBits (packBits (unpackBits (packBits .notANumber))) = _
    rw [unpackBits_nan, unpackBits_nan]
  · right; refine ⟨s, ?_⟩
    show unpackBits (packBits (unpackBits (packBits (.infinity s)))) = _
    rw [unpackBits_inf, unpackBits_inf]

theorem none_of_NF {u : UnpackedFloat} (up : Bool) (h : NF u) :
    (Float.ofBits (packDirected up u)).toReal? = none :=
  toReal?_of_NF (unpack_ofBits_packDirected_NF up h)

theorem not_fv_of_NF {u : UnpackedFloat} {up : Bool} {r : ℝ} (h : NF u) :
    ¬ Fv (Float.ofBits (packDirected up u)) r := by
  unfold Fv; rw [none_of_NF up h]; simp

/-! ### Non-finite operands propagate -/

theorem addU_NF_left {x : UnpackedFloat} (y : UnpackedFloat) (up : Bool) (h : NF x) :
    NF (addU x y up) := by
  rcases h with rfl | ⟨s, rfl⟩
  · left; cases y <;> rfl
  · cases y with
    | notANumber => left; rfl
    | infinity t =>
      simp only [addU]; split
      · right; exact ⟨s, rfl⟩
      · left; rfl
    | zero t => right; exact ⟨s, rfl⟩
    | finite t m e hm => right; exact ⟨s, rfl⟩

theorem addU_NF_right (x : UnpackedFloat) {y : UnpackedFloat} (up : Bool) (h : NF y) :
    NF (addU x y up) := by
  rcases h with rfl | ⟨s, rfl⟩
  · left; cases x <;> rfl
  · cases x with
    | notANumber => left; rfl
    | infinity t =>
      simp only [addU]; split
      · right; exact ⟨t, rfl⟩
      · left; rfl
    | zero t => right; exact ⟨s, rfl⟩
    | finite t m e hm => right; exact ⟨s, rfl⟩

theorem NF_neg {y : UnpackedFloat} (h : NF y) : NF y.neg := by
  rcases h with rfl | ⟨s, rfl⟩
  · left; rfl
  · right; exact ⟨-s, rfl⟩

theorem mulU_NF_left {x : UnpackedFloat} (y : UnpackedFloat) (up : Bool) (h : NF x) :
    NF (mulU x y up) := by
  rcases h with rfl | ⟨s, rfl⟩
  · left; cases y <;> rfl
  · cases y with
    | notANumber => left; rfl
    | infinity t => right; exact ⟨_, rfl⟩
    | zero t => left; rfl
    | finite t m e hm => right; exact ⟨_, rfl⟩

theorem mulU_NF_right (x : UnpackedFloat) {y : UnpackedFloat} (up : Bool) (h : NF y) :
    NF (mulU x y up) := by
  rcases h with rfl | ⟨s, rfl⟩
  · left; cases x <;> rfl
  · cases x with
    | notANumber => left; rfl
    | infinity t => right; exact ⟨_, rfl⟩
    | zero t => left; rfl
    | finite t m e hm => right; exact ⟨_, rfl⟩

theorem fmaU_NF (x y z : UnpackedFloat) (up : Bool) (h : NF x ∨ NF y ∨ NF z) :
    NF (fmaU x y z up) := by
  unfold fmaU
  split
  · rename_i s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂
    rcases h with h | h | h
    · rcases h with h | ⟨_, h⟩ <;> cases h
    · rcases h with h | ⟨_, h⟩ <;> cases h
    · split
      · rcases h with h | ⟨_, h⟩ <;> cases h
      · exact addU_NF_right _ up h
  · rcases h with h | h | h
    · exact addU_NF_left _ up (mulU_NF_left _ up h)
    · exact addU_NF_left _ up (mulU_NF_right _ up h)
    · exact addU_NF_right _ up h

theorem divU_NF_left {x : UnpackedFloat} {s : Sign} {m : Nat} {e : Int} {hm : 0 < m}
    (up : Bool) (h : NF x) : NF (divU x (.finite s m e hm) up) := by
  rcases h with rfl | ⟨t, rfl⟩
  · left; rfl
  · right; exact ⟨_, rfl⟩

theorem sqrtU_NF {x : UnpackedFloat} (up : Bool) (h : NF x) : NF (sqrtU x up) := by
  rcases h with rfl | ⟨t, rfl⟩
  · left; rfl
  · cases t
    · left; rfl
    · right; exact ⟨_, rfl⟩

/-! ### From `loR` / `hiR` of a finite result to a real inequality -/

theorem le_of_loR {f : Float} {r z : ℝ} (h : Fv f r) (hl : loR (bitsToEVal f.toBits) z) :
    r ≤ z := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 h
  rw [bitsToEVal_rat_of_bitsToRat? hq] at hl; exact hl

theorem ge_of_hiR {f : Float} {r z : ℝ} (h : Fv f r) (hl : hiR (bitsToEVal f.toBits) z) :
    z ≤ r := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 h
  rw [bitsToEVal_rat_of_bitsToRat? hq] at hl; exact hl

/-! ### Directed add / sub / mul -/

section
variable {a b : Float} {r : ℝ}

theorem addDown_fin (h : Fv (addDown a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ r ≤ x + y := by
  have e : addDown a b = Float.ofBits (packDirected false
      (addU (unpackBits a.toBits) (unpackBits b.toBits) false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, le_of_loR h (addDown_isRoundDownR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_right _ _ hb))
  · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_left _ _ ha))

theorem addUp_fin (h : Fv (addUp a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ x + y ≤ r := by
  have e : addUp a b = Float.ofBits (packDirected true
      (addU (unpackBits a.toBits) (unpackBits b.toBits) true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, ge_of_hiR h (addUp_isRoundUpR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_right _ _ hb))
  · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_left _ _ ha))

theorem subDown_fin (h : Fv (subDown a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ r ≤ x - y := by
  have e : subDown a b = Float.ofBits (packDirected false
      (addU (unpackBits a.toBits) (unpackBits b.toBits).neg false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, le_of_loR h (subDown_isRoundDownR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_right _ _ (NF_neg hb)))
  · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_left _ _ ha))

theorem subUp_fin (h : Fv (subUp a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ x - y ≤ r := by
  have e : subUp a b = Float.ofBits (packDirected true
      (addU (unpackBits a.toBits) (unpackBits b.toBits).neg true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, ge_of_hiR h (subUp_isRoundUpR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_right _ _ (NF_neg hb)))
  · rw [e] at h; exact absurd h (not_fv_of_NF (addU_NF_left _ _ ha))

theorem mulDown_fin (h : Fv (mulDown a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ r ≤ x * y := by
  have e : mulDown a b = Float.ofBits (packDirected false
      (mulU (unpackBits a.toBits) (unpackBits b.toBits) false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, le_of_loR h (mulDown_isRoundDownR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (mulU_NF_right _ _ hb))
  · rw [e] at h; exact absurd h (not_fv_of_NF (mulU_NF_left _ _ ha))

theorem mulUp_fin (h : Fv (mulUp a b) r) :
    ∃ x y, Fv a x ∧ Fv b y ∧ x * y ≤ r := by
  have e : mulUp a b = Float.ofBits (packDirected true
      (mulU (unpackBits a.toBits) (unpackBits b.toBits) true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · exact ⟨x, y, hx, hy, ge_of_hiR h (mulUp_isRoundUpR hx hy).1⟩
    · rw [e] at h; exact absurd h (not_fv_of_NF (mulU_NF_right _ _ hb))
  · rw [e] at h; exact absurd h (not_fv_of_NF (mulU_NF_left _ _ ha))

end

/-! ### Directed FMA (new spec) -/

theorem addZero_lo (t : Sign) {c : UInt64} {qc : ℚ} (hc : bitsToRat? c = some qc) :
    loEncloses? (bitsToEVal (packDirected false (addU (.zero t) (unpackBits c) false))) qc := by
  rcases bitsToRat?_cases hc with ⟨s3, hu3, rfl⟩ | ⟨s3, m3, e3, h3, hu3, rfl, hc3⟩
  · rw [hu3]; simp only [addU]
    split
    · exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses])
    · exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses])
  · rw [hu3, addU_zero_finite]
    exact loEncloses_packDirected_shaped s3 h3 (canonical_is_shaped hc3)

theorem addZero_hi (t : Sign) {c : UInt64} {qc : ℚ} (hc : bitsToRat? c = some qc) :
    hiEncloses? (bitsToEVal (packDirected true (addU (.zero t) (unpackBits c) true))) qc := by
  rcases bitsToRat?_cases hc with ⟨s3, hu3, rfl⟩ | ⟨s3, m3, e3, h3, hu3, rfl, hc3⟩
  · rw [hu3]; simp only [addU]
    split
    · exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses])
    · exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses])
  · rw [hu3, addU_zero_finite]
    exact hiEncloses_packDirected_shaped s3 h3 (canonical_is_shaped hc3)

theorem fma_encloses_lo {a b c : UInt64} {qa qb qc : ℚ} (ha : bitsToRat? a = some qa)
    (hb : bitsToRat? b = some qb) (hc : bitsToRat? c = some qc) :
    loEncloses? (bitsToEVal (Spec.fma a b c false)) (qa * qb + qc) := by
  unfold Spec.fma
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩ <;>
  rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩ <;>
  rw [hu1, hu2]
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.zero s1) (.zero s2) (unpackBits c) false =
      addU (.zero (s1 * s2)) (unpackBits c) false from rfl) ▸ addZero_lo (s1 * s2) hc
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.zero s1) (.finite s2 m2 e2 h2) (unpackBits c) false =
      addU (.zero (s1 * s2)) (unpackBits c) false from rfl) ▸ addZero_lo (s1 * s2) hc
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.finite s1 m1 e1 h1) (.zero s2) (unpackBits c) false =
      addU (.zero (s1 * s2)) (unpackBits c) false from rfl) ▸ addZero_lo (s1 * s2) hc
  · rcases bitsToRat?_cases hc with ⟨s3, hu3, rfl⟩ | ⟨s3, m3, e3, h3, hu3, rfl, hc3⟩
    · rw [hu3]
      have hm := mul_encloses_lo ha hb
      simp only [Spec.mulDown, Spec.mul, hu1, hu2] at hm
      exact (show fmaU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) (.zero s3) false =
        mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false from rfl) ▸ (by simpa using hm)
    · rw [hu3]
      have hred : fmaU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) (.finite s3 m3 e3 h3) false =
          addU (.finite (s1 * s2) (m1 * m2) (e1 + e2) (Nat.mul_pos h1 h2))
            (.finite s3 m3 e3 h3) false := rfl
      rw [hred]
      have hlo := addU_finite_lo (s₁ := s1 * s2) (s₂ := s3) (e₁ := e1 + e2) (e₂ := e3)
        (Nat.mul_pos h1 h2) h3
      rw [signedVal_mul] at hlo
      have hshape := normalizeDirected_zero_or_shaped
        ((s1 * s2).apply (decreaseExponent (m1 * m2) (e1 + e2) (min (e1 + e2) e3)).1 +
          s3.apply (decreaseExponent m3 e3 (min (e1 + e2) e3)).1)
        (min (e1 + e2) e3) (cancelZero false) false
      have hadd :
          addU (.finite (s1 * s2) (m1 * m2) (e1 + e2) (Nat.mul_pos h1 h2)) (.finite s3 m3 e3 h3)
              false =
            normalizeDirected
              ((s1 * s2).apply (decreaseExponent (m1 * m2) (e1 + e2) (min (e1 + e2) e3)).1 +
                s3.apply (decreaseExponent m3 e3 (min (e1 + e2) e3)).1)
              (min (e1 + e2) e3) (cancelZero false) false := rfl
      rw [hadd] at hlo ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨s, m, e, h, heq, hsh⟩
      · rw [heq]; exact loEncloses_packDirected_zero_val _ _ _ (heq ▸ hlo)
      · rw [heq]; exact loEncloses_packDirected_of_shaped s h hsh _ (heq ▸ hlo)

theorem fma_encloses_hi {a b c : UInt64} {qa qb qc : ℚ} (ha : bitsToRat? a = some qa)
    (hb : bitsToRat? b = some qb) (hc : bitsToRat? c = some qc) :
    hiEncloses? (bitsToEVal (Spec.fma a b c true)) (qa * qb + qc) := by
  unfold Spec.fma
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩ <;>
  rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩ <;>
  rw [hu1, hu2]
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.zero s1) (.zero s2) (unpackBits c) true =
      addU (.zero (s1 * s2)) (unpackBits c) true from rfl) ▸ addZero_hi (s1 * s2) hc
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.zero s1) (.finite s2 m2 e2 h2) (unpackBits c) true =
      addU (.zero (s1 * s2)) (unpackBits c) true from rfl) ▸ addZero_hi (s1 * s2) hc
  · simp only [zero_mul, mul_zero, zero_add] at *
    exact (show fmaU (.finite s1 m1 e1 h1) (.zero s2) (unpackBits c) true =
      addU (.zero (s1 * s2)) (unpackBits c) true from rfl) ▸ addZero_hi (s1 * s2) hc
  · rcases bitsToRat?_cases hc with ⟨s3, hu3, rfl⟩ | ⟨s3, m3, e3, h3, hu3, rfl, hc3⟩
    · rw [hu3]
      have hm := mul_encloses_hi ha hb
      simp only [Spec.mulUp, Spec.mul, hu1, hu2] at hm
      exact (show fmaU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) (.zero s3) true =
        mulU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true from rfl) ▸ (by simpa using hm)
    · rw [hu3]
      have hred : fmaU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) (.finite s3 m3 e3 h3) true =
          addU (.finite (s1 * s2) (m1 * m2) (e1 + e2) (Nat.mul_pos h1 h2))
            (.finite s3 m3 e3 h3) true := rfl
      rw [hred]
      have hhi := addU_finite_hi (s₁ := s1 * s2) (s₂ := s3) (e₁ := e1 + e2) (e₂ := e3)
        (Nat.mul_pos h1 h2) h3
      rw [signedVal_mul] at hhi
      have hshape := normalizeDirected_zero_or_shaped
        ((s1 * s2).apply (decreaseExponent (m1 * m2) (e1 + e2) (min (e1 + e2) e3)).1 +
          s3.apply (decreaseExponent m3 e3 (min (e1 + e2) e3)).1)
        (min (e1 + e2) e3) (cancelZero true) true
      have hadd :
          addU (.finite (s1 * s2) (m1 * m2) (e1 + e2) (Nat.mul_pos h1 h2)) (.finite s3 m3 e3 h3)
              true =
            normalizeDirected
              ((s1 * s2).apply (decreaseExponent (m1 * m2) (e1 + e2) (min (e1 + e2) e3)).1 +
                s3.apply (decreaseExponent m3 e3 (min (e1 + e2) e3)).1)
              (min (e1 + e2) e3) (cancelZero true) true := rfl
      rw [hadd] at hhi ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨s, m, e, h, heq, hsh⟩
      · rw [heq]; exact hiEncloses_packDirected_zero_val _ _ _ (heq ▸ hhi)
      · rw [heq]; exact hiEncloses_packDirected_of_shaped s h hsh _ (heq ▸ hhi)

section
variable {a b c : Float} {r : ℝ}

theorem fmaDown_fin (h : Fv (fmaDown a b c) r) :
    ∃ x y z, Fv a x ∧ Fv b y ∧ Fv c z ∧ r ≤ x * y + z := by
  have e : fmaDown a b c = Float.ofBits (packDirected false
      (fmaU (unpackBits a.toBits) (unpackBits b.toBits) (unpackBits c.toBits) false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · rcases fin_or_NF c with ⟨z, hz⟩ | hc
      · refine ⟨x, y, z, hx, hy, hz, ?_⟩
        obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 hx
        obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hy
        obtain ⟨qc, hc', rfl⟩ := toReal?_eq_some.1 hz
        have henc := fma_encloses_lo ha' hb' hc'
        obtain ⟨ev, hev⟩ := bitsToEVal_some_of_loEncloses henc
        have hl : loR (bitsToEVal (fmaDown a b c).toBits) ((qa * qb + qc : ℚ) : ℝ) := by
          rw [loR_cast]
          have : (fmaDown a b c).toBits = packBits (unpackBits (Spec.fma a.toBits b.toBits c.toBits false)) := by
            simp only [Directed.fmaDown, fmaDownSpec, Spec.fmaDown, toBits_ofBits]
          rw [this, bitsToEVal_pack_unpack_of_some hev, ← hev]; exact henc
        have := le_of_loR h hl
        push_cast at this; exact this
      · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inr (Or.inr hc))))
    · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inr (Or.inl hb))))
  · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inl ha)))

theorem fmaUp_fin (h : Fv (fmaUp a b c) r) :
    ∃ x y z, Fv a x ∧ Fv b y ∧ Fv c z ∧ x * y + z ≤ r := by
  have e : fmaUp a b c = Float.ofBits (packDirected true
      (fmaU (unpackBits a.toBits) (unpackBits b.toBits) (unpackBits c.toBits) true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · rcases fin_or_NF b with ⟨y, hy⟩ | hb
    · rcases fin_or_NF c with ⟨z, hz⟩ | hc
      · refine ⟨x, y, z, hx, hy, hz, ?_⟩
        obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 hx
        obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hy
        obtain ⟨qc, hc', rfl⟩ := toReal?_eq_some.1 hz
        have henc := fma_encloses_hi ha' hb' hc'
        obtain ⟨ev, hev⟩ := bitsToEVal_some_of_hiEncloses henc
        have hl : hiR (bitsToEVal (fmaUp a b c).toBits) ((qa * qb + qc : ℚ) : ℝ) := by
          rw [hiR_cast]
          have : (fmaUp a b c).toBits = packBits (unpackBits (Spec.fma a.toBits b.toBits c.toBits true)) := by
            simp only [Directed.fmaUp, fmaUpSpec, Spec.fmaUp, toBits_ofBits]
          rw [this, bitsToEVal_pack_unpack_of_some hev, ← hev]; exact henc
        have := ge_of_hiR h hl
        push_cast at this; exact this
      · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inr (Or.inr hc))))
    · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inr (Or.inl hb))))
  · rw [e] at h; exact absurd h (not_fv_of_NF (fmaU_NF _ _ _ _ (Or.inl ha)))

end

/-! ### Division and square root -/

theorem unpack_finite_of_fv_ne_zero {b : Float} {y : ℝ} (hb : Fv b y) (hy : y ≠ 0) :
    ∃ s m e hm, unpackBits b.toBits = .finite s m e hm := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hb
  rcases bitsToRat?_cases hq with ⟨s, hu, rfl⟩ | ⟨s, m, e, hm, hu, -, -⟩
  · simp at hy
  · exact ⟨s, m, e, hm, hu⟩

section
variable {a b : Float} {r y : ℝ}

theorem divDown_fin (h : Fv (divDown a b) r) (hb : Fv b y) (hy : y ≠ 0) :
    ∃ x, Fv a x ∧ r ≤ x / y := by
  have e : divDown a b = Float.ofBits (packDirected false
      (divU (unpackBits a.toBits) (unpackBits b.toBits) false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · exact ⟨x, hx, le_of_loR h (divDown_isRoundDownR hx hb hy).1⟩
  · obtain ⟨s, m, ee, hm, hu⟩ := unpack_finite_of_fv_ne_zero hb hy
    rw [e, hu] at h; exact absurd h (not_fv_of_NF (divU_NF_left _ ha))

theorem divUp_fin (h : Fv (divUp a b) r) (hb : Fv b y) (hy : y ≠ 0) :
    ∃ x, Fv a x ∧ x / y ≤ r := by
  have e : divUp a b = Float.ofBits (packDirected true
      (divU (unpackBits a.toBits) (unpackBits b.toBits) true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · exact ⟨x, hx, ge_of_hiR h (divUp_isRoundUpR hx hb hy).1⟩
  · obtain ⟨s, m, ee, hm, hu⟩ := unpack_finite_of_fv_ne_zero hb hy
    rw [e, hu] at h; exact absurd h (not_fv_of_NF (divU_NF_left _ ha))

theorem nonneg_of_sqrt_fin {a : Float} {x : ℝ} (up : Bool) (hx : Fv a x)
    (h : ∃ r, Fv (Float.ofBits (packDirected up (sqrtU (unpackBits a.toBits) up))) r) : 0 ≤ x := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hx
  rcases bitsToRat?_cases hq with ⟨s, hu, rfl⟩ | ⟨s, m, e, hm, hu, rfl, -⟩
  · simp
  · cases s with
    | positive =>
      have := zero_le_signedVal_pos (m := m) (e := e)
      exact_mod_cast this
    | negative =>
      obtain ⟨r, hr⟩ := h
      rw [hu] at hr
      exact absurd hr (not_fv_of_NF (Or.inl rfl))

theorem sqrtDown_fin (h : Fv (sqrtDown a) r) : ∃ x, Fv a x ∧ 0 ≤ x ∧ r ≤ Real.sqrt x := by
  have e : sqrtDown a = Float.ofBits (packDirected false (sqrtU (unpackBits a.toBits) false)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · have hx0 := nonneg_of_sqrt_fin false hx ⟨r, e ▸ h⟩
    exact ⟨x, hx, hx0, le_of_loR h (sqrtDown_isRoundDownR hx hx0).1⟩
  · rw [e] at h; exact absurd h (not_fv_of_NF (sqrtU_NF _ ha))

theorem sqrtUp_fin (h : Fv (sqrtUp a) r) : ∃ x, Fv a x ∧ 0 ≤ x ∧ Real.sqrt x ≤ r := by
  have e : sqrtUp a = Float.ofBits (packDirected true (sqrtU (unpackBits a.toBits) true)) := rfl
  rcases fin_or_NF a with ⟨x, hx⟩ | ha
  · have hx0 := nonneg_of_sqrt_fin true hx ⟨r, e ▸ h⟩
    exact ⟨x, hx, hx0, ge_of_hiR h (sqrtUp_isRoundUpR hx hx0).1⟩
  · rw [e] at h; exact absurd h (not_fv_of_NF (sqrtU_NF _ ha))

end

/-! ### Negation and comparisons -/

theorem isNaN_of_fv {f : Float} {x : ℝ} (h : Fv f x) : f.isNaN = false := by
  obtain ⟨q, hq, -⟩ := toReal?_eq_some.1 h
  exact isNaN_false_of_bitsToRat? hq

theorem toE_of_fv {f : Float} {x : ℝ} (h : Fv f x) : f.toE = (x : EReal) := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 h
  exact toE_of_bitsToRat? hq

theorem fv_of_toE {f : Float} {x : ℝ} (hn : f.isNaN = false) (h : f.toE = (x : EReal)) :
    Fv f x := by
  obtain ⟨q, hq, hqe⟩ := exists_rat_of_toE hn (by rw [h]; exact EReal.coe_ne_bot x)
    (by rw [h]; exact EReal.coe_ne_top x)
  rw [h] at hqe
  have : x = q := by exact_mod_cast hqe
  subst this; exact toReal?_of_bitsToRat? hq

theorem isNaN_of_neg {f : Float} (h : (-f).isNaN = false) : f.isNaN = false := by
  cases hn : f.isNaN
  · rfl
  · exfalso
    have hb : (-f).toBits = packBits (unpackBits f.toBits).neg := rfl
    have hnan : unpackBits f.toBits = .notANumber := by
      rw [float_isNaN] at hn
      cases hu : unpackBits f.toBits <;> simp_all [UnpackedFloat.isNaN]
    rw [float_isNaN, hb, hnan] at h
    rw [show (UnpackedFloat.notANumber).neg = .notANumber from rfl, unpackBits_nan] at h
    simp [UnpackedFloat.isNaN] at h

theorem fv_neg_iff {f : Float} {y : ℝ} : Fv (-f) y ↔ Fv f (-y) := by
  constructor
  · intro h
    have hn := isNaN_of_neg (isNaN_of_fv h)
    refine fv_of_toE hn ?_
    have := toE_of_fv h
    rw [toE_neg hn] at this
    rw [EReal.coe_neg, ← this, neg_neg]
  · intro h
    have hn := isNaN_of_fv h
    refine fv_of_toE (isNaN_neg hn) ?_
    rw [toE_neg hn, toE_of_fv h, EReal.coe_neg, neg_neg]

theorem fv_neg {f : Float} {x : ℝ} (h : Fv f x) : Fv (-f) (-x) := fv_neg_iff.2 (by simpa using h)

theorem fv_of_neg {f : Float} {y : ℝ} (h : Fv (-f) y) : Fv f (-y) := fv_neg_iff.1 h

theorem le_iff_fv {a b : Float} {x y : ℝ} (ha : Fv a x) (hb : Fv b y) :
    decide (a ≤ b) = true ↔ x ≤ y := by
  rw [decide_eq_true_iff, float_le_iff_toE (isNaN_of_fv ha) (isNaN_of_fv hb), toE_of_fv ha,
    toE_of_fv hb, EReal.coe_le_coe_iff]

theorem lt_iff_fv {a b : Float} {x y : ℝ} (ha : Fv a x) (hb : Fv b y) :
    decide (a < b) = true ↔ x < y := by
  rw [decide_eq_true_iff, float_lt_iff_toE (isNaN_of_fv ha) (isNaN_of_fv hb), toE_of_fv ha,
    toE_of_fv hb, EReal.coe_lt_coe_iff]

theorem fv_zero : Fv (0 : Float) 0 := by
  have := toReal?_of_bitsToRat? Interval64Proofs.Div.bitsToRat?_float_zero
  simpa using this

theorem isNaN_of_lt_left {a b : Float} (h : decide (a < b) = true) : a.isNaN = false := by
  rw [decide_eq_true_iff, Interval64Proofs.IntervalMem.float_lt_iff] at h
  cases hn : a.isNaN
  · rfl
  · rw [float_isNaN] at hn
    cases hu : unpackBits a.toBits <;> simp_all [UnpackedFloat.isNaN, UnpackedFloat.lt,
      UnpackedFloat.compare]

theorem isNaN_of_lt_right {a b : Float} (h : decide (a < b) = true) : b.isNaN = false := by
  rw [decide_eq_true_iff, Interval64Proofs.IntervalMem.float_lt_iff] at h
  cases hn : b.isNaN
  · rfl
  · rw [float_isNaN] at hn
    cases hu : unpackBits b.toBits <;> cases hv : unpackBits a.toBits <;>
      simp_all [UnpackedFloat.isNaN, UnpackedFloat.lt, UnpackedFloat.compare]

/-- `0 < d < ∞` gives a finite positive value. -/
theorem fv_of_pos_lt_inf {d : Float} (h0 : decide ((0 : Float) < d) = true)
    (h1 : decide (d < Float.inf) = true) : ∃ D, Fv d D ∧ 0 < D := by
  have hn := isNaN_of_lt_right h0
  have h0' := (float_lt_iff_toE (isNaN_of_fv fv_zero) hn).1 (of_decide_eq_true h0)
  have h1' := (float_lt_iff_toE hn isNaN_inf).1 (of_decide_eq_true h1)
  rw [toE_of_fv fv_zero] at h0'
  rw [toE_inf] at h1'
  obtain ⟨q, hq, hqe⟩ := exists_rat_of_toE hn (ne_bot_of_gt h0') (ne_top_of_lt h1')
  refine ⟨q, toReal?_of_bitsToRat? hq, ?_⟩
  rw [hqe] at h0'; exact_mod_cast h0'

theorem isFinite_fv {f : Float} (h : f.isFinite = true) : ∃ x, Fv f x := by
  rcases fin_or_NF f with hx | hnf
  · exact hx
  · exfalso
    have : f.isFinite = (unpackBits f.toBits).isFinite := rfl
    rcases hnf with hu | ⟨s, hu⟩ <;> rw [this, hu] at h <;> simp [UnpackedFloat.isFinite] at h

end RealFP.I128
