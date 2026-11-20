/-
Tightness of the scalar directed operations: `addDown a b` is the greatest
representable `≤ qa + qb` (or `−∞`), `addUp a b` the least representable
`≥ qa + qb` (or `+∞`), and likewise for `sub`, `mul`, `div` (nonzero
divisor). Hence each equals `ofRatDown` / `ofRatUp` of the exact result at
the value level (`bitsToEVal`; the two zeros have the same value).
-/
import Interval64Proofs.OfRat
import Interval64Proofs.Sub

namespace Interval64Proofs.Tight

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.RoundDirected
open Interval64Proofs.RoundInexact
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.Add
open Interval64Proofs.Mul
open Interval64Proofs.Div
open Interval64Proofs.ExactAdd
open Interval64Proofs.Sub
open Interval64Proofs.Grid
open Interval64Proofs.RoundOpt
open Interval64Proofs.OfRat
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Generic helpers -/

theorem isRoundDown_pack_exact (u : UnpackedFloat) (x : Rat) (hsh : Shaped u)
    (hv : toEVal u = some (.rat x)) : IsRoundDown x (bitsToEVal (packDirected false u)) :=
  isRoundDown_pack u x hsh (by rw [hv]; exact Rat.le_refl) (fun _ _ h => by rw [hv]; exact h)

theorem isRoundUp_pack_exact (u : UnpackedFloat) (x : Rat) (hsh : Shaped u)
    (hv : toEVal u = some (.rat x)) : IsRoundUp x (bitsToEVal (packDirected true u)) :=
  isRoundUp_pack u x hsh (by rw [hv]; exact Rat.le_refl) (fun _ _ h => by rw [hv]; exact h)

theorem shaped_zero (z : Sign) : Shaped (.zero z) := Or.inl ⟨z, rfl⟩

theorem shaped_canonical (s : Sign) {m : Nat} {e : Int} (h : 0 < m)
    (hc : IsCanonicalFinite m e) : Shaped (.finite s m e h) :=
  Or.inr ⟨s, m, e, h, rfl, canonical_is_shaped hc⟩

theorem isRoundDown_zero (up : Bool) (z : Sign) :
    IsRoundDown 0 (bitsToEVal (packDirected up (.zero z))) := by
  rw [packDirected_zero, bitsToEVal_pack_zero]
  exact isRoundDown_self 0

theorem isRoundUp_zero (up : Bool) (z : Sign) :
    IsRoundUp 0 (bitsToEVal (packDirected up (.zero z))) := by
  rw [packDirected_zero, bitsToEVal_pack_zero]
  exact isRoundUp_self 0

/-! ### `normalizeDirected` (exact integer mantissa) -/

theorem normalizeDirected_isRoundDown (mant : Int) (e : Int) (z : Sign) :
    IsRoundDown ((mant : Rat) * pow2 e)
      (bitsToEVal (packDirected false (normalizeDirected mant e z false))) := by
  unfold normalizeDirected
  cases hc : compare mant 0 with
  | lt =>
    have hlt : mant < 0 := (Int.compare_eq_lt).mp hc
    have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .negative (-mant).toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat, Rat.intCast_neg, ← Rat.neg_mul, Rat.neg_neg]
    rw [← hv]
    exact roundDirected_isRoundDown .negative _ e .exact _ (fun _ => rfl)
      (fun _ h => by cases h) (Or.inl rfl)
  | eq =>
    have heq : mant = 0 := (Int.compare_eq_eq).mp hc
    have : (mant : Rat) * pow2 e = 0 := by rw [heq]; simp
    rw [this]
    exact isRoundDown_zero false z
  | gt =>
    have hgt : 0 < mant := (Int.compare_eq_gt).mp hc
    have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .positive mant.toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat]
    rw [← hv]
    exact roundDirected_isRoundDown .positive _ e .exact _ (fun _ => rfl)
      (fun _ h => by cases h) (Or.inl rfl)

theorem normalizeDirected_isRoundUp (mant : Int) (e : Int) (z : Sign) :
    IsRoundUp ((mant : Rat) * pow2 e)
      (bitsToEVal (packDirected true (normalizeDirected mant e z true))) := by
  unfold normalizeDirected
  cases hc : compare mant 0 with
  | lt =>
    have hlt : mant < 0 := (Int.compare_eq_lt).mp hc
    have hnat : ((-mant).toNat : Int) = -mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .negative (-mant).toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat, Rat.intCast_neg, ← Rat.neg_mul, Rat.neg_neg]
    rw [← hv]
    exact roundDirected_isRoundUp .negative _ e .exact _ (fun _ => rfl)
      (fun _ h => by cases h) (Or.inl rfl)
  | eq =>
    have heq : mant = 0 := (Int.compare_eq_eq).mp hc
    have : (mant : Rat) * pow2 e = 0 := by rw [heq]; simp
    rw [this]
    exact isRoundUp_zero true z
  | gt =>
    have hgt : 0 < mant := (Int.compare_eq_gt).mp hc
    have hnat : (mant.toNat : Int) = mant := Int.toNat_of_nonneg (by omega)
    have hv : signedVal .positive mant.toNat e = (mant : Rat) * pow2 e := by
      simp only [signedVal, mag]
      rw [← Rat.intCast_natCast, hnat]
    rw [← hv]
    exact roundDirected_isRoundUp .positive _ e .exact _ (fun _ => rfl)
      (fun _ h => by cases h) (Or.inl rfl)

/-! ### Addition -/

/-- **Tight add (down).** `addDown a b` is the greatest representable `≤ qa + qb`. -/
theorem add_isRoundDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundDown (qa + qb) (bitsToEVal (addDown a b)) := by
  simp only [addDown, Interval64.Spec.add]
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, Rat.add_zero]
      simp only [addU]
      split
      · exact isRoundDown_zero _ _
      · exact isRoundDown_zero _ _
    · rw [hu1, hu2, addU_zero_finite, Rat.zero_add]
      exact isRoundDown_pack_exact _ _ (shaped_canonical s2 h2 hc2) rfl
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, addU_finite_zero, Rat.add_zero]
      exact isRoundDown_pack_exact _ _ (shaped_canonical s1 h1 hc1) rfl
    · rw [hu1, hu2, ← aligned_sum_eq s1 s2 m1 m2 e1 e2]
      exact normalizeDirected_isRoundDown _ _ _

/-- **Tight add (up).** -/
theorem add_isRoundUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundUp (qa + qb) (bitsToEVal (addUp a b)) := by
  simp only [addUp, Interval64.Spec.add]
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, Rat.add_zero]
      simp only [addU]
      split
      · exact isRoundUp_zero _ _
      · exact isRoundUp_zero _ _
    · rw [hu1, hu2, addU_zero_finite, Rat.zero_add]
      exact isRoundUp_pack_exact _ _ (shaped_canonical s2 h2 hc2) rfl
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, addU_finite_zero, Rat.add_zero]
      exact isRoundUp_pack_exact _ _ (shaped_canonical s1 h1 hc1) rfl
    · rw [hu1, hu2, ← aligned_sum_eq s1 s2 m1 m2 e1 e2]
      exact normalizeDirected_isRoundUp _ _ _

/-! ### Subtraction -/

theorem sub_isRoundDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundDown (qa - qb) (bitsToEVal (subDown a b)) := by
  rw [subDown_eq_addDown_neg (bitsToEVal_rat_of_bitsToRat? hb), Rat.sub_eq_add_neg]
  exact add_isRoundDown ha (bitsToRat?_negBits hb)

theorem sub_isRoundUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundUp (qa - qb) (bitsToEVal (subUp a b)) := by
  rw [subUp_eq_addUp_neg (bitsToEVal_rat_of_bitsToRat? hb), Rat.sub_eq_add_neg]
  exact add_isRoundUp ha (bitsToRat?_negBits hb)

/-! ### Multiplication -/

theorem mul_isRoundDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundDown (qa * qb) (bitsToEVal (mulDown a b)) := by
  simp only [mulDown, Interval64.Spec.mul]
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rw [Rat.zero_mul]
    rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2]; exact isRoundDown_zero _ _
    · rw [hu1, hu2]; exact isRoundDown_zero _ _
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, Rat.mul_zero]; exact isRoundDown_zero _ _
    · rw [hu1, hu2, ← signedVal_mul]
      exact roundDirected_isRoundDown _ _ _ .exact _ (fun _ => rfl)
        (fun _ h => by cases h) (Or.inl rfl)

theorem mul_isRoundUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    IsRoundUp (qa * qb) (bitsToEVal (mulUp a b)) := by
  simp only [mulUp, Interval64.Spec.mul]
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rw [Rat.zero_mul]
    rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2]; exact isRoundUp_zero _ _
    · rw [hu1, hu2]; exact isRoundUp_zero _ _
  · rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
    · rw [hu1, hu2, Rat.mul_zero]; exact isRoundUp_zero _ _
    · rw [hu1, hu2, ← signedVal_mul]
      exact roundDirected_isRoundUp _ _ _ .exact _ (fun _ => rfl)
        (fun _ h => by cases h) (Or.inl rfl)

/-! ### Division (nonzero divisor) -/

theorem div_hyps (s₁ s₂ : Sign) {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hc₁ : IsCanonicalFinite m₁ e₁) :
    let d := divCore spec64 m₁ e₁ m₂ e₂
    (d.2.2 = .exact → signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂ = signedVal (s₁ / s₂) d.1 d.2.1) ∧
    (∀ o, d.2.2 = .inexact o →
      inexactMag d.1 d.2.1 (signedMag (s₁ / s₂) (signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂))) ∧
    (d.2.2 = .exact ∨ d.2.1 ≤ spec64.minExponent ∨ 2 ^ 52 ≤ d.1) := by
  intro d
  have hbr := mag_div_bracket m₁ e₁ m₂ e₂ h₂
  have hv : signedVal s₁ m₁ e₁ / signedVal s₂ m₂ e₂ =
      signedOf (s₁ / s₂) (mag m₁ e₁ / mag m₂ e₂) :=
    signedVal_div s₁ s₂ m₁ m₂ e₁ e₂ h₂
  refine ⟨fun hex => ?_, fun o ho => ?_,
    Or.inr (divCore_enough_bits h₁ (ExactAdd.canonical_mantissa_lt hc₁) h₂)⟩
  · rw [hv, hbr.1 hex, signedVal_signedOf]
  · rw [hv, signedMag_signedOf (s := s₁ / s₂) (mag_div_nonneg m₁ e₁ m₂ e₂ h₂)]
    exact hbr.2 o ho

theorem div_isRoundDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) (hqb : qb ≠ 0) :
    IsRoundDown (qa / qb) (bitsToEVal (divDown a b)) := by
  simp only [divDown, Interval64.Spec.div]
  rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
  · exact (hqb rfl).elim
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rw [hu1, hu2]
    have : (0 : Rat) / signedVal s2 m2 e2 = 0 := by rw [Rat.div_def, Rat.zero_mul]
    rw [this]
    exact isRoundDown_zero _ _
  · rw [hu1, hu2]
    have ⟨hex, hin, hen⟩ := div_hyps s1 s2 h1 h2 hc1 (e₂ := e2)
    exact roundDirected_isRoundDown _ _ _ _ _ hex hin hen

theorem div_isRoundUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) (hqb : qb ≠ 0) :
    IsRoundUp (qa / qb) (bitsToEVal (divUp a b)) := by
  simp only [divUp, Interval64.Spec.div]
  rcases bitsToRat?_cases hb with ⟨s2, hu2, rfl⟩ | ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
  · exact (hqb rfl).elim
  rcases bitsToRat?_cases ha with ⟨s1, hu1, rfl⟩ | ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
  · rw [hu1, hu2]
    have : (0 : Rat) / signedVal s2 m2 e2 = 0 := by rw [Rat.div_def, Rat.zero_mul]
    rw [this]
    exact isRoundUp_zero _ _
  · rw [hu1, hu2]
    have ⟨hex, hin, hen⟩ := div_hyps s1 s2 h1 h2 hc1 (e₂ := e2)
    exact roundDirected_isRoundUp _ _ _ _ _ hex hin hen

/-! ### Corollaries: no representable value strictly inside the rounding gap -/

theorem IsRoundDown.no_between {x d v : Rat} (h : IsRoundDown x (some (.rat d)))
    (hv : Representable v) (hdv : d < v) : x < v :=
  Rat.not_le.mp (fun hle => (Rat.not_le.mpr hdv) (h.2 v hv hle))

theorem IsRoundUp.no_between {x u v : Rat} (h : IsRoundUp x (some (.rat u)))
    (hv : Representable v) (hvu : v < u) : v < x :=
  Rat.not_le.mp (fun hle => (Rat.not_le.mpr hvu) (h.2 v hv hle))

/-- Gap statement for a pair of directed results `lo`, `hi` of an exact value `x`:
    no representable `v` with `lo < v ≤ x` or `x ≤ v < hi`. -/
def Tight (x : Rat) (lo hi : UInt64) : Prop :=
  (∀ d v, bitsToRat? lo = some d → Representable v → d < v → x < v) ∧
  (∀ u v, bitsToRat? hi = some u → Representable v → v < u → v < x)

theorem tight_of {x : Rat} {lo hi : UInt64} (hlo : IsRoundDown x (bitsToEVal lo))
    (hhi : IsRoundUp x (bitsToEVal hi)) : Tight x lo hi := by
  refine ⟨fun d v hd hv hdv => ?_, fun u v hu hv hvu => ?_⟩
  · rw [bitsToEVal_rat_of_bitsToRat? hd] at hlo
    exact IsRoundDown.no_between hlo hv hdv
  · rw [bitsToEVal_rat_of_bitsToRat? hu] at hhi
    exact IsRoundUp.no_between hhi hv hvu

theorem add_tight {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    Tight (qa + qb) (addDown a b) (addUp a b) :=
  tight_of (add_isRoundDown ha hb) (add_isRoundUp ha hb)

theorem sub_tight {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    Tight (qa - qb) (subDown a b) (subUp a b) :=
  tight_of (sub_isRoundDown ha hb) (sub_isRoundUp ha hb)

theorem mul_tight {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    Tight (qa * qb) (mulDown a b) (mulUp a b) :=
  tight_of (mul_isRoundDown ha hb) (mul_isRoundUp ha hb)

theorem div_tight {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) (hqb : qb ≠ 0) :
    Tight (qa / qb) (divDown a b) (divUp a b) :=
  tight_of (div_isRoundDown ha hb hqb) (div_isRoundUp ha hb hqb)

/-! ### Directed operations agree with `ofRatDown` / `ofRatUp` of the exact result -/

theorem addDown_eq_ofRatDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (addDown a b) = bitsToEVal (ofRatDown (qa + qb)) :=
  isRoundDown_unique (add_isRoundDown ha hb) (ofRatDown_isRoundDown _)

theorem addUp_eq_ofRatUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (addUp a b) = bitsToEVal (ofRatUp (qa + qb)) :=
  isRoundUp_unique (add_isRoundUp ha hb) (ofRatUp_isRoundUp _)

theorem subDown_eq_ofRatDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (subDown a b) = bitsToEVal (ofRatDown (qa - qb)) :=
  isRoundDown_unique (sub_isRoundDown ha hb) (ofRatDown_isRoundDown _)

theorem subUp_eq_ofRatUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (subUp a b) = bitsToEVal (ofRatUp (qa - qb)) :=
  isRoundUp_unique (sub_isRoundUp ha hb) (ofRatUp_isRoundUp _)

theorem mulDown_eq_ofRatDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (mulDown a b) = bitsToEVal (ofRatDown (qa * qb)) :=
  isRoundDown_unique (mul_isRoundDown ha hb) (ofRatDown_isRoundDown _)

theorem mulUp_eq_ofRatUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    bitsToEVal (mulUp a b) = bitsToEVal (ofRatUp (qa * qb)) :=
  isRoundUp_unique (mul_isRoundUp ha hb) (ofRatUp_isRoundUp _)

theorem divDown_eq_ofRatDown {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) (hqb : qb ≠ 0) :
    bitsToEVal (divDown a b) = bitsToEVal (ofRatDown (qa / qb)) :=
  isRoundDown_unique (div_isRoundDown ha hb hqb) (ofRatDown_isRoundDown _)

theorem divUp_eq_ofRatUp {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) (hqb : qb ≠ 0) :
    bitsToEVal (divUp a b) = bitsToEVal (ofRatUp (qa / qb)) :=
  isRoundUp_unique (div_isRoundUp ha hb hqb) (ofRatUp_isRoundUp _)

end Interval64Proofs.Tight
