/-
Directed rounding, tightness and interval optimality over `ℝ`.

* Pointwise: for finite doubles `a`, `b` with real values `x`, `y`,
  `addDown a b` is the greatest representable real `≤ x + y` and `addUp a b`
  the least `≥ x + y` (`IsRoundDownR` / `IsRoundUpR`), likewise for
  `- * /` (`y ≠ 0`) and `Real.sqrt` (`0 ≤ x`). So no representable real lies
  strictly between a computed bound and the exact result.
* Interval level: for finite-endpoint `X`, `Y`, the endpoints of `X ∘ Y` are
  the best representable bounds of the real range `{x ∘ y | x ∈ X, y ∈ Y}`
  (`*_iv_optimalR`; `div` needs `containsZero Y = false`).
* `ofRatDown` / `ofRatUp` round rationals correctly as reals.
-/
import RealFPMathlib.Mem

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Grid Interval64Proofs.OfRat
open Interval64Proofs.TightIv Interval64Proofs.TightSqrt

namespace RealFP

/-! ### Pointwise directed rounding (Float level) -/

section pointwise
variable {a b : Float} {x y : ℝ}

theorem addDown_isRoundDownR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundDownR (x + y) (bitsToEVal (Directed.addDown a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_add, isRoundDownR_cast_iff]; exact addDown_float_tight ha' hb'

theorem addUp_isRoundUpR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundUpR (x + y) (bitsToEVal (Directed.addUp a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_add, isRoundUpR_cast_iff]; exact addUp_float_tight ha' hb'

theorem subDown_isRoundDownR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundDownR (x - y) (bitsToEVal (Directed.subDown a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_sub, isRoundDownR_cast_iff]; exact subDown_float_tight ha' hb'

theorem subUp_isRoundUpR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundUpR (x - y) (bitsToEVal (Directed.subUp a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_sub, isRoundUpR_cast_iff]; exact subUp_float_tight ha' hb'

theorem mulDown_isRoundDownR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundDownR (x * y) (bitsToEVal (Directed.mulDown a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_mul, isRoundDownR_cast_iff]; exact mulDown_float_tight ha' hb'

theorem mulUp_isRoundUpR (ha : a.toReal? = some x) (hb : b.toReal? = some y) :
    IsRoundUpR (x * y) (bitsToEVal (Directed.mulUp a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_mul, isRoundUpR_cast_iff]; exact mulUp_float_tight ha' hb'

theorem divDown_isRoundDownR (ha : a.toReal? = some x) (hb : b.toReal? = some y) (hy : y ≠ 0) :
    IsRoundDownR (x / y) (bitsToEVal (Directed.divDown a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_div, isRoundDownR_cast_iff]
  exact divDown_float_tight ha' hb' (by exact_mod_cast hy)

theorem divUp_isRoundUpR (ha : a.toReal? = some x) (hb : b.toReal? = some y) (hy : y ≠ 0) :
    IsRoundUpR (x / y) (bitsToEVal (Directed.divUp a b).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  obtain ⟨qb, hb', rfl⟩ := toReal?_eq_some.1 hb
  rw [← Rat.cast_div, isRoundUpR_cast_iff]
  exact divUp_float_tight ha' hb' (by exact_mod_cast hy)

end pointwise

/-! ### Square root -/

theorem isRoundDownR_sqrt_of_isSqrtDown {qa : ℚ} {r : Option EVal} (h : IsSqrtDown qa r) :
    IsRoundDownR (Real.sqrt qa) r := by
  obtain ⟨ρ, rfl, hρ0, hρsq, hopt⟩ := h
  have hρ0' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ0
  refine ⟨?_, ?_⟩
  · show (ρ : ℝ) ≤ Real.sqrt qa
    calc (ρ : ℝ) = Real.sqrt ((ρ : ℝ) * ρ) := (Real.sqrt_mul_self hρ0').symm
      _ ≤ Real.sqrt qa := Real.sqrt_le_sqrt (by exact_mod_cast hρsq)
  · rintro v ⟨w, hw, rfl⟩ hle
    show (w : ℝ) ≤ ρ
    rcases le_or_gt 0 w with hw0 | hw0
    · have hw0' : (0 : ℝ) ≤ w := by exact_mod_cast hw0
      by_cases hq0 : (0 : ℝ) ≤ qa
      · have hsq : (w : ℝ) * w ≤ qa := by
          calc (w : ℝ) * w ≤ Real.sqrt qa * Real.sqrt qa := mul_self_le_mul_self hw0' hle
            _ = qa := Real.mul_self_sqrt hq0
        exact_mod_cast hopt w hw hw0 (by exact_mod_cast hsq)
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.1 hq0))] at hle
        exact le_trans hle hρ0'
    · exact le_trans (by exact_mod_cast hw0.le) hρ0'

theorem isRoundUpR_sqrt_of_isSqrtUp {qa : ℚ} {r : Option EVal} (h : IsSqrtUp qa r) :
    IsRoundUpR (Real.sqrt qa) r := by
  obtain ⟨σ, rfl, hσ0, hσsq, hopt⟩ := h
  have hσ0' : (0 : ℝ) ≤ σ := by exact_mod_cast hσ0
  refine ⟨?_, ?_⟩
  · show Real.sqrt qa ≤ σ
    calc Real.sqrt qa ≤ Real.sqrt ((σ : ℝ) * σ) := Real.sqrt_le_sqrt (by exact_mod_cast hσsq)
      _ = σ := Real.sqrt_mul_self hσ0'
  · rintro v ⟨w, hw, rfl⟩ hle
    show (σ : ℝ) ≤ w
    have hw0' : (0 : ℝ) ≤ w := le_trans (Real.sqrt_nonneg _) hle
    have hw0 : (0 : ℚ) ≤ w := by exact_mod_cast hw0'
    have hsq : (qa : ℝ) ≤ w * w := by
      calc (qa : ℝ) ≤ Real.sqrt qa * Real.sqrt qa := by
            rcases le_total 0 (qa : ℝ) with h0 | h0
            · rw [Real.mul_self_sqrt h0]
            · exact le_trans h0 (mul_self_nonneg _)
        _ ≤ w * w := mul_self_le_mul_self (Real.sqrt_nonneg _) hle
    exact_mod_cast hopt w hw hw0 (by exact_mod_cast hsq)

theorem sqrtDown_isRoundDownR {a : Float} {x : ℝ} (ha : a.toReal? = some x) (hx : 0 ≤ x) :
    IsRoundDownR (Real.sqrt x) (bitsToEVal (Directed.sqrtDown a).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  exact isRoundDownR_sqrt_of_isSqrtDown (sqrtDown_float_tight ha' (by exact_mod_cast hx))

theorem sqrtUp_isRoundUpR {a : Float} {x : ℝ} (ha : a.toReal? = some x) (hx : 0 ≤ x) :
    IsRoundUpR (Real.sqrt x) (bitsToEVal (Directed.sqrtUp a).toBits) := by
  obtain ⟨qa, ha', rfl⟩ := toReal?_eq_some.1 ha
  exact isRoundUpR_sqrt_of_isSqrtUp (sqrtUp_float_tight ha' (by exact_mod_cast hx))

/-! ### Rationals -/

theorem ofRatDown_isRoundDownR (q : ℚ) : IsRoundDownR (q : ℝ) (bitsToEVal (ofRatDown q)) :=
  (isRoundDownR_cast_iff _ _).2 (ofRatDown_isRoundDown q)

theorem ofRatUp_isRoundUpR (q : ℚ) : IsRoundUpR (q : ℝ) (bitsToEVal (ofRatUp q)) :=
  (isRoundUpR_cast_iff _ _).2 (ofRatUp_isRoundUp q)

theorem isRepresentable_iff_representableR (q : ℚ) :
    isRepresentable q = true ↔ RepresentableR (q : ℝ) := by
  rw [representableR_cast, isRepresentable_iff]

theorem mem_toSet_ofRat (q : ℚ) : (q : ℝ) ∈ (ofRat q).toSet :=
  cast_mem_toSet_iff.2 (memIv_ofRat q)

theorem mem_toSet_ofRatInterval {lo hi : ℚ} {x : ℝ} (h₁ : (lo : ℝ) ≤ x) (h₂ : x ≤ (hi : ℝ)) :
    x ∈ (ofRatInterval lo hi).toSet := by
  have hlh : lo ≤ hi := by exact_mod_cast le_trans h₁ h₂
  exact mem_toSet_of_rat_bounds (memIv_ofRatInterval (le_refl lo) hlh)
    (memIv_ofRatInterval hlh (le_refl hi)) h₁ h₂

/-- `Set.Icc lo hi ⊆ (ofRatInterval lo hi).toSet`. -/
theorem Icc_subset_toSet_ofRatInterval (lo hi : ℚ) :
    Set.Icc (lo : ℝ) (hi : ℝ) ⊆ (ofRatInterval lo hi).toSet :=
  fun _ hx => mem_toSet_ofRatInterval hx.1 hx.2

/-! ### Interval-level tightness and optimality -/

section iv
variable {X Y : Interval64} {l₁ h₁ l₂ h₂ : ℚ}

theorem add_iv_tightR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    IsRoundDownR ((l₁ : ℝ) + l₂) (bitsToEVal (X + Y).lo.toBits) ∧
      IsRoundUpR ((h₁ : ℝ) + h₂) (bitsToEVal (X + Y).hi.toBits) := by
  rw [← Rat.cast_add, ← Rat.cast_add, isRoundDownR_cast_iff, isRoundUpR_cast_iff]
  exact add_iv_tight hX hY

theorem sub_iv_tightR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    IsRoundDownR ((l₁ : ℝ) - h₂) (bitsToEVal (X - Y).lo.toBits) ∧
      IsRoundUpR ((h₁ : ℝ) - l₂) (bitsToEVal (X - Y).hi.toBits) := by
  rw [← Rat.cast_sub, ← Rat.cast_sub, isRoundDownR_cast_iff, isRoundUpR_cast_iff]
  exact sub_iv_tight hX hY

/-- Generic transfer of a rational optimality statement to `ℝ`. -/
theorem optimalR_of_optimal {S T : Set ℝ} {op : ℝ → ℝ → ℝ} {opq : ℚ → ℚ → ℚ}
    (hop : ∀ p q : ℚ, ((opq p q : ℚ) : ℝ) = op p q) {X Y Z : Interval64}
    (hS : S = X.toSet) (hT : T = Y.toSet)
    (h : (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → f ≤ opq x y) →
          hiEncloses? (bitsToEVal Z.lo.toBits) f) ∧
        (∀ f, Representable f → (∀ x y, MemIv x X → MemIv y Y → opq x y ≤ f) →
          loEncloses? (bitsToEVal Z.hi.toBits) f)) :
    (∀ f : ℝ, RepresentableR f → (∀ x ∈ S, ∀ y ∈ T, f ≤ op x y) →
        hiR (bitsToEVal Z.lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → (∀ x ∈ S, ∀ y ∈ T, op x y ≤ f) →
        loR (bitsToEVal Z.hi.toBits) f) := by
  subst hS hT
  refine ⟨?_, ?_⟩
  · rintro f ⟨q, hq, rfl⟩ hf
    refine (hiR_cast _ _).2 (h.1 q hq fun x y hx hy => ?_)
    have := hf x (cast_mem_toSet_iff.2 hx) y (cast_mem_toSet_iff.2 hy)
    rw [← hop] at this; exact_mod_cast this
  · rintro f ⟨q, hq, rfl⟩ hf
    refine (loR_cast _ _).2 (h.2 q hq fun x y hx hy => ?_)
    have := hf x (cast_mem_toSet_iff.2 hx) y (cast_mem_toSet_iff.2 hy)
    rw [← hop] at this; exact_mod_cast this

/-- `(X + Y).lo` is the greatest representable lower bound, and `(X + Y).hi` the
    least representable upper bound, of `{x + y | x ∈ X, y ∈ Y}` over `ℝ`. -/
theorem add_iv_optimalR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, f ≤ x + y) →
        hiR (bitsToEVal (X + Y).lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, x + y ≤ f) →
        loR (bitsToEVal (X + Y).hi.toBits) f) :=
  optimalR_of_optimal (fun p q => Rat.cast_add p q) rfl rfl (add_iv_optimal hX hY)

theorem sub_iv_optimalR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, f ≤ x - y) →
        hiR (bitsToEVal (X - Y).lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, x - y ≤ f) →
        loR (bitsToEVal (X - Y).hi.toBits) f) :=
  optimalR_of_optimal (fun p q => Rat.cast_sub p q) rfl rfl (sub_iv_optimal hX hY)

theorem mul_iv_optimalR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂) :
    (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, f ≤ x * y) →
        hiR (bitsToEVal (X * Y).lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, x * y ≤ f) →
        loR (bitsToEVal (X * Y).hi.toBits) f) :=
  optimalR_of_optimal (fun p q => Rat.cast_mul p q) rfl rfl (mul_iv_optimal hX hY)

theorem div_iv_optimalR (hX : FinIv X l₁ h₁) (hY : FinIv Y l₂ h₂)
    (hz : containsZero Y = false) :
    (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, f ≤ x / y) →
        hiR (bitsToEVal (X / Y).lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → (∀ x ∈ X.toSet, ∀ y ∈ Y.toSet, x / y ≤ f) →
        loR (bitsToEVal (X / Y).hi.toBits) f) :=
  optimalR_of_optimal (fun p q => Rat.cast_div p q) rfl rfl (div_iv_optimal hX hY hz)

end iv

/-! ### Interval square root -/

theorem sqrt_iv_tightR {X : Interval64} {l h : ℚ} (hX : FinIv X l h) (hh : 0 ≤ h) :
    IsRoundDownR (Real.sqrt l) (bitsToEVal (Interval64.sqrt X).lo.toBits) ∧
      IsRoundUpR (Real.sqrt h) (bitsToEVal (Interval64.sqrt X).hi.toBits) := by
  obtain ⟨hlo, hhi⟩ := sqrt_iv_tight hX hh
  refine ⟨?_, isRoundUpR_sqrt_of_isSqrtUp hhi⟩
  have := isRoundDownR_sqrt_of_isSqrtDown hlo
  split_ifs at this with hl
  · have : Real.sqrt (l : ℝ) = Real.sqrt ((0 : ℚ) : ℝ) := by
      rw [Rat.cast_zero, Real.sqrt_zero]
      exact Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast hl.le)
    rwa [this]
  · exact this

/-- `(sqrt X).lo` is the greatest representable lower bound and `(sqrt X).hi` the
    least representable upper bound of `{√x | x ∈ X, 0 ≤ x}` (finite endpoints, `0 ≤ hi`). -/
theorem sqrt_iv_optimalR {X : Interval64} {l h : ℚ} (hX : FinIv X l h) (hh : 0 ≤ h) :
    (∀ f : ℝ, RepresentableR f → 0 ≤ f → (∀ x ∈ X.toSet, 0 ≤ x → f ≤ Real.sqrt x) →
        hiR (bitsToEVal (Interval64.sqrt X).lo.toBits) f) ∧
      (∀ f : ℝ, RepresentableR f → 0 ≤ f → (∀ x ∈ X.toSet, 0 ≤ x → Real.sqrt x ≤ f) →
        loR (bitsToEVal (Interval64.sqrt X).hi.toBits) f) := by
  obtain ⟨h1, h2⟩ := sqrt_iv_optimal hX hh
  refine ⟨?_, ?_⟩
  · rintro f ⟨q, hq, rfl⟩ hf0 hf
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hf0
    refine (hiR_cast _ _).2 (h1 q hq hq0 fun x hx hx0 => ?_)
    have hx0' : (0 : ℝ) ≤ x := by exact_mod_cast hx0
    have hle := hf x (cast_mem_toSet_iff.2 hx) hx0'
    have : (q : ℝ) * q ≤ x := by
      calc (q : ℝ) * q ≤ Real.sqrt x * Real.sqrt x := mul_self_le_mul_self hf0 hle
        _ = x := Real.mul_self_sqrt hx0'
    exact_mod_cast this
  · rintro f ⟨q, hq, rfl⟩ hf0 hf
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hf0
    refine (loR_cast _ _).2 (h2 q hq hq0 fun x hx hx0 => ?_)
    have hx0' : (0 : ℝ) ≤ x := by exact_mod_cast hx0
    have hle := hf x (cast_mem_toSet_iff.2 hx) hx0'
    have : (x : ℝ) ≤ q * q := by
      calc (x : ℝ) = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0').symm
        _ ≤ q * q := mul_self_le_mul_self (Real.sqrt_nonneg _) hle
    exact_mod_cast this

end RealFP
