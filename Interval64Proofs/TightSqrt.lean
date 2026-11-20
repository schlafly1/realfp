/-
Tightness of the directed square roots, stated with squares (no real `√`).

For a finite `a` with value `qa ≥ 0`:
* `sqrtDown a` is the greatest representable `ρ ≥ 0` with `ρ² ≤ qa`;
* `sqrtUp a`   is the least representable `ρ ≥ 0` with `qa ≤ ρ²`.

Interval level: for `X = [l, h]` with finite endpoints and `h ≥ 0`,
`(sqrt X).lo` is the tight lower root of `max l 0` (the clipped endpoint)
and `(sqrt X).hi` the tight upper root of `h`.
-/
import Interval64Proofs.TightIv
import Interval64Proofs.Sqrt

namespace Interval64Proofs.TightSqrt

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.RoundDirected
open Interval64Proofs.RoundInexact
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem
open Interval64Proofs.Div
open Interval64Proofs.Sqrt
open Interval64Proofs.Grid
open Interval64Proofs.RoundOpt
open Interval64Proofs.OfRat
open Interval64Proofs.Tight
open Interval64Proofs.TightIv
open Float.Model
open Float.Model.UnpackedFloat

/-- `r` is the greatest representable `ρ ≥ 0` with `ρ² ≤ qa`. -/
def IsSqrtDown (qa : Rat) (r : Option EVal) : Prop :=
  ∃ ρ, r = some (.rat ρ) ∧ 0 ≤ ρ ∧ ρ * ρ ≤ qa ∧
    ∀ f, Representable f → 0 ≤ f → f * f ≤ qa → f ≤ ρ

/-- `r` is the least representable `ρ ≥ 0` with `qa ≤ ρ²`. -/
def IsSqrtUp (qa : Rat) (r : Option EVal) : Prop :=
  ∃ ρ, r = some (.rat ρ) ∧ 0 ≤ ρ ∧ qa ≤ ρ * ρ ∧
    ∀ f, Representable f → 0 ≤ f → qa ≤ f * f → ρ ≤ f

/-! ### Grid lemmas with a sub-`minExp` grid exponent allowed -/

theorem grid_floor' {M n : Nat} {E e : Int} {X : Rat}
    (hnorm : E ≤ spec64.minExponent ∨ 2 ^ 52 ≤ M)
    (he : spec64.minExponent ≤ e) (hn : n < 2 ^ 53)
    (hX : X < mag (M + 1) E) (hle : mag n e ≤ X) :
    mag n e ≤ mag M E := by
  by_cases hEe : E ≤ e
  · rw [mag_as_multiple hEe] at hle ⊢
    have hlt : n * 2 ^ (e - E).toNat < M + 1 := lt_of_mag_lt (rlt_of_le_of_lt hle hX)
    exact mag_le_mag (Nat.le_of_lt_succ hlt)
  · have hlt : e < E := Int.lt_of_not_ge hEe
    have hM : 2 ^ 52 ≤ M := by
      rcases hnorm with h | h
      · omega
      · exact h
    exact Rat.le_of_lt (rlt_of_lt_of_le (mag_lt_pow52 hn hlt) (mag_le_mag hM))

theorem grid_ceil' {M n : Nat} {E e : Int} {X : Rat}
    (hnorm : E ≤ spec64.minExponent ∨ 2 ^ 52 ≤ M)
    (he : spec64.minExponent ≤ e) (hn : n < 2 ^ 53)
    (hX : mag M E < X) (hle : X ≤ mag n e) :
    mag (M + 1) E ≤ mag n e := by
  by_cases hEe : E ≤ e
  · rw [mag_as_multiple hEe] at hle ⊢
    have hlt : M < n * 2 ^ (e - E).toNat := lt_of_mag_lt (rlt_of_lt_of_le hX hle)
    exact mag_le_mag hlt
  · have hlt : e < E := Int.lt_of_not_ge hEe
    have hM : 2 ^ 52 ≤ M := by
      rcases hnorm with h | h
      · omega
      · exact h
    have : mag n e < X :=
      rlt_trans (rlt_of_lt_of_le (mag_lt_pow52 hn hlt) (mag_le_mag hM)) hX
    exact (Rat.lt_irrefl (rlt_of_lt_of_le this hle)).elim

/-! ### Representable nonnegative values on the grid -/

theorem rep_nonneg_cases {f : Rat} (hf : Representable f) (h0 : 0 ≤ f) :
    f = 0 ∨ ∃ n e, IsCanonicalFinite n e ∧ f = mag n e := by
  rcases representable_cases hf with h | ⟨s, n, e, hc, rfl⟩
  · exact Or.inl h
  · cases s with
    | positive => exact Or.inr ⟨n, e, hc, rfl⟩
    | negative =>
      have := signedVal_neg_lt_zero (e := e) (canonical_bounds hc).1
      exact ((Rat.lt_iff_le_and_not_ge.mp this).2 h0).elim

theorem rep_le_of_lt_succ {root : Nat} {te : Int} {f : Rat}
    (hen : te ≤ spec64.minExponent ∨ 2 ^ 52 ≤ root)
    (hf : Representable f) (h0 : 0 ≤ f) (hlt : f < mag (root + 1) te) :
    f ≤ mag root te := by
  rcases rep_nonneg_cases hf h0 with rfl | ⟨n, e, hc, rfl⟩
  · exact mag_nonneg _ _
  · have ⟨_, hn, he, _⟩ := canonical_bounds hc
    exact grid_floor' hen he hn hlt Rat.le_refl

theorem succ_le_of_rep_gt {root : Nat} {te : Int} {f : Rat}
    (hen : te ≤ spec64.minExponent ∨ 2 ^ 52 ≤ root)
    (hf : Representable f) (hgt : mag root te < f) :
    mag (root + 1) te ≤ f := by
  have h0 : 0 ≤ f := Rat.le_of_lt (rlt_of_le_of_lt (mag_nonneg _ _) hgt)
  rcases rep_nonneg_cases hf h0 with rfl | ⟨n, e, hc, rfl⟩
  · exact (Rat.lt_irrefl (rlt_of_le_of_lt (mag_nonneg root te) hgt)).elim
  · have ⟨_, hn, he, _⟩ := canonical_bounds hc
    exact grid_ceil' hen he hn hgt Rat.le_refl

/-! ### From tight rounding of a witness to tight square roots -/

theorem isSqrtDown_of {qa v : Rat} {b : UInt64} (h : IsRoundDown v (bitsToEVal b))
    (hv : 0 ≤ v)
    (hsq : ∀ ρ, Representable ρ → 0 ≤ ρ → ρ ≤ v → ρ * ρ ≤ qa)
    (hopt : ∀ f, Representable f → 0 ≤ f → f * f ≤ qa → f ≤ v) :
    IsSqrtDown qa (bitsToEVal b) := by
  rcases h with ⟨hlo, hall⟩
  have h0 := hall 0 representable_zero hv
  cases hb : bitsToEVal b with
  | none => rw [hb] at hlo; simp [loEncloses?] at hlo
  | some ev =>
    rw [hb] at hlo h0 hall
    cases ev with
    | negInf => simp [hiEncloses?, hiEncloses] at h0
    | posInf => simp [loEncloses?, loEncloses] at hlo
    | rat ρ =>
      have hρ0 : 0 ≤ ρ := h0
      have hρv : ρ ≤ v := hlo
      exact ⟨ρ, rfl, hρ0, hsq ρ (representable_of_bitsToEVal hb) hρ0 hρv,
        fun f hf hf0 hff => hall f hf (hopt f hf hf0 hff)⟩

theorem isSqrtUp_of {qa v : Rat} {b : UInt64} (h : IsRoundUp v (bitsToEVal b))
    (hv : 0 ≤ v) (hex : ∃ g, Representable g ∧ v ≤ g)
    (hsq : ∀ ρ, Representable ρ → v ≤ ρ → qa ≤ ρ * ρ)
    (hopt : ∀ f, Representable f → 0 ≤ f → qa ≤ f * f → v ≤ f) :
    IsSqrtUp qa (bitsToEVal b) := by
  rcases h with ⟨hhi, hall⟩
  rcases hex with ⟨g, hg, hvg⟩
  have hg' := hall g hg hvg
  cases hb : bitsToEVal b with
  | none => rw [hb] at hhi; simp [hiEncloses?] at hhi
  | some ev =>
    rw [hb] at hhi hg' hall
    cases ev with
    | negInf => simp [hiEncloses?, hiEncloses] at hhi
    | posInf => simp [loEncloses?, loEncloses] at hg'
    | rat ρ =>
      have hvρ : v ≤ ρ := hhi
      exact ⟨ρ, rfl, Rat.le_trans hv hvρ, hsq ρ (representable_of_bitsToEVal hb) hvρ,
        fun f hf hf0 hff => hall f hf (hopt f hf hf0 hff)⟩

/-! ### Arithmetic helpers -/

theorem four_le_maxVal : (4 : Rat) ≤ maxVal := by
  have h : mag 4 0 = 4 := by simp [mag, Interval64.Spec.pow2]
  rw [← h]; unfold maxVal
  exact Rat.le_trans (mag_mono_exp (by decide)) (mag_le_mag (by decide))

theorem add_self_le_maxVal {R : Rat} (hR : 0 ≤ R) (h : R * R ≤ maxVal) :
    R + R ≤ maxVal := by
  have h22 : (2 : Rat) + 2 = 4 := by
    have := (Rat.natCast_add 2 2).symm
    simpa using this
  have h11 : (1 : Rat) + 1 = 2 := by
    have := (Rat.natCast_add 1 1).symm
    simpa using this
  by_cases h2 : (2 : Rat) ≤ R
  · have h2R : R + R = 2 * R := by
      have h := Rat.add_mul 1 1 R
      rw [h11, Rat.one_mul] at h
      exact h.symm
    rw [h2R]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h2 hR) h
  · have hle : R ≤ 2 := Rat.le_of_lt (Rat.not_le.mp h2)
    have : R + R ≤ 2 + 2 :=
      Rat.le_trans (Rat.add_le_add_left.mpr hle) (Rat.add_le_add_right.mpr hle)
    rw [h22] at this
    exact Rat.le_trans this four_le_maxVal

theorem two_mag_bound {root : Nat} {te : Int} (hroot : 0 < root) :
    mag (root + 1) te ≤ mag root te + mag root te := by
  rw [← mag_add]; exact mag_le_mag (by omega)

theorem representable_maxVal : Representable maxVal := by
  have := representable_of_bitsToEVal (bitsToEVal_pack_maxFinite .positive)
  exact this

theorem mag_half_split (n : Nat) (e : Int) : mag n e = mag (2 * n) (e - 1) := by
  have h := mag_mul_two_pow_add n 1 (e - 1)
  rw [show e - 1 + ((1 : Nat) : Int) = e by omega, Nat.pow_one, Nat.mul_comm] at h
  exact h.symm

theorem mag_inj {a b : Nat} {E : Int} (h : mag a E = mag b E) : a = b := by
  rcases Nat.lt_trichotomy a b with hl | he | hg
  · have := mag_lt_mag (e := E) hl
    rw [h] at this
    exact (Rat.lt_irrefl this).elim
  · exact he
  · have := mag_lt_mag (e := E) hg
    rw [h] at this
    exact (Rat.lt_irrefl this).elim

theorem sqrtCore_exact_of_sq {m : Nat} {e : Int}
    (h : mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 *
      mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 = mag m e) :
    (sqrtCore spec64 m e).2.2 = .exact := by
  rw [mag_sq_two, ← mag_shiftLeft_two_te m e] at h
  exact (sqrtCore_acc_exact_iff m e).mpr (mag_inj h).symm

/-! ### The positive finite case -/

theorem sqrt_core_tight (root : Nat) (te : Int) (acc : Accuracy) (qa : Rat)
    (hroot : 0 < root)
    (hlo : mag root te * mag root te ≤ qa)
    (hhi : qa < mag (root + 1) te * mag (root + 1) te)
    (hex : acc = .exact → mag root te * mag root te = qa)
    (hin : ∀ o, acc = .inexact o → mag root te * mag root te < qa)
    (hen : te ≤ spec64.minExponent ∨ 2 ^ 52 ≤ root)
    (hmax : qa ≤ maxVal) :
    IsSqrtDown qa (bitsToEVal (packDirected false (roundDirected .positive root te acc false))) ∧
      IsSqrtUp qa (bitsToEVal (packDirected true (roundDirected .positive root te acc true))) := by
  have hR0 : 0 ≤ mag root te := mag_nonneg _ _
  have hS : mag (root + 1) te ≤ maxVal :=
    Rat.le_trans (two_mag_bound hroot) (add_self_le_maxVal hR0 (Rat.le_trans hlo hmax))
  have hbelow : ∀ f, 0 ≤ f → f * f ≤ qa → f < mag (root + 1) te := fun f _ hff =>
    Rat.not_le.mp (fun hle => Rat.lt_irrefl
      (rlt_of_lt_of_le hhi (Rat.le_trans (sq_le_sq_of_nonneg (mag_nonneg _ _) hle) hff)))
  cases acc with
  | exact =>
    have hsq := hex rfl
    have hv : mag root te = signedVal .positive root te := rfl
    have hD := roundDirected_isRoundDown .positive root te .exact (mag root te)
      (fun _ => hv) (fun _ h => by cases h) (Or.inl rfl)
    have hU := roundDirected_isRoundUp .positive root te .exact (mag root te)
      (fun _ => hv) (fun _ h => by cases h) (Or.inl rfl)
    refine ⟨isSqrtDown_of hD hR0 ?_ ?_,
      isSqrtUp_of hU hR0 ⟨maxVal, representable_maxVal,
        Rat.le_trans (mag_le_mag (Nat.le_succ root)) hS⟩ ?_ ?_⟩
    · intro ρ _ hρ0 hρv; rw [← hsq]; exact sq_le_sq_of_nonneg hρ0 hρv
    · intro f _ hf0 hff; rw [← hsq] at hff; exact le_of_sq_le_sq hf0 hR0 hff
    · intro ρ _ hρv; rw [← hsq]; exact sq_le_sq_of_nonneg hR0 hρv
    · intro f _ hf0 hff; rw [← hsq] at hff; exact le_of_sq_le_sq hR0 hf0 hff
  | inexact o =>
    have hlt := hin o rfl
    have hRv : mag root te < mag (2 * root + 1) (te - 1) := by
      rw [mag_half_split root te]; exact mag_lt_mag (by omega)
    have hvS : mag (2 * root + 1) (te - 1) < mag (root + 1) te := by
      rw [mag_half_split (root + 1) te]; exact mag_lt_mag (by omega)
    have hinM : inexactMag root te (signedMag .positive (mag (2 * root + 1) (te - 1))) :=
      ⟨hRv, hvS⟩
    have hD := roundDirected_isRoundDown .positive root te (.inexact o)
      (mag (2 * root + 1) (te - 1)) (fun h => by cases h) (fun _ _ => hinM) (Or.inr hen)
    have hU := roundDirected_isRoundUp .positive root te (.inexact o)
      (mag (2 * root + 1) (te - 1)) (fun h => by cases h) (fun _ _ => hinM) (Or.inr hen)
    have hv0 : 0 ≤ mag (2 * root + 1) (te - 1) := mag_nonneg _ _
    refine ⟨isSqrtDown_of hD hv0 ?_ ?_,
      isSqrtUp_of hU hv0 ⟨maxVal, representable_maxVal,
        Rat.le_of_lt (rlt_of_lt_of_le hvS hS)⟩ ?_ ?_⟩
    · intro ρ hρ hρ0 hρv
      have := rep_le_of_lt_succ hen hρ hρ0 (rlt_of_le_of_lt hρv hvS)
      exact Rat.le_trans (sq_le_sq_of_nonneg hρ0 this) hlo
    · intro f hf hf0 hff
      exact Rat.le_trans (rep_le_of_lt_succ hen hf hf0 (hbelow f hf0 hff)) (Rat.le_of_lt hRv)
    · intro ρ hρ hρv
      have h1 := succ_le_of_rep_gt hen hρ (rlt_of_lt_of_le hRv hρv)
      exact Rat.le_of_lt (rlt_of_lt_of_le hhi (sq_le_sq_of_nonneg (mag_nonneg _ _) h1))
    · intro f hf hf0 hff
      have hRf : mag root te < f := Rat.not_le.mp (fun hle => Rat.lt_irrefl
        (rlt_of_lt_of_le hlt (Rat.le_trans hff (sq_le_sq_of_nonneg hf0 hle))))
      exact Rat.le_trans (Rat.le_of_lt hvS) (succ_le_of_rep_gt hen hf hRf)

/-! ### Scalar square-root tightness -/

/-- **Directed sqrt is tight.** For a finite `a` with value `qa ≥ 0`, `sqrtDown a`
is the greatest representable `ρ ≥ 0` with `ρ² ≤ qa`, and `sqrtUp a` the least
representable `ρ ≥ 0` with `qa ≤ ρ²`. -/
theorem sqrt_tight {a : UInt64} {qa : Rat} (ha : bitsToRat? a = some qa) (hqa : 0 ≤ qa) :
    IsSqrtDown qa (bitsToEVal (sqrtDown a)) ∧ IsSqrtUp qa (bitsToEVal (sqrtUp a)) := by
  have hmax : qa ≤ maxVal := le_maxVal_of_representable ⟨a, ha⟩
  simp only [sqrtDown, sqrtUp, Interval64.Spec.sqrt]
  rcases bitsToRat?_cases ha with ⟨s, hu, rfl⟩ | ⟨s, m, e, hm, hu, rfl, hc⟩
  · rw [hu]
    simp only [sqrtU]
    refine ⟨isSqrtDown_of (isRoundDown_zero false s) Rat.le_refl ?_ ?_,
      isSqrtUp_of (isRoundUp_zero true s) Rat.le_refl ⟨0, representable_zero, Rat.le_refl⟩
        (fun ρ _ hρ => Rat.mul_nonneg hρ hρ) (fun _ _ hf0 _ => hf0)⟩
    · intro ρ _ hρ0 hρv
      have : ρ = 0 := Rat.le_antisymm hρv hρ0
      subst this
      rw [Rat.zero_mul]; exact Rat.le_refl
    · intro f _ hf0 hff
      exact le_of_sq_le_sq hf0 Rat.le_refl (by rw [Rat.zero_mul]; exact hff)
  · cases s with
    | negative =>
      have : signedVal .negative m e < 0 := signedVal_neg_lt_zero hm
      exact ((Rat.lt_iff_le_and_not_ge.mp this).2 hqa).elim
    | positive =>
      rw [hu]
      have hs : m < 2 ^ 53 := Interval64Proofs.ExactAdd.canonical_mantissa_lt hc
      have hbr := sqrtCore_mag_bracket m e
      have hinx : ∀ o, (sqrtCore spec64 m e).2.2 = .inexact o →
          mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 *
            mag (sqrtCore spec64 m e).1 (sqrtCore spec64 m e).2.1 < mag m e := by
        intro o ho
        refine Rat.lt_of_le_of_ne hbr.1 ?_
        intro heq
        have := sqrtCore_exact_of_sq heq
        rw [ho] at this
        cases this
      rw [sqrtU_finite_eq_round]
      exact sqrt_core_tight _ _ _ _ (sqrtCore_root_pos hm) hbr.1 (hbr.2 hm)
        sqrtCore_mag_eq_of_exact hinx (sqrtCore_enough_bits hm hs) hmax

theorem sqrtDown_tight {a : UInt64} {qa : Rat} (ha : bitsToRat? a = some qa) (hqa : 0 ≤ qa) :
    IsSqrtDown qa (bitsToEVal (sqrtDown a)) := (sqrt_tight ha hqa).1

theorem sqrtUp_tight {a : UInt64} {qa : Rat} (ha : bitsToRat? a = some qa) (hqa : 0 ≤ qa) :
    IsSqrtUp qa (bitsToEVal (sqrtUp a)) := (sqrt_tight ha hqa).2

theorem sqrtDown_float_tight {a : Float} {qa : Rat} (ha : bitsToRat? a.toBits = some qa)
    (hqa : 0 ≤ qa) : IsSqrtDown qa (bitsToEVal (Interval64.Directed.sqrtDown a).toBits) := by
  rcases sqrtDown_tight ha hqa with ⟨ρ, hρ, rest⟩
  rw [sqrtDown_toBits, bitsToEVal_pack_unpack_of_some hρ]
  exact ⟨ρ, rfl, rest⟩

theorem sqrtUp_float_tight {a : Float} {qa : Rat} (ha : bitsToRat? a.toBits = some qa)
    (hqa : 0 ≤ qa) : IsSqrtUp qa (bitsToEVal (Interval64.Directed.sqrtUp a).toBits) := by
  rcases sqrtUp_tight ha hqa with ⟨ρ, hρ, rest⟩
  rw [sqrtUp_toBits, bitsToEVal_pack_unpack_of_some hρ]
  exact ⟨ρ, rfl, rest⟩

/-! ### Interval square root -/

/-- `Interval64.sqrt X` endpoints are the tight roots of the clipped lower endpoint
and of the upper endpoint (finite endpoints, `0 ≤ h`). -/
theorem sqrt_iv_tight {X : Interval64.Interval64} {l h : Rat} (hX : FinIv X l h)
    (hh : 0 ≤ h) :
    IsSqrtDown (if l < 0 then 0 else l) (bitsToEVal (Interval64.sqrt X).lo.toBits) ∧
      IsSqrtUp h (bitsToEVal (Interval64.sqrt X).hi.toBits) := by
  have hnan : (X.lo.isNaN || X.hi.isNaN) = false := by
    simp only [Bool.or_eq_false_iff]
    exact ⟨not_isNaN_of_MemIv_lo (memIv_lo hX), not_isNaN_of_MemIv_hi (memIv_lo hX)⟩
  have hhi0 : ¬ X.hi < 0 := not_lt_zero_of_zero_le ((zero_le_iff_rat hX.2.1).mpr hh)
  have hhiDec : decide (X.hi < 0) = false := decide_eq_false hhi0
  have heq : Interval64.sqrt X =
      ⟨Interval64.Directed.sqrtDown (if decide (X.lo < 0) then (0.0 : Float) else X.lo),
        Interval64.Directed.sqrtUp X.hi⟩ := by
    unfold Interval64.sqrt
    rw [hnan, hhiDec]
    rw [ite_eq_right (by decide : ¬ (false = true))]
    rw [ite_eq_right (by decide : ¬ (false = true))]
  rw [heq]
  cases hloz : decide (X.lo < 0) with
  | true =>
    have hl : l < 0 := Rat.not_le.mp (fun hl0 =>
      not_lt_zero_of_zero_le ((zero_le_iff_rat hX.1).mpr hl0) (of_decide_eq_true hloz))
    simp only [ite_eq_left hl]
    exact ⟨sqrtDown_float_tight bitsToRat?_float_zero Rat.le_refl,
      sqrtUp_float_tight hX.2.1 hh⟩
  | false =>
    have hnlo : ¬ X.lo < 0 := of_decide_eq_false hloz
    have h0lo : (0 : Float) ≤ X.lo := le_of_not_lt_of_rats hX.1 bitsToRat?_float_zero hnlo
    have hl0 : 0 ≤ l := (zero_le_iff_rat hX.1).mp h0lo
    simp only [ite_eq_right (Rat.not_lt.mpr hl0)]
    exact ⟨sqrtDown_float_tight hX.1 hl0, sqrtUp_float_tight hX.2.1 hh⟩

/-- **Interval sqrt is optimal** (finite endpoints, `0 ≤ h`): the lower endpoint is
the greatest representable `f ≥ 0` with `f² ≤ x` for every `x ∈ X` with `x ≥ 0`, and the
upper endpoint the least representable `f ≥ 0` with `x ≤ f²` for all such `x`. -/
theorem sqrt_iv_optimal {X : Interval64.Interval64} {l h : Rat} (hX : FinIv X l h)
    (hh : 0 ≤ h) :
    (∀ f, Representable f → 0 ≤ f → (∀ x, MemIv x X → 0 ≤ x → f * f ≤ x) →
        hiEncloses? (bitsToEVal (Interval64.sqrt X).lo.toBits) f) ∧
      (∀ f, Representable f → 0 ≤ f → (∀ x, MemIv x X → 0 ≤ x → x ≤ f * f) →
        loEncloses? (bitsToEVal (Interval64.sqrt X).hi.toBits) f) := by
  have ⟨⟨ρ, hρ, _, _, hopt⟩, ⟨σ, hσ, _, _, hopt'⟩⟩ := sqrt_iv_tight hX hh
  constructor
  · intro f hf hf0 hall
    rw [hρ]
    apply hopt f hf hf0
    by_cases hl : l < 0
    · rw [ite_eq_left hl]
      exact hall 0 ((memIv_iff hX).mpr ⟨Rat.le_of_lt hl, hh⟩) Rat.le_refl
    · rw [ite_eq_right hl]
      exact hall l (memIv_lo hX) (Rat.not_lt.mp hl)
  · intro f hf hf0 hall
    rw [hσ]
    exact hopt' f hf hf0 (hall h (memIv_hi hX) hh)

end Interval64Proofs.TightSqrt
