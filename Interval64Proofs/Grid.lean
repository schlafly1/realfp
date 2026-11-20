/-
The binary64 grid: representable rationals, optimal ("tight") directed
rounding predicates, and the two grid lemmas that make tightness proofs work.

* `IsRoundDown x r`: `r` is a lower bound of `x` and every representable
  `q ≤ x` satisfies `q ≤ r` (so `r` is the greatest representable `≤ x`,
  or `−∞` when there is none).
* `IsRoundUp x r`: dually.

Grid lemmas (magnitudes): if `M·2^E ≤ X < (M+1)·2^E` and either
`E = minExponent` or `M ≥ 2^52`, then no canonical binary64 magnitude lies
in `(M·2^E, X]`, and if `M·2^E < X` none lies in `[X, (M+1)·2^E)`.
-/
import Interval64.OfRat
import Interval64Proofs.AddBits

namespace Interval64Proofs.Grid

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Small `Rat` order helpers (core has few `<` lemmas) -/

theorem rlt_of_le_of_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  Rat.not_le.mp (fun h => (Rat.not_le.mpr h₂) (Rat.le_trans h h₁))

theorem rlt_of_lt_of_le {a b c : Rat} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  Rat.not_le.mp (fun h => (Rat.not_le.mpr h₁) (Rat.le_trans h₂ h))

theorem rlt_trans {a b c : Rat} (h₁ : a < b) (h₂ : b < c) : a < c :=
  rlt_of_le_of_lt (Rat.le_of_lt h₁) h₂

theorem rneg_nonpos {a : Rat} (h : 0 ≤ a) : -a ≤ 0 := by
  have := (Rat.neg_le_neg_iff).mpr h
  simpa using this

/-! ### Tight rounding predicates -/

/-- `r` is the greatest representable value `≤ x` (`−∞` if none). -/
def IsRoundDown (x : Rat) (r : Option EVal) : Prop :=
  loEncloses? r x ∧ ∀ q, Representable q → q ≤ x → hiEncloses? r q

/-- `r` is the least representable value `≥ x` (`+∞` if none). -/
def IsRoundUp (x : Rat) (r : Option EVal) : Prop :=
  hiEncloses? r x ∧ ∀ q, Representable q → x ≤ q → loEncloses? r q

theorem representable_of_bitsToEVal {b : UInt64} {q : Rat}
    (h : bitsToEVal b = some (.rat q)) : Representable q :=
  ⟨b, by rw [bitsToRat?_eq_bitsToEVal, h]⟩

/-- Rounding down is unique among values of bit patterns. -/
theorem isRoundDown_unique {x : Rat} {a b : UInt64}
    (ha : IsRoundDown x (bitsToEVal a)) (hb : IsRoundDown x (bitsToEVal b)) :
    bitsToEVal a = bitsToEVal b := by
  rcases ha with ⟨hal, hao⟩
  rcases hb with ⟨hbl, hbo⟩
  cases hva : bitsToEVal a with
  | none => rw [hva] at hal; exact hal.elim
  | some va =>
    cases hvb : bitsToEVal b with
    | none => rw [hvb] at hbl; exact hbl.elim
    | some vb =>
      rw [hva] at hal hao
      rw [hvb] at hbl hbo
      cases va with
      | posInf => exact hal.elim
      | negInf =>
        cases vb with
        | posInf => exact hbl.elim
        | negInf => rfl
        | rat qb =>
          exact (hao qb (representable_of_bitsToEVal hvb) hbl).elim
      | rat qa =>
        cases vb with
        | posInf => exact hbl.elim
        | negInf =>
          exact (hbo qa (representable_of_bitsToEVal hva) hal).elim
        | rat qb =>
          have h1 : qa ≤ qb := hbo qa (representable_of_bitsToEVal hva) hal
          have h2 : qb ≤ qa := hao qb (representable_of_bitsToEVal hvb) hbl
          rw [Rat.le_antisymm h1 h2]

theorem isRoundUp_unique {x : Rat} {a b : UInt64}
    (ha : IsRoundUp x (bitsToEVal a)) (hb : IsRoundUp x (bitsToEVal b)) :
    bitsToEVal a = bitsToEVal b := by
  rcases ha with ⟨hal, hao⟩
  rcases hb with ⟨hbl, hbo⟩
  cases hva : bitsToEVal a with
  | none => rw [hva] at hal; exact hal.elim
  | some va =>
    cases hvb : bitsToEVal b with
    | none => rw [hvb] at hbl; exact hbl.elim
    | some vb =>
      rw [hva] at hal hao
      rw [hvb] at hbl hbo
      cases va with
      | negInf => exact hal.elim
      | posInf =>
        cases vb with
        | negInf => exact hbl.elim
        | posInf => rfl
        | rat qb =>
          exact (hao qb (representable_of_bitsToEVal hvb) hbl).elim
      | rat qa =>
        cases vb with
        | negInf => exact hbl.elim
        | posInf =>
          exact (hbo qa (representable_of_bitsToEVal hva) hal).elim
        | rat qb =>
          have h1 : qb ≤ qa := hbo qa (representable_of_bitsToEVal hva) hal
          have h2 : qa ≤ qb := hao qb (representable_of_bitsToEVal hvb) hbl
          rw [Rat.le_antisymm h1 h2]

/-- A representable value rounds to itself. -/
theorem isRoundDown_self (q : Rat) : IsRoundDown q (some (.rat q)) :=
  ⟨Rat.le_refl, fun _ _ h => h⟩

theorem isRoundUp_self (q : Rat) : IsRoundUp q (some (.rat q)) :=
  ⟨Rat.le_refl, fun _ _ h => h⟩

/-! ### Representable rationals -/

theorem representable_cases {q : Rat} (h : Representable q) :
    q = 0 ∨ ∃ s n e, IsCanonicalFinite n e ∧ q = signedVal s n e := by
  rcases h with ⟨b, hb⟩
  rcases bitsToRat?_cases hb with ⟨_, _, hq⟩ | ⟨s, n, e, _, _, hq, hc⟩
  · exact Or.inl hq
  · exact Or.inr ⟨s, n, e, hc, hq⟩

theorem canonical_bounds {n : Nat} {e : Int} (hc : IsCanonicalFinite n e) :
    0 < n ∧ n < 2 ^ 53 ∧ spec64.minExponent ≤ e ∧ e < overflowExponent := by
  rcases hc with ⟨he, hn, hlt⟩ | ⟨he, hov, hlo, hlt⟩
  · refine ⟨hn, Nat.lt_trans hlt (by decide), Int.le_of_eq he.symm, ?_⟩
    rw [he]; decide
  · exact ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos 52) hlo, hlt, he, hov⟩

theorem representable_zero : Representable 0 := ⟨0, by decide⟩

/-- Value of `MaxFinite`. -/
def maxVal : Rat := mag (2 ^ 53 - 1) 971

theorem mag_le_maxVal {n : Nat} {e : Int} (hc : IsCanonicalFinite n e) :
    mag n e ≤ maxVal := by
  have ⟨_, hn, _, he⟩ := canonical_bounds hc
  have h1 : mag n e ≤ mag (2 ^ 53 - 1) e := mag_le_mag (by omega)
  have h2 : mag (2 ^ 53 - 1) e ≤ mag (2 ^ 53 - 1) 971 :=
    mag_mono_exp (by simp [overflowExponent] at he; omega)
  exact Rat.le_trans h1 h2

theorem maxVal_lt_of_overflow {m : Nat} {e : Int} (h : IsOverflowNormal m e) :
    maxVal < mag m e := by
  have ⟨hov, hlo, _⟩ := h
  exact rlt_of_lt_of_le mag_maxFinite_lt_overflow
    (Rat.le_trans (mag_mono_exp hov) (mag_le_mag hlo))

theorem neg_maxVal_le_of_representable {q : Rat} (h : Representable q) :
    -maxVal ≤ q := by
  have hmax : (0 : Rat) ≤ maxVal := mag_nonneg _ _
  rcases representable_cases h with rfl | ⟨s, n, e, hc, rfl⟩
  · exact rneg_nonpos hmax
  · cases s with
    | positive =>
      exact Rat.le_trans (rneg_nonpos hmax) (mag_nonneg _ _)
    | negative =>
      exact (Rat.neg_le_neg_iff).mpr (mag_le_maxVal hc)

theorem le_maxVal_of_representable {q : Rat} (h : Representable q) : q ≤ maxVal := by
  have hmax : (0 : Rat) ≤ maxVal := mag_nonneg _ _
  rcases representable_cases h with rfl | ⟨s, n, e, hc, rfl⟩
  · exact hmax
  · cases s with
    | positive => exact mag_le_maxVal hc
    | negative =>
      exact Rat.le_trans (rneg_nonpos (mag_nonneg _ _)) hmax

/-! ### Grid lemmas -/

theorem lt_of_mag_lt {a b : Nat} {E : Int} (h : mag a E < mag b E) : a < b := by
  apply Nat.lt_of_not_le
  intro hle
  exact Rat.lt_irrefl (rlt_of_lt_of_le h (mag_le_mag hle))

/-- A magnitude at exponent `≥ E` is an integer multiple of `2^E`. -/
theorem mag_as_multiple {n : Nat} {e E : Int} (h : E ≤ e) :
    mag n e = mag (n * 2 ^ (e - E).toNat) E := by
  rw [mag_mul_two_pow_add]
  congr 1
  omega

theorem mag_lt_pow52 {n : Nat} {e E : Int} (hn : n < 2 ^ 53) (h : e < E) :
    mag n e < mag (2 ^ 52) E := by
  have h1 : mag n e < mag (2 ^ 53) e := mag_lt_mag hn
  have h2 : mag (2 ^ 53) e ≤ mag (2 ^ 52) E := by
    rw [mag_two_pow, mag_two_pow]
    exact pow2_le (by omega)
  exact rlt_of_lt_of_le h1 h2

/-- Grid lemma (floor side). -/
theorem grid_floor {M n : Nat} {E e : Int} {X : Rat}
    (hnorm : E = spec64.minExponent ∨ 2 ^ 52 ≤ M)
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

/-- Grid lemma (ceiling side). -/
theorem grid_ceil {M n : Nat} {E e : Int} {X : Rat}
    (hnorm : E = spec64.minExponent ∨ 2 ^ 52 ≤ M)
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

end Interval64Proofs.Grid
