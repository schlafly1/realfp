/-
`roundDirected` + `packDirected` is *optimal*: rounding down returns the
greatest representable binary64 `≤ v` (or `−∞` if none) and rounding up
the least representable `≥ v` (or `+∞`), under the same hypotheses used for
enclosure (`roundDirected_lo_acc`) plus the "enough bits" condition used
for `divCore` / `sqrtCore`.
-/
import Interval64Proofs.Grid
import Interval64Proofs.Div

namespace Interval64Proofs.RoundOpt

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.RoundInexact
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.AddBits
open Interval64Proofs.Div
open Interval64Proofs.Grid
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Decomposing `firstRoundedAcc` -/

/-- The pair fed to the first `shiftToTargetExponent` in `roundDirected`. -/
def preShift (m : Nat) (e : Int) : Accuracy → Nat × Int
  | .exact => decreaseExponent m e (spec64.targetExponent (totalExponent m e))
  | .inexact _ => (m, e)

/-- The truncated extended mantissa and exponent before directed rounding. -/
def shOf (m : Nat) (e : Int) (acc : Accuracy) : ExtendedMantissa × Int :=
  shiftToTargetExponent spec64 (preShift m e acc).1 (preShift m e acc).2 acc

theorem firstRoundedAcc_eq (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (up : Bool) :
    firstRoundedAcc s m e acc up =
      (roundMantissaDirected (shOf m e acc).1.mantissa up s (shOf m e acc).1.accuracy,
        (shOf m e acc).2) := by
  cases acc <;> rfl

/-- Bracket: `M·2^E ≤ X < (M+1)·2^E`, with equality iff the residual is exact. -/
def Bracket (M : Nat) (E : Int) (X : Rat) (a : Accuracy) : Prop :=
  mag M E ≤ X ∧ X < mag (M + 1) E ∧ (a = .exact → mag M E = X) ∧
    (a ≠ .exact → mag M E < X)

theorem signedMag_signedVal (s : Sign) (m : Nat) (e : Int) :
    signedMag s (signedVal s m e) = mag m e := by
  cases s <;> simp [signedMag, signedVal]

theorem mag_succ_eq (M : Nat) (E : Int) : mag (M + 1) E = mag M E + pow2 E := by
  rw [mag_add, mag_one]

theorem bracket_exact_shift (m : Nat) (e : Int) (k : Nat) :
    Bracket ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).mantissa (e + k)
      (mag m e) ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> k).accuracy := by
  rw [shiftRight_exact_mantissa]
  have hsplit := mag_split m k e
  have hmod : mag (m % 2 ^ k) e < pow2 (e + k) := by
    rw [← mag_two_pow]
    exact mag_lt_mag (Nat.mod_lt _ (Nat.two_pow_pos k))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact le_add_of_nonneg_right (mag_nonneg _ _)
  · rw [hsplit, mag_succ_eq]
    exact (Rat.add_lt_add_left).mpr hmod
  · intro hacc
    have h0 : m % 2 ^ k = 0 := (shiftRight_exact_accuracy m k).mp hacc
    rw [hsplit, h0, mag_zero, Rat.add_zero]
  · intro hacc
    have h0 : m % 2 ^ k ≠ 0 := fun h => hacc ((shiftRight_exact_accuracy m k).mpr h)
    have hpos : (0 : Rat) < mag (m % 2 ^ k) e := by
      have := mag_lt_mag (e := e) (Nat.pos_of_ne_zero h0)
      rwa [mag_zero] at this
    rw [hsplit]
    have := (Rat.add_lt_add_left (c := mag (m >>> k) (e + k))).mpr hpos
    simpa [Rat.add_zero] using this

theorem bracket_inexact_shift (m : Nat) (e : Int) (k : Nat) (o : Ordering) {X : Rat}
    (hv : inexactMag m e X) :
    Bracket ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).mantissa (e + k)
      X ((ExtendedMantissa.ofMantissaAndAccuracy m (.inexact o)) >>> k).accuracy := by
  rw [shiftRight_of_acc_mantissa]
  rcases shiftRight_of_inexact_accuracy m k o with ⟨o', ho'⟩
  rw [ho']
  have h1 : mag (m >>> k) (e + k) < X := rlt_of_le_of_lt (mag_shiftRight_le m k e) hv.1
  refine ⟨Rat.le_of_lt h1, rlt_of_lt_of_le hv.2 (mag_succ_le_shiftRight_succ m k e),
    (fun h => by cases h), (fun _ => h1)⟩

theorem shOf_bracket (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v)) :
    Bracket (shOf m e acc).1.mantissa (shOf m e acc).2 (signedMag s v)
      (shOf m e acc).1.accuracy := by
  cases acc with
  | exact =>
    rw [hex rfl, signedMag_signedVal]
    unfold shOf
    rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
    have hmag : mag m e = mag (preShift m e .exact).1 (preShift m e .exact).2 :=
      (decreaseExponent_mag _ _ _).symm
    rw [hmag]
    exact bracket_exact_shift _ _ _
  | inexact o =>
    unfold shOf
    rw [shiftToTargetExponent_em, shiftToTargetExponent_exp]
    exact bracket_inexact_shift m e _ o (hin o rfl)

/-- Toward-zero direction for a sign. -/
def tz : Sign → Bool
  | .positive => false
  | .negative => true

theorem roundMantissa_tz (M : Nat) (s : Sign) (a : Accuracy) :
    roundMantissaDirected M (tz s) s a = M := by
  cases a <;> cases s <;> rfl

theorem roundMantissa_away_inexact (M : Nat) (s : Sign) (o : Ordering) :
    roundMantissaDirected M (!tz s) s (.inexact o) = M + 1 := by
  cases s <;> rfl

theorem shOf_norm (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v))
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m)
    (hX : 0 < signedMag s v) :
    (shOf m e acc).2 = spec64.minExponent ∨ 2 ^ 52 ≤ (shOf m e acc).1.mantissa := by
  have hb := shOf_bracket s m e acc v hex hin
  by_cases hM : (shOf m e acc).1.mantissa = 0
  · -- the residual must be inexact; round away gives mantissa 1
    have hacc : (shOf m e acc).1.accuracy ≠ .exact := by
      intro h
      have := hb.2.2.1 h
      rw [hM, mag_zero] at this
      rw [← this] at hX
      exact Rat.lt_irrefl hX
    cases ha : (shOf m e acc).1.accuracy with
    | exact => exact (hacc ha).elim
    | inexact o =>
      have h0 : (firstRoundedAcc s m e acc (!tz s)).1 ≠ 0 := by
        rw [firstRoundedAcc_eq, ha, roundMantissa_away_inexact]
        omega
      have := firstRoundedAcc_norm_of_enough s m e acc (!tz s) hen h0
      rw [firstRoundedAcc_eq, ha, roundMantissa_away_inexact, hM] at this
      rcases this with h | h
      · exact Or.inl h
      · exfalso
        simp at h
  · have h0 : (firstRoundedAcc s m e acc (tz s)).1 ≠ 0 := by
      rw [firstRoundedAcc_eq, roundMantissa_tz]
      exact hM
    have := firstRoundedAcc_norm_of_enough s m e acc (tz s) hen h0
    rw [firstRoundedAcc_eq, roundMantissa_tz] at this
    exact this

/-! ### Value of the unpacked result -/

theorem toEVal_roundDirected_acc (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (up : Bool) :
    toEVal (roundDirected s m e acc up) =
      some (.rat (signedVal s (firstRoundedAcc s m e acc up).1
        (firstRoundedAcc s m e acc up).2)) := by
  rw [roundDirected_eq_shift_of_rounded_acc]
  have he := firstRoundedAcc_snd_ge_min s m e acc up
  have hm := firstRoundedAcc_fst_le_pow53 s m e acc up
  by_cases h0 : (firstRoundedAcc s m e acc up).1 = 0
  · have hshift0 := shiftToTarget_short_zero_of_first h0
    dsimp
    rw [dite_eq_left hshift0, h0, signedVal_zero]
    rfl
  · have hne := shiftToTarget_short_ne_zero_of_first h0
    dsimp
    rw [dite_eq_right hne]
    have hpres := signedVal_shiftToTarget_short s he hm
    simp [toEVal, hpres]

/-! ### Optimality of the mantissa rounding step -/

theorem mag_pos {n : Nat} (e : Int) (hn : 0 < n) : (0 : Rat) < mag n e := by
  have := mag_lt_mag (e := e) hn
  rwa [mag_zero] at this

theorem opt_down (s : Sign) (M : Nat) (E : Int) (a : Accuracy) (x : Rat)
    (hb : Bracket M E (signedMag s x) a)
    (hn : 0 < signedMag s x → E = spec64.minExponent ∨ 2 ^ 52 ≤ M) :
    ∀ q, Representable q → q ≤ x → q ≤ signedVal s (roundMantissaDirected M false s a) E := by
  intro q hq hle
  cases s with
  | positive =>
    have hR : roundMantissaDirected M false .positive a = M := roundMantissa_tz M .positive a
    rw [hR]
    simp only [signedMag] at hb hn
    simp only [signedVal]
    rcases representable_cases hq with rfl | ⟨s', n, e', hc, rfl⟩
    · exact mag_nonneg _ _
    · have ⟨hn0, hn53, he', _⟩ := canonical_bounds hc
      cases s' with
      | positive =>
        simp only [signedVal] at hle ⊢
        have hX : 0 < x := rlt_of_lt_of_le (mag_pos e' hn0) hle
        exact grid_floor (hn hX) he' hn53 hb.2.1 hle
      | negative =>
        simp only [signedVal]
        exact Rat.le_trans (rneg_nonpos (mag_nonneg _ _)) (mag_nonneg _ _)
  | negative =>
    simp only [signedMag] at hb hn
    have hx : x = -(-x) := (Rat.neg_neg x).symm
    cases a with
    | exact =>
      have hR : roundMantissaDirected M false .negative .exact = M := rfl
      rw [hR]
      simp only [signedVal]
      rw [hb.2.2.1 rfl, ← hx]
      exact hle
    | inexact o =>
      have hR : roundMantissaDirected M false .negative (.inexact o) = M + 1 := rfl
      rw [hR]
      have hlt : mag M E < -x := hb.2.2.2 (fun h => by cases h)
      have hX : 0 < -x := rlt_of_le_of_lt (mag_nonneg _ _) hlt
      have hxneg : x < 0 := by
        have := (Rat.neg_lt_neg_iff).mpr hX
        simpa using this
      simp only [signedVal]
      rcases representable_cases hq with rfl | ⟨s', n, e', hc, rfl⟩
      · exact (Rat.lt_irrefl (rlt_of_le_of_lt hle hxneg)).elim
      · have ⟨hn0, hn53, he', _⟩ := canonical_bounds hc
        cases s' with
        | positive =>
          simp only [signedVal] at hle
          exact (Rat.lt_irrefl (rlt_of_le_of_lt (Rat.le_trans (mag_nonneg _ _) hle) hxneg)).elim
        | negative =>
          simp only [signedVal] at hle ⊢
          have hle' : -x ≤ mag n e' := by
            have := (Rat.neg_le_neg_iff).mpr hle
            simpa using this
          exact (Rat.neg_le_neg_iff).mpr (grid_ceil (hn hX) he' hn53 hlt hle')

theorem opt_up (s : Sign) (M : Nat) (E : Int) (a : Accuracy) (x : Rat)
    (hb : Bracket M E (signedMag s x) a)
    (hn : 0 < signedMag s x → E = spec64.minExponent ∨ 2 ^ 52 ≤ M) :
    ∀ q, Representable q → x ≤ q → signedVal s (roundMantissaDirected M true s a) E ≤ q := by
  intro q hq hle
  cases s with
  | negative =>
    have hR : roundMantissaDirected M true .negative a = M := roundMantissa_tz M .negative a
    rw [hR]
    simp only [signedMag] at hb hn
    simp only [signedVal]
    rcases representable_cases hq with rfl | ⟨s', n, e', hc, rfl⟩
    · exact rneg_nonpos (mag_nonneg _ _)
    · have ⟨hn0, hn53, he', _⟩ := canonical_bounds hc
      cases s' with
      | negative =>
        simp only [signedVal] at hle ⊢
        have hle' : mag n e' ≤ -x := by
          have := (Rat.neg_le_neg_iff).mpr hle
          simpa using this
        have hX : 0 < -x := rlt_of_lt_of_le (mag_pos e' hn0) hle'
        exact (Rat.neg_le_neg_iff).mpr (grid_floor (hn hX) he' hn53 hb.2.1 hle')
      | positive =>
        simp only [signedVal]
        exact Rat.le_trans (rneg_nonpos (mag_nonneg _ _)) (mag_nonneg _ _)
  | positive =>
    simp only [signedMag] at hb hn
    cases a with
    | exact =>
      have hR : roundMantissaDirected M true .positive .exact = M := rfl
      rw [hR]
      simp only [signedVal]
      rw [hb.2.2.1 rfl]
      exact hle
    | inexact o =>
      have hR : roundMantissaDirected M true .positive (.inexact o) = M + 1 := rfl
      rw [hR]
      have hlt : mag M E < x := hb.2.2.2 (fun h => by cases h)
      have hX : 0 < x := rlt_of_le_of_lt (mag_nonneg _ _) hlt
      simp only [signedVal]
      rcases representable_cases hq with rfl | ⟨s', n, e', hc, rfl⟩
      · exact (Rat.lt_irrefl (rlt_of_lt_of_le hX hle)).elim
      · have ⟨hn0, hn53, he', _⟩ := canonical_bounds hc
        cases s' with
        | negative =>
          simp only [signedVal] at hle
          exact (Rat.lt_irrefl (rlt_of_lt_of_le hX
            (Rat.le_trans hle (rneg_nonpos (mag_nonneg _ _))))).elim
        | positive =>
          simp only [signedVal] at hle ⊢
          exact grid_ceil (hn hX) he' hn53 hlt hle

/-! ### Unpacked optimality of `roundDirected` -/

theorem roundDirected_opt_lo (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v))
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m) :
    ∀ q, Representable q → q ≤ v → hiEncloses? (toEVal (roundDirected s m e acc false)) q := by
  intro q hq hle
  rw [toEVal_roundDirected_acc, firstRoundedAcc_eq]
  exact opt_down s _ _ _ v (shOf_bracket s m e acc v hex hin)
    (shOf_norm s m e acc v hex hin hen) q hq hle

theorem roundDirected_opt_hi (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v))
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m) :
    ∀ q, Representable q → v ≤ q → loEncloses? (toEVal (roundDirected s m e acc true)) q := by
  intro q hq hle
  rw [toEVal_roundDirected_acc, firstRoundedAcc_eq]
  exact opt_up s _ _ _ v (shOf_bracket s m e acc v hex hin)
    (shOf_norm s m e acc v hex hin hen) q hq hle

/-! ### Packing preserves optimality (overflow included) -/

/-- Shape of an unpacked result: zero, or a finite with a canonical /
    overflowing-normal shape. -/
def Shaped (u : UnpackedFloat) : Prop :=
  (∃ z, u = .zero z) ∨
    ∃ s m e h, u = .finite s m e h ∧ (IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e)

theorem isRoundDown_pack (u : UnpackedFloat) (x : Rat) (hsh : Shaped u)
    (hlo : loEncloses? (toEVal u) x)
    (hopt : ∀ q, Representable q → q ≤ x → hiEncloses? (toEVal u) q) :
    IsRoundDown x (bitsToEVal (packDirected false u)) := by
  rcases hsh with ⟨z, rfl⟩ | ⟨s, m, e, h, rfl, hs⟩
  · rw [packDirected_zero, bitsToEVal_pack_zero]
    exact ⟨hlo, hopt⟩
  · rcases hs with hsub | hnorm | hov
    · rw [packDirected_eq_pack_of_canonical false s h (Or.inl hsub),
        bitsToEVal_pack_canonical s h (Or.inl hsub)]
      exact ⟨hlo, hopt⟩
    · rw [packDirected_eq_pack_of_canonical false s h (Or.inr hnorm),
        bitsToEVal_pack_canonical s h (Or.inr hnorm)]
      exact ⟨hlo, hopt⟩
    · refine ⟨loEncloses_packDirected_of_shaped s h (Or.inr (Or.inr hov)) x hlo, ?_⟩
      intro q hq hle
      rw [packDirected_eq_overflow false s h hov.1]
      cases s with
      | positive =>
        simp only [awayFromZero, Bool.false_eq_true, ↓reduceIte]
        rw [bitsToEVal_pack_maxFinite]
        exact le_maxVal_of_representable hq
      | negative =>
        exfalso
        have h1 : q ≤ -mag m e := by simpa [toEVal, hiEncloses?, signedVal] using hopt q hq hle
        have h2 : -mag m e < -maxVal := (Rat.neg_lt_neg_iff).mpr (maxVal_lt_of_overflow hov)
        exact Rat.lt_irrefl (rlt_of_lt_of_le (rlt_of_le_of_lt h1 h2)
          (neg_maxVal_le_of_representable hq))

theorem isRoundUp_pack (u : UnpackedFloat) (x : Rat) (hsh : Shaped u)
    (hhi : hiEncloses? (toEVal u) x)
    (hopt : ∀ q, Representable q → x ≤ q → loEncloses? (toEVal u) q) :
    IsRoundUp x (bitsToEVal (packDirected true u)) := by
  rcases hsh with ⟨z, rfl⟩ | ⟨s, m, e, h, rfl, hs⟩
  · rw [packDirected_zero, bitsToEVal_pack_zero]
    exact ⟨hhi, hopt⟩
  · rcases hs with hsub | hnorm | hov
    · rw [packDirected_eq_pack_of_canonical true s h (Or.inl hsub),
        bitsToEVal_pack_canonical s h (Or.inl hsub)]
      exact ⟨hhi, hopt⟩
    · rw [packDirected_eq_pack_of_canonical true s h (Or.inr hnorm),
        bitsToEVal_pack_canonical s h (Or.inr hnorm)]
      exact ⟨hhi, hopt⟩
    · refine ⟨hiEncloses_packDirected_of_shaped s h (Or.inr (Or.inr hov)) x hhi, ?_⟩
      intro q hq hle
      rw [packDirected_eq_overflow true s h hov.1]
      cases s with
      | negative =>
        simp only [awayFromZero, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [bitsToEVal_pack_maxFinite]
        have := neg_maxVal_le_of_representable hq
        simpa [loEncloses?, loEncloses, signedVal, maxVal] using this
      | positive =>
        exfalso
        have h1 : mag m e ≤ q := by simpa [toEVal, loEncloses?, signedVal] using hopt q hq hle
        exact Rat.lt_irrefl (rlt_of_lt_of_le (rlt_of_lt_of_le (maxVal_lt_of_overflow hov) h1)
          (le_maxVal_of_representable hq))

theorem shaped_roundDirected (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (up : Bool)
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m) :
    Shaped (roundDirected s m e acc up) := by
  rcases roundDirected_zero_or_shaped_acc s m e acc up
    (firstRoundedAcc_norm_of_enough s m e acc up hen) with h | ⟨m', e', h, heq, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, m', e', h, heq, hs⟩

/-- **Optimal directed rounding (down).** -/
theorem roundDirected_isRoundDown (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v))
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m) :
    IsRoundDown v (bitsToEVal (packDirected false (roundDirected s m e acc false))) :=
  isRoundDown_pack _ v (shaped_roundDirected s m e acc false hen)
    (roundDirected_lo_acc s m e acc v hex hin) (roundDirected_opt_lo s m e acc v hex hin hen)

/-- **Optimal directed rounding (up).** -/
theorem roundDirected_isRoundUp (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) (v : Rat)
    (hex : acc = .exact → v = signedVal s m e)
    (hin : ∀ o, acc = .inexact o → inexactMag m e (signedMag s v))
    (hen : acc = .exact ∨ e ≤ spec64.minExponent ∨ 2 ^ 52 ≤ m) :
    IsRoundUp v (bitsToEVal (packDirected true (roundDirected s m e acc true))) :=
  isRoundUp_pack _ v (shaped_roundDirected s m e acc true hen)
    (roundDirected_hi_acc s m e acc v hex hin) (roundDirected_opt_hi s m e acc v hex hin hen)

end Interval64Proofs.RoundOpt
