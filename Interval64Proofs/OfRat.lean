/-
`ofRatDown` / `ofRatUp` are optimal: the greatest (least) representable
binary64 below (above) a rational, with IEEE overflow. Consequences:
enclosure, exactness on representables, and a decidable `Representable`.
-/
import Interval64Proofs.RoundOpt
import Interval64Proofs.FloatBits

namespace Interval64Proofs.OfRat

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.RoundInexact
open Interval64Proofs.Pack
open Interval64Proofs.Grid
open Interval64Proofs.RoundOpt
open Float.Model
open Float.Model.UnpackedFloat

/-! ### Arithmetic facts about `ratExp` / `ratMant` -/

theorem ratAbs_pos {q : Rat} (hq : q ≠ 0) : 0 < ratAbs q := by
  unfold ratAbs
  split
  · rename_i h
    have := (Rat.neg_lt_neg_iff).mpr h
    simpa using this
  · rename_i h
    have h' : 0 ≤ q := Rat.not_lt.mp h
    exact Rat.lt_of_le_of_ne h' (Ne.symm hq)

theorem signedMag_ratSign (q : Rat) : signedMag (ratSign q) q = ratAbs q := by
  unfold ratSign ratAbs
  split <;> rfl

theorem signedVal_ratSign {q : Rat} {M : Nat} {E : Int} (h : ratAbs q = mag M E) :
    q = signedVal (ratSign q) M E := by
  unfold ratSign
  unfold ratAbs at h
  split
  · rename_i hlt
    rw [ite_eq_left hlt] at h
    simp only [signedVal]
    rw [← h, Rat.neg_neg]
  · rename_i hlt
    rw [ite_eq_right hlt] at h
    exact h

theorem floor_nonneg {Y : Rat} (h : 0 ≤ Y) : 0 ≤ Y.floor :=
  Rat.le_floor_iff.mpr (by simpa using h)

theorem natCast_toNat_floor {Y : Rat} (h : 0 ≤ Y) : ((Y.floor.toNat : Nat) : Rat) = (Y.floor : Rat) := by
  rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (floor_nonneg h)]

theorem scaled_nonneg {X : Rat} (hX : 0 < X) (E : Int) : 0 ≤ X / pow2 E := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.le_of_lt hX) (Rat.le_of_lt (Rat.inv_pos.mpr (pow2_pos E)))

theorem ratMant_le {X : Rat} (hX : 0 < X) :
    (ratMant X : Rat) ≤ X / pow2 (ratExp X) := by
  unfold ratMant
  rw [natCast_toNat_floor (scaled_nonneg hX _)]
  exact Rat.floor_le _

theorem lt_ratMant_succ {X : Rat} (hX : 0 < X) :
    X / pow2 (ratExp X) < ((ratMant X + 1 : Nat) : Rat) := by
  unfold ratMant
  have h := Rat.lt_floor_add_one (X / pow2 (ratExp X))
  have hc : (((X / pow2 (ratExp X)).floor.toNat + 1 : Nat) : Rat) =
      (((X / pow2 (ratExp X)).floor + 1 : Int) : Rat) := by
    rw [Rat.natCast_add, natCast_toNat_floor (scaled_nonneg hX _), Rat.intCast_add]
    rfl
  rw [hc]
  exact h

theorem mul_pow2_of_div {Y X : Rat} {E : Int} (h : Y = X / pow2 E) : X = Y * pow2 E := by
  rw [h, Rat.div_mul_cancel (pow2_ne_zero E)]

theorem mag_ratMant_le {X : Rat} (hX : 0 < X) : mag (ratMant X) (ratExp X) ≤ X := by
  unfold mag
  have := Rat.mul_le_mul_of_nonneg_right (ratMant_le hX) (pow2_nonneg (ratExp X))
  rwa [Rat.div_mul_cancel (pow2_ne_zero _)] at this

theorem lt_mag_ratMant_succ {X : Rat} (hX : 0 < X) : X < mag (ratMant X + 1) (ratExp X) := by
  unfold mag
  have := Rat.mul_lt_mul_of_pos_right (lt_ratMant_succ hX) (pow2_pos (ratExp X))
  rwa [Rat.div_mul_cancel (pow2_ne_zero _)] at this

theorem ratAcc_exact {X : Rat} (h : ratAcc X = .exact) : X = mag (ratMant X) (ratExp X) := by
  unfold ratAcc at h
  split at h
  · rename_i heq
    unfold mag
    exact mul_pow2_of_div heq
  · cases h

theorem ratAcc_inexact {X : Rat} (hX : 0 < X) {o : Ordering} (h : ratAcc X = .inexact o) :
    inexactMag (ratMant X) (ratExp X) X := by
  unfold ratAcc at h
  split at h
  · cases h
  · rename_i hne
    refine ⟨?_, lt_mag_ratMant_succ hX⟩
    have hlt : (ratMant X : Rat) < X / pow2 (ratExp X) := Rat.lt_of_le_of_ne (ratMant_le hX) hne
    unfold mag
    have := Rat.mul_lt_mul_of_pos_right hlt (pow2_pos (ratExp X))
    rwa [Rat.div_mul_cancel (pow2_ne_zero _)] at this

/-- `X ≥ 2^(log₂ num − log₂ den − 1)`. -/
theorem pow2_log_le {X : Rat} (hX : 0 < X) :
    pow2 ((X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 1) ≤ X := by
  have hnum : 0 < X.num := by
    have h1 : 0 ≤ X.num := Rat.num_nonneg.mpr (Rat.le_of_lt hX)
    have h2 : X.num ≠ 0 := fun h => by
      rw [Rat.num_eq_zero] at h
      rw [h] at hX
      exact Rat.lt_irrefl hX
    omega
  have hnn : ((X.num.natAbs : Nat) : Int) = X.num := Int.natAbs_of_nonneg (Int.le_of_lt hnum)
  have hn0 : X.num.natAbs ≠ 0 := by omega
  have hd0 : 0 < X.den := X.den_pos
  have hXeq : X = ((X.num.natAbs : Nat) : Rat) / ((X.den : Nat) : Rat) := by
    rw [← Rat.intCast_natCast X.num.natAbs, hnn]
    have := Rat.num_divInt_den X
    rw [Rat.divInt_eq_div] at this
    exact this.symm
  -- 2^a ≤ n and d < 2^(b+1)
  have ha : pow2 (X.num.natAbs.log2 : Int) ≤ ((X.num.natAbs : Nat) : Rat) := by
    rw [pow2_nat]
    have h' := Rat.natCast_le_natCast.mpr (Nat.log2_self_le hn0)
    simpa using h'
  have hb : ((X.den : Nat) : Rat) ≤ pow2 ((X.den.log2 : Int) + 1) := by
    have : ((X.den.log2 : Int) + 1) = ((X.den.log2 + 1 : Nat) : Int) := by omega
    rw [this, pow2_nat]
    have h' := Rat.natCast_le_natCast.mpr (Nat.le_of_lt (Nat.lt_log2_self (n := X.den)))
    simpa using h'
  have hdpos : (0 : Rat) < ((X.den : Nat) : Rat) := Rat.natCast_pos.mpr hd0
  have hsplit : pow2 ((X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 1) *
      pow2 ((X.den.log2 : Int) + 1) = pow2 (X.num.natAbs.log2 : Int) := by
    rw [← pow2_add]
    congr 1
    omega
  have hXd : X * ((X.den : Nat) : Rat) = ((X.num.natAbs : Nat) : Rat) := by
    have h1 : X * ((X.den : Nat) : Rat) =
        ((X.num.natAbs : Nat) : Rat) / ((X.den : Nat) : Rat) * ((X.den : Nat) : Rat) := by
      rw [← hXeq]
    rw [h1]
    exact Rat.div_mul_cancel (Rat.ne_of_gt hdpos)
  apply Rat.le_of_mul_le_mul_right _ hdpos
  rw [hXd]
  refine Rat.le_trans ?_ (hsplit ▸ ha)
  exact Rat.mul_le_mul_of_nonneg_left hb (pow2_nonneg _)

theorem ratExp_enough {X : Rat} (hX : 0 < X) :
    ratExp X ≤ spec64.minExponent ∨ 2 ^ 52 ≤ ratMant X := by
  by_cases h : ((X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 53) ≤ spec64.minExponent
  · left
    unfold ratExp
    exact Int.le_of_eq (Int.max_eq_left h)
  · right
    have hE : ratExp X = (X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 53 := by
      unfold ratExp
      exact Int.max_eq_right (Int.le_of_lt (Int.lt_of_not_ge h))
    -- 2^52 ≤ X / 2^E
    have hY : ((2 ^ 52 : Nat) : Rat) ≤ X / pow2 (ratExp X) := by
      apply Rat.le_of_mul_le_mul_right _ (pow2_pos (ratExp X))
      rw [Rat.div_mul_cancel (pow2_ne_zero _)]
      have : ((2 ^ 52 : Nat) : Rat) * pow2 (ratExp X) =
          pow2 ((X.num.natAbs.log2 : Int) - (X.den.log2 : Int) - 1) := by
        have hm := mag_two_pow 52 (ratExp X)
        unfold mag at hm
        rw [hm, hE]
        congr 1
        omega
      rw [this]
      exact pow2_log_le hX
    have hf : ((2 ^ 52 : Nat) : Int) ≤ (X / pow2 (ratExp X)).floor :=
      Rat.le_floor_iff.mpr hY
    unfold ratMant
    omega

/-! ### Optimality of `ofRatDown` / `ofRatUp` -/

theorem ofRatU_zero (up : Bool) : ofRatU 0 up = .zero .positive := rfl

theorem ofRatU_ne {q : Rat} (hq : q ≠ 0) (up : Bool) :
    ofRatU q up = roundDirected (ratSign q) (ratMant (ratAbs q)) (ratExp (ratAbs q))
      (ratAcc (ratAbs q)) up := by
  unfold ofRatU
  rw [ite_eq_right_iff.mpr (fun h => absurd h hq)]

theorem ofRat_hyps {q : Rat} (hq : q ≠ 0) :
    (ratAcc (ratAbs q) = .exact →
        q = signedVal (ratSign q) (ratMant (ratAbs q)) (ratExp (ratAbs q))) ∧
      (∀ o, ratAcc (ratAbs q) = .inexact o →
        inexactMag (ratMant (ratAbs q)) (ratExp (ratAbs q)) (signedMag (ratSign q) q)) ∧
      (ratAcc (ratAbs q) = .exact ∨ ratExp (ratAbs q) ≤ spec64.minExponent ∨
        2 ^ 52 ≤ ratMant (ratAbs q)) := by
  have hX := ratAbs_pos hq
  refine ⟨fun h => signedVal_ratSign (ratAcc_exact h), fun o h => ?_, Or.inr (ratExp_enough hX)⟩
  rw [signedMag_ratSign]
  exact ratAcc_inexact hX h

/-- **`ofRatDown q` is the greatest representable `≤ q`** (or `−∞` if none). -/
theorem ofRatDown_isRoundDown (q : Rat) : IsRoundDown q (bitsToEVal (ofRatDown q)) := by
  by_cases hq : q = 0
  · subst hq
    unfold ofRatDown
    rw [ofRatU_zero, packDirected_zero, bitsToEVal_pack_zero]
    exact isRoundDown_self 0
  · unfold ofRatDown
    rw [ofRatU_ne hq]
    have ⟨hex, hin, hen⟩ := ofRat_hyps hq
    exact roundDirected_isRoundDown _ _ _ _ q hex hin hen

/-- **`ofRatUp q` is the least representable `≥ q`** (or `+∞` if none). -/
theorem ofRatUp_isRoundUp (q : Rat) : IsRoundUp q (bitsToEVal (ofRatUp q)) := by
  by_cases hq : q = 0
  · subst hq
    unfold ofRatUp
    rw [ofRatU_zero, packDirected_zero, bitsToEVal_pack_zero]
    exact isRoundUp_self 0
  · unfold ofRatUp
    rw [ofRatU_ne hq]
    have ⟨hex, hin, hen⟩ := ofRat_hyps hq
    exact roundDirected_isRoundUp _ _ _ _ q hex hin hen

/-! ### Consequences -/

theorem eval_of_isRoundDown {x : Rat} {r : Option EVal} (h : IsRoundDown x r) :
    ∃ ev, r = some ev := by
  rcases h with ⟨hl, _⟩
  cases r with
  | none => exact hl.elim
  | some ev => exact ⟨ev, rfl⟩

theorem eval_of_isRoundUp {x : Rat} {r : Option EVal} (h : IsRoundUp x r) :
    ∃ ev, r = some ev := by
  rcases h with ⟨hl, _⟩
  cases r with
  | none => exact hl.elim
  | some ev => exact ⟨ev, rfl⟩

/-- If `x` is representable, a tight lower bound of `x` is `x` itself. -/
theorem isRoundDown_eq_of_representable {x : Rat} {r : Option EVal} (h : IsRoundDown x r)
    (hx : Representable x) : r = some (.rat x) := by
  rcases h with ⟨hl, ho⟩
  have hh := ho x hx Rat.le_refl
  cases r with
  | none => exact hl.elim
  | some ev =>
    cases ev with
    | negInf => exact hh.elim
    | posInf => exact hl.elim
    | rat r => rw [Rat.le_antisymm hl hh]

theorem isRoundUp_eq_of_representable {x : Rat} {r : Option EVal} (h : IsRoundUp x r)
    (hx : Representable x) : r = some (.rat x) := by
  rcases h with ⟨hl, ho⟩
  have hh := ho x hx Rat.le_refl
  cases r with
  | none => exact hl.elim
  | some ev =>
    cases ev with
    | posInf => exact hh.elim
    | negInf => exact hl.elim
    | rat r => rw [Rat.le_antisymm hh hl]

/-- Enclosure: `ofRatDown q ≤ q ≤ ofRatUp q`. -/
theorem ofRat_encloses (q : Rat) :
    loEncloses? (bitsToEVal (ofRatDown q)) q ∧ hiEncloses? (bitsToEVal (ofRatUp q)) q :=
  ⟨(ofRatDown_isRoundDown q).1, (ofRatUp_isRoundUp q).1⟩

/-- Exactness: a representable `q` rounds to itself in both directions. -/
theorem ofRat_exact {q : Rat} (hq : Representable q) :
    bitsToEVal (ofRatDown q) = some (.rat q) ∧ bitsToEVal (ofRatUp q) = some (.rat q) :=
  ⟨isRoundDown_eq_of_representable (ofRatDown_isRoundDown q) hq,
    isRoundUp_eq_of_representable (ofRatUp_isRoundUp q) hq⟩

theorem bitsToRat?_of_bitsToEVal {b : UInt64} {q : Rat} (h : bitsToEVal b = some (.rat q)) :
    bitsToRat? b = some q := by
  rw [bitsToRat?_eq_bitsToEVal, h]

/-- `Representable q ↔ value(ofRatDown q) = q`. -/
theorem representable_iff_ofRatDown (q : Rat) :
    Representable q ↔ bitsToRat? (ofRatDown q) = some q :=
  ⟨fun h => bitsToRat?_of_bitsToEVal (ofRat_exact h).1, fun h => ⟨_, h⟩⟩

theorem representable_iff_ofRatUp (q : Rat) :
    Representable q ↔ bitsToRat? (ofRatUp q) = some q :=
  ⟨fun h => bitsToRat?_of_bitsToEVal (ofRat_exact h).2, fun h => ⟨_, h⟩⟩

theorem isRepresentable_iff (q : Rat) : isRepresentable q = true ↔ Representable q := by
  rw [representable_iff_ofRatDown]
  simp [isRepresentable]

instance : DecidablePred Representable :=
  fun q => decidable_of_iff _ (isRepresentable_iff q)

/-- Optimality (down), user form: every finite float `v ≤ q` is `≤ ofRatDown q`,
    and `ofRatDown q` is then finite. -/
theorem ofRatDown_greatest {q v : Rat} {b : UInt64} (hb : bitsToRat? b = some v)
    (hv : v ≤ q) : ∃ r, bitsToRat? (ofRatDown q) = some r ∧ v ≤ r ∧ r ≤ q := by
  have ⟨hl, ho⟩ := ofRatDown_isRoundDown q
  have hh := ho v ⟨b, hb⟩ hv
  cases h : bitsToEVal (ofRatDown q) with
  | none => rw [h] at hl; exact hl.elim
  | some ev =>
    rw [h] at hl hh
    cases ev with
    | negInf => exact hh.elim
    | posInf => exact hl.elim
    | rat r => exact ⟨r, bitsToRat?_of_bitsToEVal h, hh, hl⟩

theorem ofRatUp_least {q v : Rat} {b : UInt64} (hb : bitsToRat? b = some v)
    (hv : q ≤ v) : ∃ r, bitsToRat? (ofRatUp q) = some r ∧ q ≤ r ∧ r ≤ v := by
  have ⟨hl, ho⟩ := ofRatUp_isRoundUp q
  have hh := ho v ⟨b, hb⟩ hv
  cases h : bitsToEVal (ofRatUp q) with
  | none => rw [h] at hl; exact hl.elim
  | some ev =>
    rw [h] at hl hh
    cases ev with
    | posInf => exact hh.elim
    | negInf => exact hl.elim
    | rat r => exact ⟨r, bitsToRat?_of_bitsToEVal h, hl, hh⟩

/-- `ofRatDown q = −∞` exactly when no finite float is `≤ q`. -/
theorem ofRatDown_negInf_iff (q : Rat) :
    bitsToEVal (ofRatDown q) = some .negInf ↔ ∀ v, Representable v → q < v := by
  have ⟨hl, ho⟩ := ofRatDown_isRoundDown q
  constructor
  · intro h v hv
    apply Rat.not_le.mp
    intro hle
    have := ho v hv hle
    rw [h] at this
    exact this
  · intro hall
    cases h : bitsToEVal (ofRatDown q) with
    | none => rw [h] at hl; exact hl.elim
    | some ev =>
      rw [h] at hl
      cases ev with
      | negInf => rfl
      | posInf => exact hl.elim
      | rat r =>
        exact absurd hl (Rat.not_le.mpr (hall r (representable_of_bitsToEVal h)))

theorem ofRatUp_posInf_iff (q : Rat) :
    bitsToEVal (ofRatUp q) = some .posInf ↔ ∀ v, Representable v → v < q := by
  have ⟨hl, ho⟩ := ofRatUp_isRoundUp q
  constructor
  · intro h v hv
    apply Rat.not_le.mp
    intro hle
    have := ho v hv hle
    rw [h] at this
    exact this
  · intro hall
    cases h : bitsToEVal (ofRatUp q) with
    | none => rw [h] at hl; exact hl.elim
    | some ev =>
      rw [h] at hl
      cases ev with
      | posInf => rfl
      | negInf => exact hl.elim
      | rat r =>
        exact absurd hl (Rat.not_le.mpr (hall r (representable_of_bitsToEVal h)))

/-! ### `Interval64.ofRat` -/

open Interval64
open Interval64Proofs.FloatBits
open Interval64Proofs.AddBits

theorem bitsToEVal_ofBits_of_some {b : UInt64} {r : Option EVal} (hr : bitsToEVal b = r)
    (hs : ∃ ev, r = some ev) : bitsToEVal (Float.ofBits b).toBits = r := by
  rcases hs with ⟨ev, rfl⟩
  exact bitsToEVal_toBits_ofBits hr

theorem ofRat_lo_eval (q : Rat) :
    bitsToEVal (ofRat q).lo.toBits = bitsToEVal (ofRatDown q) :=
  bitsToEVal_ofBits_of_some rfl (eval_of_isRoundDown (ofRatDown_isRoundDown q))

theorem ofRat_hi_eval (q : Rat) :
    bitsToEVal (ofRat q).hi.toBits = bitsToEVal (ofRatUp q) :=
  bitsToEVal_ofBits_of_some rfl (eval_of_isRoundUp (ofRatUp_isRoundUp q))

/-- **Enclosure:** `q ∈ ofRat q`. -/
theorem memIv_ofRat (q : Rat) : MemIv q (ofRat q) := by
  unfold MemIv Mem
  rw [ofRat_lo_eval, ofRat_hi_eval]
  exact ofRat_encloses q

/-- **Exactness:** a representable `q` gives the point interval `[q, q]`. -/
theorem ofRat_exact_iv {q : Rat} (hq : Representable q) :
    bitsToRat? (ofRat q).lo.toBits = some q ∧ bitsToRat? (ofRat q).hi.toBits = some q := by
  rw [bitsToRat?_eq_bitsToEVal, bitsToRat?_eq_bitsToEVal, ofRat_lo_eval, ofRat_hi_eval,
    (ofRat_exact hq).1, (ofRat_exact hq).2]
  exact ⟨rfl, rfl⟩

/-- **Tightness:** `ofRat q`'s endpoints are the tight rounding of `q`. -/
theorem ofRat_tight (q : Rat) :
    IsRoundDown q (bitsToEVal (ofRat q).lo.toBits) ∧
      IsRoundUp q (bitsToEVal (ofRat q).hi.toBits) := by
  rw [ofRat_lo_eval, ofRat_hi_eval]
  exact ⟨ofRatDown_isRoundDown q, ofRatUp_isRoundUp q⟩

theorem ofRatInterval_lo_eval (lo hi : Rat) :
    bitsToEVal (ofRatInterval lo hi).lo.toBits = bitsToEVal (ofRatDown lo) :=
  bitsToEVal_ofBits_of_some rfl (eval_of_isRoundDown (ofRatDown_isRoundDown lo))

theorem ofRatInterval_hi_eval (lo hi : Rat) :
    bitsToEVal (ofRatInterval lo hi).hi.toBits = bitsToEVal (ofRatUp hi) :=
  bitsToEVal_ofBits_of_some rfl (eval_of_isRoundUp (ofRatUp_isRoundUp hi))

/-- Every `x ∈ [lo, hi]` lies in `ofRatInterval lo hi`. -/
theorem memIv_ofRatInterval {lo hi x : Rat} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    MemIv x (ofRatInterval lo hi) := by
  unfold MemIv Mem
  rw [ofRatInterval_lo_eval, ofRatInterval_hi_eval]
  exact ⟨Interval64Proofs.PackFinite.loEncloses_trans (ofRat_encloses lo).1 hlo,
    Interval64Proofs.PackFinite.hiEncloses_trans (ofRat_encloses hi).2 hhi⟩

end Interval64Proofs.OfRat
