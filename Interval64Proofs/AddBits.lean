/-
Bits-level enclosure of directed addition, interval membership lift,
and exactness when the true sum is a representable binary64.
-/
import Interval64Proofs.PackFinite

namespace Interval64Proofs.AddBits

open Interval64.Spec
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Round
open Interval64Proofs.RoundDirected
open Interval64Proofs.Canonical
open Interval64Proofs.Pack
open Interval64Proofs.PackFinite
open Interval64Proofs.Add
open Float.Model
open Float.Model.UnpackedFloat

/-! ### `unpack` of a finite bit pattern is canonical -/

theorem exponentVec_trichotomy (v : BitVec spec64.exponentBits) :
    v = 0#_ ∨ v = -1#_ ∨
      (0 < v.toNat ∧ v.toNat < 2 ^ spec64.exponentBits - 1) := by
  have hlt : v.toNat < 2048 := by
    have := v.isLt
    rwa [exponentBits_pow] at this
  rcases Nat.eq_zero_or_pos v.toNat with h0 | hpos
  · left
    exact BitVec.eq_of_toNat_eq (by simp [h0])
  · by_cases h1 : v.toNat = 2047
    · right; left
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, exponentBits_pow, h1]
    · right; right
      refine ⟨hpos, ?_⟩
      have : 2 ^ spec64.exponentBits - 1 = 2047 := by rw [exponentBits_pow]
      rw [this]
      omega

theorem zero_ne_negOne_11 : (0#11 : BitVec 11) ≠ -1#11 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this

theorem unpack_of_inf_field {b : BitVec spec64.numBits}
    (hinf : unpackExponent b = -1#_) :
    UnpackedFloat.unpack spec64 b = .infinity (Sign.ofBitVec (unpackSign b)) ∨
      UnpackedFloat.unpack spec64 b = .notANumber := by
  by_cases hm : unpackMantissa b = 0#_
  · left
    simp [UnpackedFloat.unpack, hinf, hm]
  · right
    simp [UnpackedFloat.unpack, hinf, hm]

theorem unpack_of_subnormal {b : BitVec spec64.numBits}
    (hz : unpackExponent b = 0#_) (hmnz : unpackMantissa b ≠ 0#_) :
    UnpackedFloat.unpack spec64 b =
      .finite (Sign.ofBitVec (unpackSign b)) (unpackMantissa b).toNat
        (((unpackExponent b).toNat : Int) -
          (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) + 1)
        (by simpa [BitVec.toNat_pos, BitVec.pos_iff_ne_zero] using hmnz) := by
  have hne1 : unpackExponent b ≠ -1#_ := by
    intro h
    rw [hz] at h
    have ht := congrArg BitVec.toNat h
    simp [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, exponentBits_pow] at ht
  simp [UnpackedFloat.unpack, hne1, hz, hmnz, zero_ne_negOne_11]

theorem unpack_of_zero_field {b : BitVec spec64.numBits}
    (hz : unpackExponent b = 0#_) (hm0 : unpackMantissa b = 0#_) :
    UnpackedFloat.unpack spec64 b = .zero (Sign.ofBitVec (unpackSign b)) := by
  have hne1 : unpackExponent b ≠ -1#_ := by
    intro h
    rw [hz] at h
    have ht := congrArg BitVec.toNat h
    simp [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, exponentBits_pow] at ht
  simp [UnpackedFloat.unpack, hne1, hz, hm0, zero_ne_negOne_11]

theorem unpack_of_normal_field {b : BitVec spec64.numBits}
    (hne0 : unpackExponent b ≠ 0#_) (hne1 : unpackExponent b ≠ -1#_) :
    UnpackedFloat.unpack spec64 b =
      .finite (Sign.ofBitVec (unpackSign b)) (1#1 ++ unpackMantissa b).toNat
        (((unpackExponent b).toNat : Int) -
          (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit))
        (by simp) := by
  have hne2047 : unpackExponent b ≠ 2047#11 := by
    intro h
    apply hne1
    apply BitVec.eq_of_toNat_eq
    have h1 : (unpackExponent b).toNat = 2047 := by
      rw [h]
      simp [BitVec.toNat_ofNat]
    have h2 : (-1#spec64.exponentBits).toNat = 2047 := by
      rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      have hp : 2 ^ spec64.exponentBits = 2048 := exponentBits_pow
      rw [hp]
    rw [h1, h2]
  simp [UnpackedFloat.unpack, hne2047, hne0]

theorem unpack_finite_is_canonical {b : BitVec spec64.numBits} {s : Sign}
    {m : Nat} {e : Int} {h : 0 < m}
    (hu : UnpackedFloat.unpack spec64 b = .finite s m e h) :
    IsCanonicalFinite m e := by
  have htri := exponentVec_trichotomy (unpackExponent b)
  rcases htri with hz | hinf | ⟨hpos, hhi⟩
  · by_cases hm0 : unpackMantissa b = 0#_
    · have := unpack_of_zero_field hz hm0
      rw [this] at hu
      cases hu
    · have := unpack_of_subnormal hz hm0
      rw [this] at hu
      have hm : m = (unpackMantissa b).toNat := by
        cases hu; rfl
      have he : e = ((unpackExponent b).toNat : Int) -
          (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) + 1 := by
        cases hu; rfl
      refine Or.inl ⟨?_, ?_, ?_⟩
      · rw [he, hz]
        simp [exponentBits_spec64, exponentBias_spec64,
          mantissaBitsWithoutImplicit_spec64, minExponent_spec64]
      · rw [hm]
        exact Nat.pos_of_ne_zero (fun hmz =>
          hm0 (BitVec.eq_of_toNat_eq (by simp [hmz])))
      · rw [hm]
        have := (unpackMantissa b).isLt
        simpa [mantissaBitsWithoutImplicit_spec64] using this
  · have hon := unpack_of_inf_field hinf
    rcases hon with hin | hnan
    · rw [hin] at hu; cases hu
    · rw [hnan] at hu; cases hu
  · have hne0 : unpackExponent b ≠ 0#_ := by
      intro heq
      have := congrArg BitVec.toNat heq
      simp [BitVec.toNat_zero] at this
      exact Nat.ne_of_gt hpos this
    have hne1 : unpackExponent b ≠ -1#_ := by
      intro heq
      have := congrArg BitVec.toNat heq
      have ht : (unpackExponent b).toNat = 2 ^ spec64.exponentBits - 1 := by
        rw [heq, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      omega
    have := unpack_of_normal_field hne0 hne1
    rw [this] at hu
    have hm : m = (1#1 ++ unpackMantissa b).toNat := by
      cases hu; rfl
    have he : e = ((unpackExponent b).toNat : Int) -
        (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit) := by
      cases hu; rfl
    have hmant : m = 2 ^ 52 + (unpackMantissa b).toNat := by
      rw [hm]
      simp only [mantissaBitsWithoutImplicit_spec64]
      exact implicit_toNat _
    have hmv : (unpackMantissa b).toNat < 2 ^ 52 := by
      have := (unpackMantissa b).isLt
      simpa [mantissaBitsWithoutImplicit_spec64] using this
    have hlo : 2 ^ 52 ≤ m := by omega
    have hhi' : m < 2 ^ 53 := by
      have : (2 ^ 53 : Nat) = 2 ^ 52 + 2 ^ 52 := by decide
      omega
    have hle : spec64.minExponent ≤ e := by
      have heq : ((unpackExponent b).toNat : Int) ≥ 1 := by exact_mod_cast (Nat.succ_le_of_lt hpos)
      rw [he]
      simp [exponentBias_spec64, mantissaBitsWithoutImplicit_spec64, minExponent_spec64]
      omega
    have hlt : e < overflowExponent := by
      have hpow : 2 ^ spec64.exponentBits - 1 = 2047 := by rw [exponentBits_pow]
      have hlt2047 : (unpackExponent b).toNat < 2047 := by
        have := hhi
        rwa [hpow] at this
      have hbound : (unpackExponent b).toNat ≤ 2046 := Nat.le_of_lt_succ hlt2047
      rw [he]
      have hbias : (spec64.exponentBias + spec64.mantissaBitsWithoutImplicit : Int) = 1075 := by
        simp [exponentBias_spec64, mantissaBitsWithoutImplicit_spec64]
      have hov : overflowExponent = 972 := rfl
      have hcast : ((unpackExponent b).toNat : Int) ≤ (2046 : Int) :=
        Int.ofNat_le.mpr hbound
      omega
    exact Or.inr ⟨hle, hlt, hlo, hhi'⟩

theorem bitsToRat?_cases {a : UInt64} {qa : Rat} (ha : bitsToRat? a = some qa) :
    (∃ s, unpackBits a = .zero s ∧ qa = 0) ∨
      (∃ s m e h, unpackBits a = .finite s m e h ∧ qa = signedVal s m e ∧
        IsCanonicalFinite m e) := by
  cases hu : unpackBits a with
  | notANumber =>
    simp [bitsToRat?, hu, toRat?] at ha
  | infinity s =>
    simp [bitsToRat?, hu, toRat?] at ha
  | zero s =>
    refine Or.inl ⟨s, rfl, ?_⟩
    simp [bitsToRat?, hu, toRat?] at ha
    exact ha.symm
  | finite s m e h =>
    refine Or.inr ⟨s, m, e, h, rfl, ?_, ?_⟩
    · simp [bitsToRat?, hu, toRat?_finite] at ha
      exact ha.symm
    · simp [unpackBits] at hu
      exact unpack_finite_is_canonical hu


/-! ### Shape of `normalizeDirected` (exact path) -/

theorem normalizeDirected_zero_or_shaped (mant : Int) (e : Int) (z : Sign) (up : Bool) :
    (∃ s, normalizeDirected mant e z up = .zero s) ∨
      (∃ s m e' h, normalizeDirected mant e z up = .finite s m e' h ∧
        (IsSubnormal m e' ∨ IsNormal m e' ∨ IsOverflowNormal m e')) := by
  unfold normalizeDirected
  cases compare mant 0 with
  | eq =>
    exact Or.inl ⟨z, rfl⟩
  | lt =>
    exact (roundDirected_zero_or_shaped .negative (-mant).toNat e up).elim
      (fun ⟨s, hs⟩ => Or.inl ⟨s, hs⟩)
      (fun ⟨m, e', h, heq, hsh⟩ => Or.inr ⟨.negative, m, e', h, heq, hsh⟩)
  | gt =>
    exact (roundDirected_zero_or_shaped .positive mant.toNat e up).elim
      (fun ⟨s, hs⟩ => Or.inl ⟨s, hs⟩)
      (fun ⟨m, e', h, heq, hsh⟩ => Or.inr ⟨.positive, m, e', h, heq, hsh⟩)

theorem addU_zero_finite (s s₂ : Sign) (m : Nat) (e : Int) (h : 0 < m) (up : Bool) :
    addU (.zero s) (.finite s₂ m e h) up = .finite s₂ m e h :=
  rfl

theorem addU_finite_zero (s₁ s : Sign) (m : Nat) (e : Int) (h : 0 < m) (up : Bool) :
    addU (.finite s₁ m e h) (.zero s) up = .finite s₁ m e h :=
  rfl

theorem canonical_is_shaped {m : Nat} {e : Int} (hc : IsCanonicalFinite m e) :
    IsSubnormal m e ∨ IsNormal m e ∨ IsOverflowNormal m e :=
  hc.elim Or.inl (fun hn => Or.inr (Or.inl hn))

/-! ### Bits-level enclosure of directed add -/

theorem add_encloses_lo {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (addDown a b)) (qa + qb) := by
  simp only [addDown, Interval64.Spec.add]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [addU]
      split
      · exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, Rat.add_zero])
      · exact loEncloses_packDirected_zero_val _ _ _ (by simp [loEncloses?, loEncloses, Rat.add_zero])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2, addU_zero_finite]
      have := loEncloses_packDirected_shaped s2 h2 (canonical_is_shaped hc2)
      simpa [Rat.zero_add] using this
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2, addU_finite_zero]
      have := loEncloses_packDirected_shaped s1 h1 (canonical_is_shaped hc1)
      simpa [Rat.add_zero] using this
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2]
      have hlo := addU_finite_lo (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape := normalizeDirected_zero_or_shaped
        (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
          s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
        (min e1 e2) (cancelZero false) false
      have hadd :
          addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) false =
            normalizeDirected
              (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
              (min e1 e2) (cancelZero false) false :=
        rfl
      rw [hadd] at hlo ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨s, m, e, h, heq, hsh⟩
      · rw [heq]
        exact loEncloses_packDirected_zero_val _ _ _ (heq ▸ hlo)
      · rw [heq]
        exact loEncloses_packDirected_of_shaped s h hsh _ (heq ▸ hlo)

theorem add_encloses_hi {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    hiEncloses? (bitsToEVal (addUp a b)) (qa + qb) := by
  simp only [addUp, Interval64.Spec.add]
  rcases bitsToRat?_cases ha with hza | hfa
  · rcases hza with ⟨s1, hu1, rfl⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2]
      simp only [addU]
      split
      · exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, Rat.add_zero])
      · exact hiEncloses_packDirected_zero_val _ _ _ (by simp [hiEncloses?, hiEncloses, Rat.add_zero])
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2, addU_zero_finite]
      have := hiEncloses_packDirected_shaped s2 h2 (canonical_is_shaped hc2)
      simpa [Rat.zero_add] using this
  · rcases hfa with ⟨s1, m1, e1, h1, hu1, rfl, hc1⟩
    rcases bitsToRat?_cases hb with hzb | hfb
    · rcases hzb with ⟨s2, hu2, rfl⟩
      rw [hu1, hu2, addU_finite_zero]
      have := hiEncloses_packDirected_shaped s1 h1 (canonical_is_shaped hc1)
      simpa [Rat.add_zero] using this
    · rcases hfb with ⟨s2, m2, e2, h2, hu2, rfl, hc2⟩
      rw [hu1, hu2]
      have hhi := addU_finite_hi (s₁ := s1) (s₂ := s2) (e₁ := e1) (e₂ := e2) h1 h2
      have hshape := normalizeDirected_zero_or_shaped
        (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
          s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
        (min e1 e2) (cancelZero true) true
      have hadd :
          addU (.finite s1 m1 e1 h1) (.finite s2 m2 e2 h2) true =
            normalizeDirected
              (s1.apply (decreaseExponent m1 e1 (min e1 e2)).1 +
                s2.apply (decreaseExponent m2 e2 (min e1 e2)).1)
              (min e1 e2) (cancelZero true) true :=
        rfl
      rw [hadd] at hhi ⊢
      rcases hshape with ⟨z, heq⟩ | ⟨s, m, e, h, heq, hsh⟩
      · rw [heq]
        exact hiEncloses_packDirected_zero_val _ _ _ (heq ▸ hhi)
      · rw [heq]
        exact hiEncloses_packDirected_of_shaped s h hsh _ (heq ▸ hhi)

theorem add_encloses {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (addDown a b)) (qa + qb) ∧
    hiEncloses? (bitsToEVal (addUp a b)) (qa + qb) :=
  ⟨add_encloses_lo ha hb, add_encloses_hi ha hb⟩

/-! ### Interval membership -/

def Mem (x : Rat) (lo hi : UInt64) : Prop :=
  loEncloses? (bitsToEVal lo) x ∧ hiEncloses? (bitsToEVal hi) x

theorem add_mem {x y : Rat} {loX hiX loY hiY : UInt64}
    (hx : Mem x loX hiX) (hy : Mem y loY hiY)
    (hloX : ∃ qx, bitsToRat? loX = some qx)
    (hloY : ∃ qy, bitsToRat? loY = some qy)
    (hhiX : ∃ qx, bitsToRat? hiX = some qx)
    (hhiY : ∃ qy, bitsToRat? hiY = some qy) :
    Mem (x + y) (addDown loX loY) (addUp hiX hiY) := by
  rcases hloX with ⟨qx, hqx⟩
  rcases hloY with ⟨qy, hqy⟩
  rcases hhiX with ⟨rx, hrx⟩
  rcases hhiY with ⟨ry, hry⟩
  have hsumlo := add_encloses_lo hqx hqy
  have hsumhi := add_encloses_hi hrx hry
  have hxlo : loEncloses? (bitsToEVal loX) x := hx.1
  have hylo : loEncloses? (bitsToEVal loY) y := hy.1
  have hxhi : hiEncloses? (bitsToEVal hiX) x := hx.2
  have hyhi : hiEncloses? (bitsToEVal hiY) y := hy.2
  have hqx' := bitsToEVal_rat_of_bitsToRat? hqx
  have hqy' := bitsToEVal_rat_of_bitsToRat? hqy
  have hrx' := bitsToEVal_rat_of_bitsToRat? hrx
  have hry' := bitsToEVal_rat_of_bitsToRat? hry
  have hlex : qx ≤ x := by
    simp [loEncloses?, loEncloses, hqx'] at hxlo
    exact hxlo
  have hley : qy ≤ y := by
    simp [loEncloses?, loEncloses, hqy'] at hylo
    exact hylo
  have hgex : x ≤ rx := by
    simp [hiEncloses?, hiEncloses, hrx'] at hxhi
    exact hxhi
  have hgey : y ≤ ry := by
    simp [hiEncloses?, hiEncloses, hry'] at hyhi
    exact hyhi
  have hle : qx + qy ≤ x + y :=
    Rat.le_trans ((Rat.add_le_add_right (a := qx) (b := x) (c := qy)).mpr hlex)
      ((Rat.add_le_add_left (a := qy) (b := y) (c := x)).mpr hley)
  have hge : x + y ≤ rx + ry :=
    Rat.le_trans ((Rat.add_le_add_right (a := x) (b := rx) (c := y)).mpr hgex)
      ((Rat.add_le_add_left (a := y) (b := ry) (c := rx)).mpr hgey)
  exact ⟨loEncloses_trans hsumlo hle, hiEncloses_trans hsumhi hge⟩


/-! ### Exactness when the downward and upward results agree -/

/-- If directed add in both directions yields the same rational, it is the exact sum. -/
theorem add_exact_of_same {a b : UInt64} {qa qb q : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hd : bitsToRat? (addDown a b) = some q)
    (hu : bitsToRat? (addUp a b) = some q) :
    q = qa + qb := by
  have ⟨hlo, hhi⟩ := add_encloses ha hb
  have hd' := bitsToEVal_rat_of_bitsToRat? hd
  have hu' := bitsToEVal_rat_of_bitsToRat? hu
  have h1 : q ≤ qa + qb := by
    simp [loEncloses?, loEncloses, hd'] at hlo
    exact hlo
  have h2 : qa + qb ≤ q := by
    simp [hiEncloses?, hiEncloses, hu'] at hhi
    exact hhi
  exact Rat.le_antisymm h1 h2

/-! ### Rounding a already-canonical finite is the identity -/

theorem decreaseExponent_id (m : Nat) (e : Int) :
    decreaseExponent m e e = (m, e) := by
  simp only [decreaseExponent]
  have : (e - e).toNat = 0 := by simp
  simp [this, Nat.shiftLeft_zero]

theorem target_eq_of_normal {m : Nat} {e : Int} (hn : IsNormal m e) :
    spec64.targetExponent (totalExponent m e) = e := by
  have ⟨hle, _, hlo, hhi⟩ := hn
  have hlog := log2_eq_52 hlo hhi
  unfold Format.targetExponent totalExponent
  simp only [hlog, mantissaBits_spec64]
  have heq : ((52 : Nat) : Int) + 1 + e - ((53 : Nat) : Int) = e := by omega
  simp only [heq]
  exact Int.max_eq_left hle

theorem target_eq_of_subnormal {m : Nat} {e : Int} (hs : IsSubnormal m e) :
    spec64.targetExponent (totalExponent m e) = e := by
  have ⟨he, hm, hhi⟩ := hs
  have hlog : (m.log2 : Int) + 1 ≤ 52 := by
    have := log2_lt_52 hm hhi
    exact Int.ofNat_le.mpr (Nat.succ_le_of_lt this)
  unfold Format.targetExponent totalExponent
  simp [mantissaBits_spec64, he]
  apply Int.max_eq_right
  have : (m.log2 + 1 : Int) ≤ 52 := hlog
  omega

end Interval64Proofs.AddBits
