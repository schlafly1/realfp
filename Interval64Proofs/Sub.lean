/-
Directed subtraction is addition of the IEEE negation. Scalar enclosure
and exactness therefore reduce to the corresponding add theorems;
`sub_mem_iv` matches `Interval64.sub` (`subDown` on `lo`/`hi` swapped).
-/
import Interval64Proofs.ExactAdd
import Interval64Proofs.IntervalMem

namespace Interval64Proofs.Sub

open Interval64
open Interval64.Spec
open Interval64.Directed
open Interval64Proofs.Pow2
open Interval64Proofs.Value
open Interval64Proofs.Canonical
open Interval64Proofs.PackFinite
open Interval64Proofs.Pack
open Interval64Proofs.AddBits
open Interval64Proofs.ExactAdd
open Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem
open Float.Model
open Float.Model.UnpackedFloat

def negEVal : EVal → EVal
  | .negInf => .posInf
  | .posInf => .negInf
  | .rat q => .rat (-q)

def negBits (b : UInt64) : UInt64 :=
  packBits (unpackBits b).neg

theorem signedVal_neg_sign (s : Sign) (m : Nat) (e : Int) :
    signedVal (-s) m e = -signedVal s m e := by
  cases s with
  | positive => rfl
  | negative =>
    simp only [signedVal, Neg.neg]
    exact (Rat.neg_neg (mag m e)).symm

theorem unpackBits_negBits {b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    unpackBits (negBits b) = (unpackBits b).neg := by
  simp only [negBits]
  cases hu : unpackBits b with
  | notANumber =>
    simp [bitsToEVal, hu] at h
  | infinity s =>
    rw [UnpackedFloat.neg, unpackBits_inf]
  | zero s =>
    rw [UnpackedFloat.neg, unpackBits_zero]
  | finite s m e hm =>
    have hc : IsCanonicalFinite m e := by
      simp [unpackBits] at hu
      exact unpack_finite_is_canonical hu
    rw [UnpackedFloat.neg]
    cases hc with
    | inl hs => exact unpackBits_pack_subnormal (-s) hm hs
    | inr hn => exact unpackBits_pack_normal (-s) hm hn

theorem bitsToEVal_negBits {b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    bitsToEVal (negBits b) = some (negEVal ev) := by
  have hu := unpackBits_negBits h
  simp only [bitsToEVal] at h ⊢
  rw [hu]
  cases hv : unpackBits b with
  | notANumber =>
    rw [hv] at h; simp [toEVal] at h
  | infinity s =>
    rw [hv] at h
    cases s with
    | negative =>
      simp [UnpackedFloat.neg, toEVal, negEVal] at h ⊢
      cases h; rfl
    | positive =>
      simp [UnpackedFloat.neg, toEVal, negEVal] at h ⊢
      cases h; rfl
  | zero s =>
    rw [hv] at h
    simp [UnpackedFloat.neg, toEVal, negEVal] at h ⊢
    cases h; rfl
  | finite s m e hm =>
    rw [hv] at h
    simp [UnpackedFloat.neg, toEVal, negEVal, signedVal_neg_sign] at h ⊢
    cases h; rfl

theorem bitsToRat?_negBits {b : UInt64} {q : Rat}
    (h : bitsToRat? b = some q) :
    bitsToRat? (negBits b) = some (-q) := by
  have hev := bitsToEVal_rat_of_bitsToRat? h
  have := bitsToEVal_negBits hev
  exact bitsToRat?_of_ratEVal (by simp [this, negEVal])

theorem sub_eq_add_neg {a b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) (up : Bool) :
    Spec.sub a b up = Spec.add a (negBits b) up := by
  have hu := unpackBits_negBits h
  simp only [Spec.sub, Spec.add, hu]

theorem subDown_eq_addDown_neg {a b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    Spec.subDown a b = Spec.addDown a (negBits b) :=
  sub_eq_add_neg h false

theorem subUp_eq_addUp_neg {a b : UInt64} {ev : EVal}
    (h : bitsToEVal b = some ev) :
    Spec.subUp a b = Spec.addUp a (negBits b) :=
  sub_eq_add_neg h true

theorem sub_encloses_lo {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (Spec.subDown a b)) (qa - qb) := by
  have hev := bitsToEVal_rat_of_bitsToRat? hb
  rw [subDown_eq_addDown_neg hev, Rat.sub_eq_add_neg]
  exact add_encloses_lo ha (bitsToRat?_negBits hb)

theorem sub_encloses_hi {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    hiEncloses? (bitsToEVal (Spec.subUp a b)) (qa - qb) := by
  have hev := bitsToEVal_rat_of_bitsToRat? hb
  rw [subUp_eq_addUp_neg hev, Rat.sub_eq_add_neg]
  exact add_encloses_hi ha (bitsToRat?_negBits hb)

theorem sub_encloses {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb) :
    loEncloses? (bitsToEVal (Spec.subDown a b)) (qa - qb) ∧
    hiEncloses? (bitsToEVal (Spec.subUp a b)) (qa - qb) :=
  ⟨sub_encloses_lo ha hb, sub_encloses_hi ha hb⟩

/-- If `qa - qb` is a finite binary64 value, both directed results have
    that value. -/
theorem sub_exact {a b : UInt64} {qa qb : Rat}
    (ha : bitsToRat? a = some qa) (hb : bitsToRat? b = some qb)
    (hrep : ∃ c, bitsToRat? c = some (qa - qb)) :
    bitsToRat? (Spec.subDown a b) = some (qa - qb) ∧
    bitsToRat? (Spec.subUp a b) = some (qa - qb) := by
  have hev := bitsToEVal_rat_of_bitsToRat? hb
  have hrep' : ∃ c, bitsToRat? c = some (qa + -qb) := by
    rw [← Rat.sub_eq_add_neg]
    exact hrep
  have ⟨hd, hu⟩ := add_exact ha (bitsToRat?_negBits hb) hrep'
  rw [subDown_eq_addDown_neg hev, subUp_eq_addUp_neg hev, Rat.sub_eq_add_neg]
  exact ⟨hd, hu⟩

theorem sub_exact_int {a b : UInt64} {na nb : Int}
    (ha : bitsToRat? a = some (na : Rat))
    (hb : bitsToRat? b = some (nb : Rat))
    (hna : na.natAbs ≤ 2 ^ 53)
    (hnb : nb.natAbs ≤ 2 ^ 53)
    (hsum : (na - nb).natAbs ≤ 2 ^ 53) :
    bitsToRat? (Spec.subDown a b) = some ((na - nb : Int) : Rat) ∧
    bitsToRat? (Spec.subUp a b) = some ((na - nb : Int) : Rat) := by
  have hneg : (-nb).natAbs ≤ 2 ^ 53 := by
    simpa [Int.natAbs_neg] using hnb
  have hsum' : (na + -nb).natAbs ≤ 2 ^ 53 := by
    simpa [Int.sub_eq_add_neg] using hsum
  have hb' : bitsToRat? (negBits b) = some ((-nb : Int) : Rat) := by
    rw [bitsToRat?_negBits hb, Rat.intCast_neg]
  have ⟨hd, hu⟩ := add_exact_int ha hb' hna hneg hsum'
  have hev := bitsToEVal_rat_of_bitsToRat? hb
  have hcast : ((na - nb : Int) : Rat) = ((na + -nb : Int) : Rat) := by
    rw [Int.sub_eq_add_neg]
  rw [subDown_eq_addDown_neg hev, subUp_eq_addUp_neg hev, hcast]
  exact ⟨hd, hu⟩

/-! ### `MemIv` for `Interval64.sub` -/

theorem loEncloses_negBits {b : UInt64} {y : Rat}
    (h : hiEncloses? (bitsToEVal b) y) :
    loEncloses? (bitsToEVal (negBits b)) (-y) := by
  rcases bitsToEVal_some_of_hiEncloses h with ⟨ev, hev⟩
  have hneg := bitsToEVal_negBits hev
  cases ev with
  | negInf =>
    simp [hiEncloses?, hiEncloses, hev] at h
  | posInf =>
    simp [loEncloses?, loEncloses, hneg, negEVal]
  | rat q =>
    simp [hiEncloses?, hiEncloses, hev] at h
    simp [loEncloses?, loEncloses, hneg, negEVal]
    exact h

theorem hiEncloses_negBits {b : UInt64} {y : Rat}
    (h : loEncloses? (bitsToEVal b) y) :
    hiEncloses? (bitsToEVal (negBits b)) (-y) := by
  rcases bitsToEVal_some_of_loEncloses h with ⟨ev, hev⟩
  have hneg := bitsToEVal_negBits hev
  cases ev with
  | posInf =>
    simp [loEncloses?, loEncloses, hev] at h
  | negInf =>
    simp [hiEncloses?, hiEncloses, hneg, negEVal]
  | rat q =>
    simp [loEncloses?, loEncloses, hev] at h
    simp [hiEncloses?, hiEncloses, hneg, negEVal]
    exact h

theorem subDown_toBits (a b : Float) :
    (Directed.subDown a b).toBits =
      packBits (unpackBits (Spec.subDown a.toBits b.toBits)) := by
  simp only [Directed.subDown, subDownSpec, toBits_ofBits]

theorem subUp_toBits (a b : Float) :
    (Directed.subUp a b).toBits =
      packBits (unpackBits (Spec.subUp a.toBits b.toBits)) := by
  simp only [Directed.subUp, subUpSpec, toBits_ofBits]

theorem sub_eq_directed {X Y : Interval64} (h : anyNan X Y = false) :
    X - Y = ⟨Directed.subDown X.lo Y.hi, Directed.subUp X.hi Y.lo⟩ := by
  change Interval64.sub X Y = _
  unfold Interval64.sub
  rw [h]
  rfl

theorem not_memIv_invalid (x : Rat) : ¬ MemIv x invalid := by
  intro hx
  have hlo := not_isNaN_of_MemIv_lo hx
  have : invalid.lo.isNaN = true := rfl
  simp [this] at hlo

theorem subDown_loEncloses {x y : Rat} {loX hiY : UInt64}
    (hx : loEncloses? (bitsToEVal loX) x)
    (hy : hiEncloses? (bitsToEVal hiY) y) :
    loEncloses? (bitsToEVal (Spec.subDown loX hiY)) (x - y) := by
  rcases bitsToEVal_some_of_hiEncloses hy with ⟨ev, hev⟩
  have hneg := loEncloses_negBits hy
  have hadd := addDown_loEncloses hx hneg
  rw [subDown_eq_addDown_neg hev, Rat.sub_eq_add_neg]
  exact hadd

theorem subUp_hiEncloses {x y : Rat} {hiX loY : UInt64}
    (hx : hiEncloses? (bitsToEVal hiX) x)
    (hy : loEncloses? (bitsToEVal loY) y) :
    hiEncloses? (bitsToEVal (Spec.subUp hiX loY)) (x - y) := by
  rcases bitsToEVal_some_of_loEncloses hy with ⟨ev, hev⟩
  have hneg := hiEncloses_negBits hy
  have hadd := addUp_hiEncloses hx hneg
  rw [subUp_eq_addUp_neg hev, Rat.sub_eq_add_neg]
  exact hadd

theorem sub_mem_iv {x y : Rat} {X Y : Interval64}
    (hx : MemIv x X) (hy : MemIv y Y) : MemIv (x - y) (X - Y) := by
  have hnan : anyNan X Y = false := anyNan_eq_false hx hy
  have hsub := sub_eq_directed hnan
  have hlo := subDown_loEncloses hx.1 hy.2
  have hhi := subUp_hiEncloses hx.2 hy.1
  rw [hsub]
  constructor
  · rw [subDown_toBits]
    rcases bitsToEVal_some_of_loEncloses hlo with ⟨evl, hel⟩
    rw [bitsToEVal_pack_unpack_of_some hel, ← hel]
    exact hlo
  · rw [subUp_toBits]
    rcases bitsToEVal_some_of_hiEncloses hhi with ⟨evh, heh⟩
    rw [bitsToEVal_pack_unpack_of_some heh, ← heh]
    exact hhi

end Interval64Proofs.Sub
