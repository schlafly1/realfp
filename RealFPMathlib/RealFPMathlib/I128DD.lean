/-
Interval128 proofs, part 2: the double-double kernels are one-sided.

For each kernel `k` returning `⟨hi, lo⟩`: if both returned words are finite
with values `H`, `L`, then `H + L` is a lower (`*Lo`) / upper (`*Hi`) bound of
the exact real result computed from the input words. The round-to-nearest
approximations inside the kernels are arbitrary floats here: only the
directed error terms are used, each through an exact real identity.
-/
import RealFPMathlib.I128Prims

open Interval64 Interval64.Directed
open Interval128 Interval128.DD

namespace RealFP.I128

/-- The pair `d` is finite with exact value `v`. -/
def DDv (d : DD) (v : ℝ) : Prop := ∃ h l, Fv d.hi h ∧ Fv d.lo l ∧ h + l = v

theorem addLo_le {ah al bh bl : Float} {H L : ℝ} (hH : Fv (addLo ah al bh bl).hi H)
    (hL : Fv (addLo ah al bh bl).lo L) :
    ∃ a1 a2 b1 b2, Fv ah a1 ∧ Fv al a2 ∧ Fv bh b1 ∧ Fv bl b2 ∧
      H + L ≤ a1 + a2 + (b1 + b2) := by
  dsimp only [addLo] at hH hL
  obtain ⟨v1, ve3, h1, he3, i1⟩ := addDown_fin hL
  obtain ⟨vs2, vs3, hs2, hs3, i2⟩ := subDown_fin h1
  have := fv_unique hs3 hH; subst this
  obtain ⟨vg, vf, hg, hf, i3⟩ := addDown_fin he3
  obtain ⟨v4, ve2, h4, he2, i4⟩ := addDown_fin hg
  obtain ⟨vs, vs2', hs, hs2', i5⟩ := subDown_fin h4
  have := fv_unique hs2' hs2; subst this
  obtain ⟨ve, vt, he, ht, i6⟩ := addDown_fin he2
  obtain ⟨v7, v8, h7, h8, i7⟩ := addDown_fin hf
  obtain ⟨a2, v9, ha2, h9, i8⟩ := subDown_fin h7
  obtain ⟨vt', vcc, ht', hcc, i9⟩ := subUp_fin h9
  have := fv_unique ht' ht; subst this
  obtain ⟨b2, vcc', hb2, hcc', i10⟩ := subDown_fin h8
  have := fv_unique hcc' hcc; subst this
  obtain ⟨v11, v12, h11, h12, i11⟩ := addDown_fin he
  obtain ⟨a1, v13, ha1, h13, i12⟩ := subDown_fin h11
  obtain ⟨vs', vbb, hs', hbb, i13⟩ := subUp_fin h13
  have := fv_unique hs' hs; subst this
  obtain ⟨b1, vbb', hb1, hbb', i14⟩ := subDown_fin h12
  have := fv_unique hbb' hbb; subst this
  exact ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, by linarith⟩

theorem addHi_ge {ah al bh bl : Float} {H L : ℝ} (hH : Fv (addHi ah al bh bl).hi H)
    (hL : Fv (addHi ah al bh bl).lo L) :
    ∃ a1 a2 b1 b2, Fv ah a1 ∧ Fv al a2 ∧ Fv bh b1 ∧ Fv bl b2 ∧
      a1 + a2 + (b1 + b2) ≤ H + L := by
  dsimp only [addHi] at hH hL
  obtain ⟨v1, ve3, h1, he3, i1⟩ := addUp_fin hL
  obtain ⟨vs2, vs3, hs2, hs3, i2⟩ := subUp_fin h1
  have := fv_unique hs3 hH; subst this
  obtain ⟨vg, vf, hg, hf, i3⟩ := addUp_fin he3
  obtain ⟨v4, ve2, h4, he2, i4⟩ := addUp_fin hg
  obtain ⟨vs, vs2', hs, hs2', i5⟩ := subUp_fin h4
  have := fv_unique hs2' hs2; subst this
  obtain ⟨ve, vt, he, ht, i6⟩ := addUp_fin he2
  obtain ⟨v7, v8, h7, h8, i7⟩ := addUp_fin hf
  obtain ⟨a2, v9, ha2, h9, i8⟩ := subUp_fin h7
  obtain ⟨vt', vcc, ht', hcc, i9⟩ := subDown_fin h9
  have := fv_unique ht' ht; subst this
  obtain ⟨b2, vcc', hb2, hcc', i10⟩ := subUp_fin h8
  have := fv_unique hcc' hcc; subst this
  obtain ⟨v11, v12, h11, h12, i11⟩ := addUp_fin he
  obtain ⟨a1, v13, ha1, h13, i12⟩ := subUp_fin h11
  obtain ⟨vs', vbb, hs', hbb, i13⟩ := subDown_fin h13
  have := fv_unique hs' hs; subst this
  obtain ⟨b1, vbb', hb1, hbb', i14⟩ := subUp_fin h12
  have := fv_unique hbb' hbb; subst this
  exact ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, by linarith⟩

theorem mulLo_le {ah al bh bl : Float} {H L : ℝ} (hH : Fv (mulLo ah al bh bl).hi H)
    (hL : Fv (mulLo ah al bh bl).lo L) :
    ∃ a1 a2 b1 b2, Fv ah a1 ∧ Fv al a2 ∧ Fv bh b1 ∧ Fv bl b2 ∧
      H + L ≤ (a1 + a2) * (b1 + b2) := by
  dsimp only [mulLo] at hH hL
  obtain ⟨v1, ve2, h1, he2, i1⟩ := addDown_fin hL
  obtain ⟨vp, vs, hp, hs, i2⟩ := subDown_fin h1
  have := fv_unique hs hH; subst this
  obtain ⟨ve, vc, he, hc, i3⟩ := addDown_fin he2
  obtain ⟨a1, b1, vq, ha1, hb1, hq, i4⟩ := fmaDown_fin he
  have hq' := fv_of_neg hq
  have := fv_unique hq' hp; subst this
  obtain ⟨v5, v6, h5, h6, i5⟩ := addDown_fin hc
  obtain ⟨v7, v8, h7, h8, i6⟩ := addDown_fin h5
  obtain ⟨a1', b2, ha1', hb2, i7⟩ := mulDown_fin h7
  have := fv_unique ha1' ha1; subst this
  obtain ⟨a2, b1', ha2, hb1', i8⟩ := mulDown_fin h8
  have := fv_unique hb1' hb1; subst this
  obtain ⟨a2', b2', ha2', hb2', i9⟩ := mulDown_fin h6
  have := fv_unique ha2' ha2; subst this
  have := fv_unique hb2' hb2; subst this
  exact ⟨a1', a2', b1', b2', ha1, ha2, hb1, hb2, by nlinarith⟩

theorem mulHi_ge {ah al bh bl : Float} {H L : ℝ} (hH : Fv (mulHi ah al bh bl).hi H)
    (hL : Fv (mulHi ah al bh bl).lo L) :
    ∃ a1 a2 b1 b2, Fv ah a1 ∧ Fv al a2 ∧ Fv bh b1 ∧ Fv bl b2 ∧
      (a1 + a2) * (b1 + b2) ≤ H + L := by
  dsimp only [mulHi] at hH hL
  obtain ⟨v1, ve2, h1, he2, i1⟩ := addUp_fin hL
  obtain ⟨vp, vs, hp, hs, i2⟩ := subUp_fin h1
  have := fv_unique hs hH; subst this
  obtain ⟨ve, vc, he, hc, i3⟩ := addUp_fin he2
  obtain ⟨a1, b1, vq, ha1, hb1, hq, i4⟩ := fmaUp_fin he
  have hq' := fv_of_neg hq
  have := fv_unique hq' hp; subst this
  obtain ⟨v5, v6, h5, h6, i5⟩ := addUp_fin hc
  obtain ⟨v7, v8, h7, h8, i6⟩ := addUp_fin h5
  obtain ⟨a1', b2, ha1', hb2, i7⟩ := mulUp_fin h7
  have := fv_unique ha1' ha1; subst this
  obtain ⟨a2, b1', ha2, hb1', i8⟩ := mulUp_fin h8
  have := fv_unique hb1' hb1; subst this
  obtain ⟨a2', b2', ha2', hb2', i9⟩ := mulUp_fin h6
  have := fv_unique ha2' ha2; subst this
  have := fv_unique hb2' hb2; subst this
  exact ⟨a1', a2', b1', b2', ha1, ha2, hb1, hb2, by nlinarith⟩

theorem not_fv_neginf {x : ℝ} : ¬ Fv (-Float.inf) x := by
  intro h
  have := toE_of_fv h
  rw [toE_neg isNaN_inf, toE_inf] at this
  exact EReal.coe_ne_bot x (by rw [← this]; rfl)

theorem not_fv_inf {x : ℝ} : ¬ Fv Float.inf x := by
  intro h
  have := toE_of_fv h
  rw [toE_inf] at this
  exact EReal.coe_ne_top x this.symm

/-! ### Sign tests -/

theorem nonneg_iff {h l : Float} {a b : ℝ} (ha : Fv h a) (hb : Fv l b) :
    DD.nonneg h l = true ↔ 0 ≤ a + b := by
  unfold DD.nonneg; rw [le_iff_fv (fv_neg ha) hb]; constructor <;> intro <;> linarith

theorem nonpos_iff {h l : Float} {a b : ℝ} (ha : Fv h a) (hb : Fv l b) :
    DD.nonpos h l = true ↔ a + b ≤ 0 := by
  unfold DD.nonpos; rw [le_iff_fv hb (fv_neg ha)]; constructor <;> intro <;> linarith

theorem pos_iff {h l : Float} {a b : ℝ} (ha : Fv h a) (hb : Fv l b) :
    DD.pos h l = true ↔ 0 < a + b := by
  unfold DD.pos; rw [lt_iff_fv (fv_neg ha) hb]; constructor <;> intro <;> linarith

theorem neg_iff {h l : Float} {a b : ℝ} (ha : Fv h a) (hb : Fv l b) :
    DD.neg h l = true ↔ a + b < 0 := by
  unfold DD.neg; rw [lt_iff_fv hb (fv_neg ha)]; constructor <;> intro <;> linarith

/-! ### Quotient of a remainder bound -/

theorem quotLo_le {r dLo dHi : Float} {B C : ℝ} (hB : 0 < B)
    (hlo : ∀ D, Fv dLo D → D ≤ B) (hhi : ∀ D, Fv dHi D → B ≤ D)
    (hC : Fv (quotLo r dLo dHi) C) : ∃ R, Fv r R ∧ C ≤ R / B := by
  unfold quotLo at hC
  split at hC
  · rename_i hr
    split at hC
    · rename_i hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨D, hD, hD0⟩ := fv_of_pos_lt_inf hd.1 hd.2
      obtain ⟨R, hR, i⟩ := divDown_fin hC hD hD0.ne'
      have hR0 : 0 ≤ R := (le_iff_fv fv_zero hR).1 hr
      refine ⟨R, hR, le_trans i ?_⟩
      exact div_le_div_of_nonneg_left hR0 hB (hhi D hD)
    · exact absurd hC not_fv_neginf
  · rename_i hr
    split at hC
    · rename_i hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨D, hD, hD0⟩ := fv_of_pos_lt_inf hd.1 hd.2
      obtain ⟨R, hR, i⟩ := divDown_fin hC hD hD0.ne'
      have hR0 : R < 0 := by
        have := (le_iff_fv fv_zero hR).not.1 (by simpa using hr); linarith
      refine ⟨R, hR, le_trans i ?_⟩
      rw [div_le_div_iff₀ hD0 hB]; nlinarith [hlo D hD]
    · exact absurd hC not_fv_neginf

theorem quotHi_ge {r dLo dHi : Float} {B C : ℝ} (hB : 0 < B)
    (hlo : ∀ D, Fv dLo D → D ≤ B) (hhi : ∀ D, Fv dHi D → B ≤ D)
    (hC : Fv (quotHi r dLo dHi) C) : ∃ R, Fv r R ∧ R / B ≤ C := by
  unfold quotHi at hC
  split at hC
  · rename_i hr
    split at hC
    · rename_i hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨D, hD, hD0⟩ := fv_of_pos_lt_inf hd.1 hd.2
      obtain ⟨R, hR, i⟩ := divUp_fin hC hD hD0.ne'
      have hR0 : 0 ≤ R := (le_iff_fv fv_zero hR).1 hr
      refine ⟨R, hR, le_trans ?_ i⟩
      exact div_le_div_of_nonneg_left hR0 hD0 (hlo D hD)
    · exact absurd hC not_fv_inf
  · rename_i hr
    split at hC
    · rename_i hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨D, hD, hD0⟩ := fv_of_pos_lt_inf hd.1 hd.2
      obtain ⟨R, hR, i⟩ := divUp_fin hC hD hD0.ne'
      have hR0 : R < 0 := by
        have := (le_iff_fv fv_zero hR).not.1 (by simpa using hr); linarith
      refine ⟨R, hR, le_trans ?_ i⟩
      rw [div_le_div_iff₀ hB hD0]; nlinarith [hhi D hD]
    · exact absurd hC not_fv_inf

theorem isFinite_of_fv {f : Float} {x : ℝ} (h : Fv f x) : f.isFinite = true := by
  obtain ⟨q, hq, -⟩ := toReal?_eq_some.1 h
  have : f.isFinite = (Interval64.Spec.unpackBits f.toBits).isFinite := rfl
  rw [this]
  rcases Interval64Proofs.AddBits.bitsToRat?_cases hq with ⟨s, hu, -⟩ | ⟨s, m, e, hm, hu, -, -⟩ <;>
    rw [hu] <;> rfl

theorem isFin_of_fv {d : DD} {a b : ℝ} (ha : Fv d.hi a) (hb : Fv d.lo b) : d.isFin = true := by
  simp [DD.isFin, isFinite_of_fv ha, isFinite_of_fv hb]

theorem fv_of_isFin {d : DD} (h : d.isFin = true) : ∃ a b, Fv d.hi a ∧ Fv d.lo b := by
  simp only [DD.isFin, Bool.and_eq_true] at h
  obtain ⟨a, ha⟩ := isFinite_fv h.1
  obtain ⟨b, hb⟩ := isFinite_fv h.2
  exact ⟨a, b, ha, hb⟩

/-! ### Minimum / maximum of two pairs -/

theorem minLo_le {a b : DD} {H L : ℝ} (hH : Fv (minLo a b).hi H) (hL : Fv (minLo a b).lo L) :
    ∃ A B, DDv a A ∧ DDv b B ∧ H + L ≤ A ∧ H + L ≤ B := by
  unfold minLo at hH hL
  dsimp only at hH hL
  split_ifs at hH hL with c1 c2
  · simp only [Bool.and_eq_true] at c1
    obtain ⟨U1, U2, hU1, hU2⟩ := fv_of_isFin c1.1
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addHi_ge hU1 hU2
    have i2 := (nonpos_iff hU1 hU2).1 c1.2
    have := fv_unique ha1 hH; subst this
    have := fv_unique ha2 hL; subst this
    exact ⟨a1 + a2, -b1 + -b2, ⟨a1, a2, ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, le_rfl, by linarith⟩
  · simp only [Bool.and_eq_true] at c2
    obtain ⟨W1, W2, hW1, hW2⟩ := fv_of_isFin c2.1
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addLo_le hW1 hW2
    have i2 := (pos_iff hW1 hW2).1 c2.2
    have := fv_unique (fv_of_neg hb1) hH; subst this
    have := fv_unique (fv_of_neg hb2) hL; subst this
    exact ⟨a1 + a2, -b1 + -b2, ⟨a1, a2, ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, by linarith, le_rfl⟩
  · obtain ⟨a1, a2, c1', c2', ha1, ha2, hc1, hc2, i⟩ := addLo_le hH hL
    have hU1 := fv_of_neg hc1
    have hU2 := fv_of_neg hc2
    obtain ⟨a1', a2', b1, b2, ha1', ha2', hb1, hb2, j⟩ := addHi_ge hU1 hU2
    have := fv_unique ha1' ha1; subst this
    have := fv_unique ha2' ha2; subst this
    have hpos : ¬ (-c1' + -c2' ≤ 0) := by
      intro hle
      exact c1 (by simp [isFin_of_fv hU1 hU2, (nonpos_iff hU1 hU2).2 hle])
    exact ⟨a1' + a2', -b1 + -b2, ⟨a1', a2', ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, by linarith, by linarith⟩

theorem maxHi_ge {a b : DD} {H L : ℝ} (hH : Fv (maxHi a b).hi H) (hL : Fv (maxHi a b).lo L) :
    ∃ A B, DDv a A ∧ DDv b B ∧ A ≤ H + L ∧ B ≤ H + L := by
  unfold maxHi at hH hL
  dsimp only at hH hL
  split_ifs at hH hL with c1 c2
  · simp only [Bool.and_eq_true] at c1
    obtain ⟨W1, W2, hW1, hW2⟩ := fv_of_isFin c1.1
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addLo_le hW1 hW2
    have i2 := (nonneg_iff hW1 hW2).1 c1.2
    have := fv_unique ha1 hH; subst this
    have := fv_unique ha2 hL; subst this
    exact ⟨a1 + a2, -b1 + -b2, ⟨a1, a2, ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, le_rfl, by linarith⟩
  · simp only [Bool.and_eq_true] at c2
    obtain ⟨U1, U2, hU1, hU2⟩ := fv_of_isFin c2.1
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addHi_ge hU1 hU2
    have i2 := (neg_iff hU1 hU2).1 c2.2
    have := fv_unique (fv_of_neg hb1) hH; subst this
    have := fv_unique (fv_of_neg hb2) hL; subst this
    exact ⟨a1 + a2, -b1 + -b2, ⟨a1, a2, ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, by linarith, le_rfl⟩
  · obtain ⟨a1, a2, c1', c2', ha1, ha2, hc1, hc2, i⟩ := addHi_ge hH hL
    have hW1 := fv_of_neg hc1
    have hW2 := fv_of_neg hc2
    obtain ⟨a1', a2', b1, b2, ha1', ha2', hb1, hb2, j⟩ := addLo_le hW1 hW2
    have := fv_unique ha1' ha1; subst this
    have := fv_unique ha2' ha2; subst this
    have hneg : ¬ (0 ≤ -c1' + -c2') := by
      intro hle
      exact c1 (by simp [isFin_of_fv hW1 hW2, (nonneg_iff hW1 hW2).2 hle])
    exact ⟨a1' + a2', -b1 + -b2, ⟨a1', a2', ha1, ha2, rfl⟩,
      ⟨-b1, -b2, fv_of_neg hb1, fv_of_neg hb2, rfl⟩, by linarith, by linarith⟩

/-! ### Division -/

theorem den_lo {bh bl : Float} {b1 b2 : ℝ} (hb1 : Fv bh b1) (hb2 : Fv bl b2) :
    ∀ D, Fv (addDown bh bl) D → D ≤ b1 + b2 := by
  intro D hD
  obtain ⟨x, y, hx, hy, i⟩ := addDown_fin hD
  rw [fv_unique hx hb1, fv_unique hy hb2] at i; exact i

theorem den_hi {bh bl : Float} {b1 b2 : ℝ} (hb1 : Fv bh b1) (hb2 : Fv bl b2) :
    ∀ D, Fv (addUp bh bl) D → b1 + b2 ≤ D := by
  intro D hD
  obtain ⟨x, y, hx, hy, i⟩ := addUp_fin hD
  rw [fv_unique hx hb1, fv_unique hy hb2] at i; exact i

theorem divLo_le {ah al bh bl : Float} {a1 a2 b1 b2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hb1 : Fv bh b1) (hb2 : Fv bl b2) (hB : 0 < b1 + b2)
    (hH : Fv (divLo ah al bh bl).hi H) (hL : Fv (divLo ah al bh bl).lo L) :
    H + L ≤ (a1 + a2) / (b1 + b2) := by
  dsimp only [divLo] at hH hL
  obtain ⟨v1, ve, h1, he, i1⟩ := addDown_fin hL
  obtain ⟨vs, vs2, hs, hs2, i2⟩ := subDown_fin h1
  have := fv_unique hs2 hH; subst this
  obtain ⟨v2, vc, h2, hc, i3⟩ := addDown_fin he
  obtain ⟨v3, vq2, h3, hq2, i4⟩ := addDown_fin h2
  obtain ⟨vq1, vs', hq1, hs', i5⟩ := subDown_fin h3
  have := fv_unique hs' hs; subst this
  obtain ⟨R, hR, i6⟩ := quotLo_le hB (den_lo hb1 hb2) (den_hi hb1 hb2) hc
  obtain ⟨w1, w2, hw1, hw2, i7⟩ := addDown_fin hR
  obtain ⟨w3, ve2, hw3, he2, i8⟩ := subDown_fin hw1
  obtain ⟨vx, vp2, hx, hp2, i9⟩ := subDown_fin hw3
  obtain ⟨n2, b2', hn2, hb2', i10⟩ := mulDown_fin hw2
  have := fv_unique hb2' hb2; subst this
  have := fv_unique (fv_of_neg hn2) hq2; subst this
  obtain ⟨q2', b1', np2, hq2', hb1', hnp2, i11⟩ := fmaUp_fin he2
  have := fv_unique hq2' hq2; subst this
  have := fv_unique hb1' hb1; subst this
  have := fv_unique (fv_of_neg hnp2) hp2; subst this
  obtain ⟨y1, y2, hy1, hy2, i12⟩ := addDown_fin hx
  obtain ⟨vr1, a2', hr1, ha2', i13⟩ := addDown_fin hy1
  have := fv_unique ha2' ha2; subst this
  obtain ⟨n1, b2'', hn1, hb2'', i14⟩ := mulDown_fin hy2
  have := fv_unique hb2'' hb2; subst this
  have := fv_unique (fv_of_neg hn1) hq1; subst this
  obtain ⟨n1', b1'', a1', hn1', hb1'', ha1', i15⟩ := fmaDown_fin hr1
  have := fv_unique hn1' hn1; subst this
  have := fv_unique hb1'' hb1; subst this
  have := fv_unique ha1' ha1; subst this
  -- R ≤ A - (q1 + q2) B
  have hRle : R ≤ (a1' + a2') - (-n1' + -n2) * (b1'' + b2'') := by nlinarith
  have e : (a1' + a2') / (b1'' + b2'') - (-n1' + -n2) =
      ((a1' + a2') - (-n1' + -n2) * (b1'' + b2'')) / (b1'' + b2'') := by
    field_simp
  have hq : R / (b1'' + b2'') ≤ (a1' + a2') / (b1'' + b2'') - (-n1' + -n2) := by
    rw [e]; exact (div_le_div_iff_of_pos_right hB).2 hRle
  linarith

theorem divHi_ge {ah al bh bl : Float} {a1 a2 b1 b2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hb1 : Fv bh b1) (hb2 : Fv bl b2) (hB : 0 < b1 + b2)
    (hH : Fv (divHi ah al bh bl).hi H) (hL : Fv (divHi ah al bh bl).lo L) :
    (a1 + a2) / (b1 + b2) ≤ H + L := by
  dsimp only [divHi] at hH hL
  obtain ⟨v1, ve, h1, he, i1⟩ := addUp_fin hL
  obtain ⟨vs, vs2, hs, hs2, i2⟩ := subUp_fin h1
  have := fv_unique hs2 hH; subst this
  obtain ⟨v2, vc, h2, hc, i3⟩ := addUp_fin he
  obtain ⟨v3, vq2, h3, hq2, i4⟩ := addUp_fin h2
  obtain ⟨vq1, vs', hq1, hs', i5⟩ := subUp_fin h3
  have := fv_unique hs' hs; subst this
  obtain ⟨R, hR, i6⟩ := quotHi_ge hB (den_lo hb1 hb2) (den_hi hb1 hb2) hc
  obtain ⟨w1, w2, hw1, hw2, i7⟩ := addUp_fin hR
  obtain ⟨w3, ve2, hw3, he2, i8⟩ := subUp_fin hw1
  obtain ⟨vx, vp2, hx, hp2, i9⟩ := subUp_fin hw3
  obtain ⟨n2, b2', hn2, hb2', i10⟩ := mulUp_fin hw2
  have := fv_unique hb2' hb2; subst this
  have := fv_unique (fv_of_neg hn2) hq2; subst this
  obtain ⟨q2', b1', np2, hq2', hb1', hnp2, i11⟩ := fmaDown_fin he2
  have := fv_unique hq2' hq2; subst this
  have := fv_unique hb1' hb1; subst this
  have := fv_unique (fv_of_neg hnp2) hp2; subst this
  obtain ⟨y1, y2, hy1, hy2, i12⟩ := addUp_fin hx
  obtain ⟨vr1, a2', hr1, ha2', i13⟩ := addUp_fin hy1
  have := fv_unique ha2' ha2; subst this
  obtain ⟨n1, b2'', hn1, hb2'', i14⟩ := mulUp_fin hy2
  have := fv_unique hb2'' hb2; subst this
  have := fv_unique (fv_of_neg hn1) hq1; subst this
  obtain ⟨n1', b1'', a1', hn1', hb1'', ha1', i15⟩ := fmaUp_fin hr1
  have := fv_unique hn1' hn1; subst this
  have := fv_unique hb1'' hb1; subst this
  have := fv_unique ha1' ha1; subst this
  have hRle : (a1' + a2') - (-n1' + -n2) * (b1'' + b2'') ≤ R := by nlinarith
  have e : (a1' + a2') / (b1'' + b2'') - (-n1' + -n2) =
      ((a1' + a2') - (-n1' + -n2) * (b1'' + b2'')) / (b1'' + b2'') := by
    field_simp
  have hq : (a1' + a2') / (b1'' + b2'') - (-n1' + -n2) ≤ R / (b1'' + b2'') := by
    rw [e]; exact (div_le_div_iff_of_pos_right hB).2 hRle
  linarith

/-! ### Square root -/

theorem sqrt_den_lo {ah al s : Float} {a1 a2 S : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hs : Fv s S) :
    ∀ D, Fv (addDown (sqrtDown (addDown ah al)) s) D → D ≤ Real.sqrt (a1 + a2) + S := by
  intro D hD
  obtain ⟨u, S', hu, hs', i1⟩ := addDown_fin hD
  rw [fv_unique hs' hs] at i1
  obtain ⟨t, ht, -, i2⟩ := sqrtDown_fin hu
  obtain ⟨x, y, hx, hy, i3⟩ := addDown_fin ht
  rw [fv_unique hx ha1, fv_unique hy ha2] at i3
  have := Real.sqrt_le_sqrt i3
  linarith

theorem sqrt_den_hi {ah al s : Float} {a1 a2 S : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hs : Fv s S) :
    ∀ D, Fv (addUp (sqrtUp (addUp ah al)) s) D → Real.sqrt (a1 + a2) + S ≤ D := by
  intro D hD
  obtain ⟨u, S', hu, hs', i1⟩ := addUp_fin hD
  rw [fv_unique hs' hs] at i1
  obtain ⟨t, ht, -, i2⟩ := sqrtUp_fin hu
  obtain ⟨x, y, hx, hy, i3⟩ := addUp_fin ht
  rw [fv_unique hx ha1, fv_unique hy ha2] at i3
  have := Real.sqrt_le_sqrt i3
  linarith

theorem sqrt_identity {A S : ℝ} (hA : 0 ≤ A) (hS : 0 < S) :
    (A - S * S) / (Real.sqrt A + S) = Real.sqrt A - S := by
  have h0 : 0 < Real.sqrt A + S := by positivity
  rw [div_eq_iff h0.ne']
  have := Real.sq_sqrt hA
  nlinarith

theorem sqrtLo_le {ah al : Float} {a1 a2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hA : 0 ≤ a1 + a2) (hH : Fv (sqrtLo ah al).hi H) (hL : Fv (sqrtLo ah al).lo L) :
    H + L ≤ Real.sqrt (a1 + a2) := by
  unfold sqrtLo at hH hL
  dsimp only at hH hL
  split_ifs at hH hL with c
  · obtain ⟨v1, vc, h1, hc, i1⟩ := addDown_fin hL
    obtain ⟨vs, vs2, hs, hs2, i2⟩ := subDown_fin h1
    have := fv_unique hs2 hH; subst this
    have hS : 0 < vs := (lt_iff_fv fv_zero hs).1 c
    have hB : 0 < Real.sqrt (a1 + a2) + vs := by positivity
    obtain ⟨R, hR, i3⟩ := quotLo_le hB (sqrt_den_lo ha1 ha2 hs) (sqrt_den_hi ha1 ha2 hs) hc
    obtain ⟨vf, a2', hf, ha2', i4⟩ := addDown_fin hR
    have := fv_unique ha2 ha2'; subst this
    obtain ⟨n, s', a1', hn, hs', ha1', i5⟩ := fmaDown_fin hf
    have := fv_unique hs hs'; subst this
    have := fv_unique ha1 ha1'; subst this
    have hn' : n = -vs := by have := fv_unique (fv_of_neg hn) hs; linarith
    subst hn'
    have hRle : R ≤ (a1 + a2) - vs * vs := by nlinarith
    have hq : R / (Real.sqrt (a1 + a2) + vs) ≤ Real.sqrt (a1 + a2) - vs := by
      rw [← sqrt_identity hA hS]; exact (div_le_div_iff_of_pos_right hB).2 hRle
    linarith
  · exact absurd hH not_fv_neginf

theorem sqrtHi_ge {ah al : Float} {a1 a2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hA : 0 ≤ a1 + a2) (hH : Fv (sqrtHi ah al).hi H) (hL : Fv (sqrtHi ah al).lo L) :
    Real.sqrt (a1 + a2) ≤ H + L := by
  unfold sqrtHi at hH hL
  dsimp only at hH hL
  split_ifs at hH hL with c
  · obtain ⟨v1, vc, h1, hc, i1⟩ := addUp_fin hL
    obtain ⟨vs, vs2, hs, hs2, i2⟩ := subUp_fin h1
    have := fv_unique hs2 hH; subst this
    have hS : 0 < vs := (lt_iff_fv fv_zero hs).1 c
    have hB : 0 < Real.sqrt (a1 + a2) + vs := by positivity
    obtain ⟨R, hR, i3⟩ := quotHi_ge hB (sqrt_den_lo ha1 ha2 hs) (sqrt_den_hi ha1 ha2 hs) hc
    obtain ⟨vf, a2', hf, ha2', i4⟩ := addUp_fin hR
    have := fv_unique ha2 ha2'; subst this
    obtain ⟨n, s', a1', hn, hs', ha1', i5⟩ := fmaUp_fin hf
    have := fv_unique hs hs'; subst this
    have := fv_unique ha1 ha1'; subst this
    have hn' : n = -vs := by have := fv_unique (fv_of_neg hn) hs; linarith
    subst hn'
    have hRle : (a1 + a2) - vs * vs ≤ R := by nlinarith
    have hq : Real.sqrt (a1 + a2) - vs ≤ R / (Real.sqrt (a1 + a2) + vs) := by
      rw [← sqrt_identity hA hS]; exact (div_le_div_iff_of_pos_right hB).2 hRle
    linarith
  · exact absurd hH not_fv_inf

end RealFP.I128
