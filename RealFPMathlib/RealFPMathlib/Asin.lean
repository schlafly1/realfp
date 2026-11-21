/-
Real enclosures for the directed `asin`, `acos` of `Interval64.Asin` and the intervals.
-/
import RealFPMathlib.Tan
import Interval64.Asin
import RealFPMathlib.Ops

open Interval64 Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig
open Interval64.Asin
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits

namespace RealFP.Asin

open RealFP.Transc RealFP.Trig RealFP.InvTrig RealFP.Hyp

theorem le_arcsin_of_sin_le {a q : ℝ} (ha0 : -(Real.pi / 2) ≤ a) (ha1 : a ≤ Real.pi / 2)
    (h : Real.sin a ≤ q) : a ≤ Real.arcsin q := by
  have := Real.arcsin_le_arcsin h; rwa [Real.arcsin_sin ha0 ha1] at this

theorem arcsin_le_of_le_sin {b q : ℝ} (hb0 : -(Real.pi / 2) ≤ b) (hb1 : b ≤ Real.pi / 2)
    (h : q ≤ Real.sin b) : Real.arcsin q ≤ b := by
  have := Real.arcsin_le_arcsin h; rwa [Real.arcsin_sin hb0 hb1] at this

theorem le_arcsin_self {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : q ≤ Real.arcsin q := by
  have hs := Real.sin_arcsin (by linarith) h1
  have hy : 0 ≤ Real.arcsin q := Real.arcsin_nonneg.2 h0
  rcases hy.lt_or_eq with hy | hy
  · have := Real.sin_lt hy; linarith
  · rw [← hy, Real.sin_zero] at hs; linarith

theorem arcsin_le_tiny {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1 / 32) : Real.arcsin q ≤ q + q ^ 3 / 5 := by
  set b := q + q ^ 3 / 5 with hbdef
  have hq3 : q ^ 3 ≤ q / 1024 := by nlinarith [pow_le_pow_left₀ h0 h1 2]
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b ≤ q * (5121 / 5120) := by nlinarith
  have hbl : b ≤ 1 := by linarith
  have hpi := Real.pi_gt_three
  refine arcsin_le_of_le_sin (by linarith) (by linarith) ?_
  have hsb := Real.sin_bound (x := b) (by rw [abs_of_nonneg hb0]; exact hbl)
  rw [abs_of_nonneg hb0] at hsb
  have hs := (abs_le.1 hsb).1
  have e3 : b ^ 3 ≤ (q * (5121 / 5120)) ^ 3 := pow_le_pow_left₀ hb0 hb1 3
  have e5 : b ^ 5 ≤ b ^ 3 := pow_le_pow_of_le_one hb0 hbl (by norm_num)
  have hq0 : 0 ≤ q ^ 3 := by positivity
  nlinarith

theorem halfPi_le {p : ℕ} : ((piBounds p false).1 / 2 : ℚ) ≤ (Real.pi / 2 : ℝ) := by
  have := (piBounds_spec p false).1; push_cast; linarith

theorem lo_ok {q a : ℚ} {cp : ℕ} {pb : ℚ × ℚ} (hpb : (pb.1 : ℝ) ≤ Real.pi)
    (h : 0 ≤ a ∧ a ≤ pb.1 / 2 ∧ (trigBounds a cp).1.2 ≤ q) : (a : ℝ) ≤ Real.arcsin q := by
  obtain ⟨a0, a1, a2⟩ := h
  have ts := (trigBounds_spec a cp).1
  have b0 : (0 : ℝ) ≤ a := by exact_mod_cast a0
  have b1 : (a : ℝ) ≤ (pb.1 : ℝ) / 2 := by
    have := Rat.cast_le (K := ℝ) |>.2 a1; push_cast at this; exact this
  have b2 : ((trigBounds a cp).1.2 : ℝ) ≤ q := by exact_mod_cast a2
  exact le_arcsin_of_sin_le (by linarith [Real.pi_pos]) (by linarith) (by linarith [ts.2])

theorem hi_ok {q b : ℚ} {cp : ℕ} {pb : ℚ × ℚ} (hpb : (pb.1 : ℝ) ≤ Real.pi)
    (h : 0 ≤ b ∧ b ≤ pb.1 / 2 ∧ q ≤ (trigBounds b cp).1.1) : Real.arcsin q ≤ (b : ℝ) := by
  obtain ⟨a0, a1, a2⟩ := h
  have ts := (trigBounds_spec b cp).1
  have b0 : (0 : ℝ) ≤ b := by exact_mod_cast a0
  have b1 : (b : ℝ) ≤ (pb.1 : ℝ) / 2 := by
    have := Rat.cast_le (K := ℝ) |>.2 a1; push_cast at this; exact this
  have b2 : (q : ℝ) ≤ (trigBounds b cp).1.1 := by exact_mod_cast a2
  exact arcsin_le_of_le_sin (by linarith [Real.pi_pos]) (by linarith) (by linarith [ts.1])

theorem asinPos_spec {q : ℚ} (h0 : 0 < q) (h1 : q < 1) (p : ℕ) :
    ((asinPos q p).1 : ℝ) ≤ Real.arcsin q ∧ Real.arcsin q ≤ (asinPos q p).2 := by
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast h0.le
  have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast h1.le
  have hpi := piBounds_spec (p + 20) false
  have flo : ((0 : ℚ) : ℝ) ≤ Real.arcsin q := by push_cast; exact Real.arcsin_nonneg.2 hq0
  have fhi : Real.arcsin q ≤ (((piBounds (p + 20) false).2 / 2 : ℚ) : ℝ) := by
    push_cast; linarith [Real.arcsin_le_pi_div_two q, hpi.2]
  unfold asinPos
  dsimp only
  split_ifs with ht hl hh hh
  · have h32 := Rat.cast_le (K := ℝ) |>.2 ht.1
    push_cast at h32 ⊢
    exact ⟨le_arcsin_self hq0 hq1, arcsin_le_tiny hq0 h32⟩
  · exact ⟨lo_ok hpi.1 hl, hi_ok hpi.1 hh⟩
  · exact ⟨lo_ok hpi.1 hl, fhi⟩
  · exact ⟨flo, hi_ok hpi.1 hh⟩
  · exact ⟨flo, fhi⟩

theorem asinBounds_spec {q : ℚ} (h : |(q : ℝ)| ≤ 1) (p : ℕ) :
    ((asinBounds q p).1 : ℝ) ≤ Real.arcsin q ∧ Real.arcsin q ≤ (asinBounds q p).2 := by
  obtain ⟨hl, hu⟩ := abs_le.1 h
  unfold asinBounds
  split_ifs with h0 h1 h2 h3
  · subst h0; simp
  · subst h1
    have := piMul_spec (1 / 2) p; push_cast at this ⊢; rw [Real.arcsin_one]
    constructor <;> linarith [this.1, this.2]
  · subst h2
    have := piMul_spec (-1 / 2) p; push_cast at this ⊢; rw [Real.arcsin_neg_one]
    constructor <;> linarith [this.1, this.2]
  · have h1' : q < 1 := lt_of_le_of_ne (by exact_mod_cast hu) h1
    exact asinPos_spec h3 h1' p
  · have hq : 0 < -q := by
      rcases lt_or_eq_of_le (not_lt.1 h3) with h | h
      · linarith
      · exact absurd h h0
    have hq1 : -q < 1 := by
      have : (-1 : ℝ) ≤ q := hl
      have h' : (-1 : ℚ) ≤ q := by exact_mod_cast this
      rcases lt_or_eq_of_le h' with h | h
      · linarith
      · exact absurd h.symm h2
    obtain ⟨a, b⟩ := asinPos_spec hq hq1 p
    push_cast at a b ⊢
    rw [Real.arcsin_neg] at a b
    constructor <;> linarith

theorem acosBounds_spec {q : ℚ} (h : |(q : ℝ)| ≤ 1) (p : ℕ) :
    ((acosBounds q p).1 : ℝ) ≤ Real.arccos q ∧ Real.arccos q ≤ (acosBounds q p).2 := by
  unfold acosBounds
  split_ifs with h1
  · subst h1; simp
  · dsimp only
    obtain ⟨a, b⟩ := asinBounds_spec h (p + 64)
    obtain ⟨c, d⟩ := piBounds_spec (p + 64) false
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    push_cast
    constructor <;> linarith

/-! ### Bit level -/

theorem ratAbs_le_one {q : ℚ} (h : |(q : ℝ)| ≤ 1) : ratAbs' q ≤ 1 := by
  obtain ⟨hl, hu⟩ := abs_le.1 h
  have hl' : (-1 : ℚ) ≤ q := by exact_mod_cast hl
  have hu' : q ≤ 1 := by exact_mod_cast hu
  unfold ratAbs'; split <;> linarith

theorem asinDown_loR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q))
    (hq : |(q : ℝ)| ≤ 1) : loR (bitsToEVal (Directed.asinDown a).toBits) (Real.arcsin q) := by
  apply loR_ofBits
  unfold asinDownBits asinBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show loR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [val_of_unpack_finite hu h, if_pos (ratAbs_le_one hq)]
    exact rndD_down_loR (fun p => (asinBounds_spec hq p).1)

theorem asinUp_hiR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q))
    (hq : |(q : ℝ)| ≤ 1) : hiR (bitsToEVal (Directed.asinUp a).toBits) (Real.arcsin q) := by
  apply hiR_ofBits
  unfold asinUpBits asinBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show hiR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [val_of_unpack_finite hu h, if_pos (ratAbs_le_one hq)]
    exact rndD_up_hiR (fun p => (asinBounds_spec hq p).2)

theorem acosDown_loR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q))
    (hq : |(q : ℝ)| ≤ 1) : loR (bitsToEVal (Directed.acosDown a).toBits) (Real.arccos q) := by
  apply loR_ofBits
  unfold acosDownBits acosBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    rw [zero_of_unpack_zero hu h]
    refine rndD_down_loR (fun p => ?_)
    have := (piMul_spec (1 / 2) p).1
    push_cast at this ⊢; rw [Real.arccos_zero]; linarith
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [val_of_unpack_finite hu h, if_pos (ratAbs_le_one hq)]
    exact rndD_down_loR (fun p => (acosBounds_spec hq p).1)

theorem acosUp_hiR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q))
    (hq : |(q : ℝ)| ≤ 1) : hiR (bitsToEVal (Directed.acosUp a).toBits) (Real.arccos q) := by
  apply hiR_ofBits
  unfold acosUpBits acosBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    rw [zero_of_unpack_zero hu h]
    refine rndD_up_hiR (fun p => ?_)
    have := (piMul_spec (1 / 2) p).2
    push_cast at this ⊢; rw [Real.arccos_zero]; linarith
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [val_of_unpack_finite hu h, if_pos (ratAbs_le_one hq)]
    exact rndD_up_hiR (fun p => (acosBounds_spec hq p).2)

/-! ### Interval endpoints (clamped `Real.arcsin` / `Real.arccos`) -/

theorem toE_negOne : (-1 : Float).toE = -1 := by
  rw [toE_neg isNaN_one, toE_one]

theorem isNaN_negOne : (-1 : Float).isNaN = false := by decide

/-- An endpoint that is neither `< -1` nor `> 1` is a rational in `[-1, 1]`. -/
theorem rat_of_mid {f : Float} (hn : f.isNaN = false) (h1 : ¬ f < -1) (h2 : ¬ 1 < f) :
    ∃ q : ℚ, bitsToEVal f.toBits = some (.rat q) ∧ |(q : ℝ)| ≤ 1 := by
  rw [float_lt_iff_toE hn isNaN_negOne, toE_negOne, not_lt] at h1
  rw [float_lt_iff_toE isNaN_one hn, toE_one, not_lt] at h2
  have ht : f.toE ≠ ⊤ := fun h => by rw [h] at h2; exact absurd h2 (by decide)
  have hb : f.toE ≠ ⊥ := fun h => by rw [h] at h1; exact absurd h1 (by decide)
  obtain ⟨q, hq, he⟩ := exists_rat_of_toE hn hb ht
  refine ⟨q, bitsToEVal_rat_of_bitsToRat? hq, abs_le.2 ⟨?_, ?_⟩⟩
  · rw [he] at h1; exact EReal.coe_le_coe_iff.1 (by simpa using h1)
  · rw [he] at h2; exact EReal.coe_le_coe_iff.1 (by simpa using h2)

theorem lo_of_loR {f : Float} {q : ℚ} {x : ℝ} (h : loR (bitsToEVal f.toBits) x)
    (hq : bitsToEVal f.toBits = some (.rat q)) : (q : ℝ) ≤ x := by rw [hq] at h; exact h

theorem hi_of_hiR {f : Float} {q : ℚ} {x : ℝ} (h : hiR (bitsToEVal f.toBits) x)
    (hq : bitsToEVal f.toBits = some (.rat q)) : x ≤ (q : ℝ) := by rw [hq] at h; exact h

theorem lt_negOne_real {f : Float} {x : ℝ} (hn : f.isNaN = false) (h : f < -1)
    (hx : (x : EReal) ≤ f.toE) : x ≤ -1 := by
  rw [float_lt_iff_toE hn isNaN_negOne, toE_negOne] at h
  have := lt_of_le_of_lt hx h
  exact (EReal.coe_lt_coe_iff.1 (by simpa using this)).le

theorem one_lt_real {f : Float} {x : ℝ} (hn : f.isNaN = false) (h : 1 < f)
    (hx : f.toE ≤ (x : EReal)) : 1 ≤ x := by
  rw [float_lt_iff_toE isNaN_one hn, toE_one] at h
  have := lt_of_lt_of_le h hx
  exact (EReal.coe_lt_coe_iff.1 (by simpa using this)).le

theorem zero_loR {y : ℝ} (h : 0 ≤ y) : loR (bitsToEVal (0 : Float).toBits) y :=
  (loR_iff_toE _ _).2 ⟨isNaN_zero, by simpa using h⟩

theorem zero_hiR {y : ℝ} (h : y ≤ 0) : hiR (bitsToEVal (0 : Float).toBits) y :=
  (hiR_iff_toE _ _).2 ⟨isNaN_zero, by simpa using h⟩

theorem asinLo_loR {f : Float} {x : ℝ} (h : loR (bitsToEVal f.toBits) x) :
    loR (bitsToEVal (asinLo f).toBits) (Real.arcsin x) := by
  have hn := isNaN_false_of_loR h
  have hx := ((loR_iff_toE _ _).1 h).2
  unfold asinLo
  split_ifs with h1 h2
  · exact loR_mono negHalfPi_mem_toSet.1 (Real.neg_pi_div_two_le_arcsin x)
  · rw [Real.arcsin_of_one_le (one_lt_real hn (of_decide_eq_true h2) hx)]
    exact halfPi_mem_toSet.1
  · obtain ⟨q, hq, hq1⟩ := rat_of_mid hn (fun h' => h1 (decide_eq_true h'))
      (fun h' => h2 (decide_eq_true h'))
    exact loR_mono (asinDown_loR hq hq1) (Real.arcsin_le_arcsin (lo_of_loR h hq))

theorem asinHi_hiR {f : Float} {x : ℝ} (h : hiR (bitsToEVal f.toBits) x) :
    hiR (bitsToEVal (asinHi f).toBits) (Real.arcsin x) := by
  have hn := isNaN_false_of_hiR h
  have hx := ((hiR_iff_toE _ _).1 h).2
  unfold asinHi
  split_ifs with h1 h2
  · rw [Real.arcsin_of_le_neg_one (lt_negOne_real hn (of_decide_eq_true h1) hx)]
    exact negHalfPi_mem_toSet.2
  · exact hiR_mono halfPi_mem_toSet.2 (Real.arcsin_le_pi_div_two x)
  · obtain ⟨q, hq, hq1⟩ := rat_of_mid hn (fun h' => h1 (decide_eq_true h'))
      (fun h' => h2 (decide_eq_true h'))
    exact hiR_mono (asinUp_hiR hq hq1) (Real.arcsin_le_arcsin (hi_of_hiR h hq))

theorem arccos_anti {x y : ℝ} (h : x ≤ y) : Real.arccos y ≤ Real.arccos x := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [Real.arcsin_le_arcsin h]

/-- Lower end of `acos X` from the upper endpoint `f ≥ x`. -/
theorem acosLo_loR {f : Float} {x : ℝ} (h : hiR (bitsToEVal f.toBits) x) :
    loR (bitsToEVal (acosLo f).toBits) (Real.arccos x) := by
  have hn := isNaN_false_of_hiR h
  have hx := ((hiR_iff_toE _ _).1 h).2
  unfold acosLo
  split_ifs with h1 h2
  · rw [Real.arccos_of_le_neg_one (lt_negOne_real hn (of_decide_eq_true h1) hx)]
    exact pi_mem_toSet.1
  · exact zero_loR (Real.arccos_nonneg x)
  · obtain ⟨q, hq, hq1⟩ := rat_of_mid hn (fun h' => h1 (decide_eq_true h'))
      (fun h' => h2 (decide_eq_true h'))
    exact loR_mono (acosDown_loR hq hq1) (arccos_anti (hi_of_hiR h hq))

/-- Upper end of `acos X` from the lower endpoint `f ≤ x`. -/
theorem acosHi_hiR {f : Float} {x : ℝ} (h : loR (bitsToEVal f.toBits) x) :
    hiR (bitsToEVal (acosHi f).toBits) (Real.arccos x) := by
  have hn := isNaN_false_of_loR h
  have hx := ((loR_iff_toE _ _).1 h).2
  unfold acosHi
  split_ifs with h1 h2
  · exact hiR_mono pi_mem_toSet.2 (Real.arccos_le_pi x)
  · rw [Real.arccos_of_one_le (one_lt_real hn (of_decide_eq_true h2) hx)]
    exact zero_hiR le_rfl
  · obtain ⟨q, hq, hq1⟩ := rat_of_mid hn (fun h' => h1 (decide_eq_true h'))
      (fun h' => h2 (decide_eq_true h'))
    exact hiR_mono (acosUp_hiR hq hq1) (arccos_anti (lo_of_loR h hq))

/-- `asin` interval enclosure (Mathlib's `Real.arcsin`, any real member). -/
theorem asin_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.arcsin x ∈ (Interval64.asin X).toSet := by
  unfold Interval64.asin
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨asinLo_loR hx.1, asinHi_hiR hx.2⟩

/-- `acos` interval enclosure (Mathlib's `Real.arccos`, any real member). -/
theorem acos_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.arccos x ∈ (Interval64.acos X).toSet := by
  unfold Interval64.acos
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨acosLo_loR hx.2, acosHi_hiR hx.1⟩

end RealFP.Asin
