/-
Real enclosures for the directed `tan` of `Interval64.Tan` and the interval `tan`.
-/
import RealFPMathlib.Hyp
import Interval64.Tan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Irrational

open Interval64 Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig
open Interval64.Hyp Interval64.Tan
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits

namespace RealFP.Tan

open RealFP.Transc RealFP.Trig RealFP.InvTrig RealFP.Hyp

theorem tanRes_spec {q : ℚ} {p : ℕ} {b : ℚ × ℚ} (h : tanRes q p = some b) :
    (b.1 : ℝ) ≤ Real.tan q ∧ Real.tan q ≤ b.2 := by
  unfold tanRes at h
  dsimp only at h
  obtain ⟨hs, hc⟩ := trigBounds_spec q p
  rw [Real.tan_eq_sin_div_cos]
  split_ifs at h with h1 h2
  · cases h
    exact divPos_spec hs hc (by exact_mod_cast h1)
  · cases h
    have := divPos_spec (x := -Real.sin q) (y := -Real.cos q)
      (n := (-(trigBounds q p).1.2, -(trigBounds q p).1.1))
      (d := (-(trigBounds q p).2.2, -(trigBounds q p).2.1))
      (by push_cast; constructor <;> linarith [hs.1, hs.2])
      (by push_cast; constructor <;> linarith [hc.1, hc.2])
      (by push_cast; have : ((trigBounds q p).2.2 : ℝ) < 0 := by exact_mod_cast h2
          linarith)
    rwa [neg_div_neg_eq] at this

theorem tanFallback_spec {q : ℚ} {b : ℚ × ℚ} (h : tanFallback q = some b) :
    (b.1 : ℝ) ≤ Real.tan q ∧ Real.tan q ≤ b.2 := by
  unfold tanFallback at h
  split at h
  · rename_i b' hb; cases h; exact tanRes_spec hb
  · exact tanRes_spec h

theorem tanBounds_spec {q : ℚ} {b0 : ℚ × ℚ} (h0 : tanFallback q = some b0) (p : ℕ) :
    ((tanBounds q p).1 : ℝ) ≤ Real.tan q ∧ Real.tan q ≤ (tanBounds q p).2 := by
  unfold tanBounds
  split
  · rename_i b hb; exact tanRes_spec hb
  · rw [h0]; exact tanFallback_spec h0

theorem tanRat_down (q : ℚ) : loR (bitsToEVal (tanRat q false).1) (Real.tan q) := by
  unfold tanRat
  split
  · rename_i b hb; exact rndD_down_loR (fun p => (tanBounds_spec hb p).1)
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [bitsToEVal_negInf]; trivial

theorem tanRat_up (q : ℚ) : hiR (bitsToEVal (tanRat q true).1) (Real.tan q) := by
  unfold tanRat
  split
  · rename_i b hb; exact rndD_up_hiR (fun p => (tanBounds_spec hb p).2)
  · simp only [↓reduceIte]; rw [bitsToEVal_posInf]; trivial

theorem tanDown_loR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    loR (bitsToEVal (Directed.tanDown a).toBits) (Real.tan q) := by
  apply loR_ofBits
  unfold tanDownBits tanBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show loR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact tanRat_down _

theorem tanUp_hiR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    hiR (bitsToEVal (Directed.tanUp a).toBits) (Real.tan q) := by
  apply hiR_ofBits
  unfold tanUpBits tanBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show hiR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact tanRat_up _

/-! ### No pole between `a` and `b` -/

theorem halfPi_mul_ne {j : ℤ} (hj : j ≠ 0) (r : ℚ) : (j : ℝ) * (Real.pi / 2) ≠ r := by
  intro h
  apply irrational_pi
  refine ⟨2 * r / j, ?_⟩
  have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  push_cast; rw [← h]; field_simp

theorem int_lt_of_rat {m j : ℤ} {r : ℚ} (hm : m ≠ 0) (h1 : (m : ℝ) * (Real.pi / 2) ≤ r)
    (h2 : (r : ℝ) ≤ j * (Real.pi / 2)) : m < j := by
  have hP : 0 < Real.pi / 2 := by positivity
  have hle : (m : ℝ) ≤ j := le_of_mul_le_mul_right (h1.trans h2) hP
  rcases lt_or_eq_of_le (show m ≤ j by exact_mod_cast hle) with h | h
  · exact h
  · subst h; exact absurd (le_antisymm h1 h2) (halfPi_mul_ne hm r)

theorem cos_ne_of_avoids {a b : ℚ} (h1 : avoids a b 1 = true) (h3 : avoids a b 3 = true)
    {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ b) : Real.cos x ≠ 0 := by
  intro hc
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 hc
  have hx : x = ((2 * k + 1 : ℤ) : ℝ) * (Real.pi / 2) := by rw [hk]; push_cast; ring
  obtain ⟨n1, l1, u1⟩ := avoids_spec h1
  obtain ⟨n3, l3, u3⟩ := avoids_spec h3
  rw [hx] at ha hb
  have a1 := int_lt_of_rat (by omega) l1 ha
  have b1 := int_lt_of_rat (by omega) hb u1
  have a3 := int_lt_of_rat (by omega) l3 ha
  have b3 := int_lt_of_rat (by omega) hb u3
  omega

theorem tan_mono_of_avoids {a b : ℚ} (h1 : avoids a b 1 = true) (h3 : avoids a b 3 = true)
    {x y : ℝ} (ha : (a : ℝ) ≤ x) (hxy : x ≤ y) (hb : y ≤ b) : Real.tan x ≤ Real.tan y := by
  have hc : ∀ z ∈ Set.Icc (a : ℝ) b, Real.cos z ≠ 0 := fun z hz => cos_ne_of_avoids h1 h3 hz.1 hz.2
  have hmono : MonotoneOn Real.tan (Set.Icc (a : ℝ) b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (Real.continuousOn_tan.mono (fun z hz => hc z hz)) ?_ ?_
    · intro z hz
      rw [interior_Icc] at hz
      exact (Real.hasDerivAt_tan (hc z (Set.Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(Real.hasDerivAt_tan (hc z (Set.Ioo_subset_Icc_self hz))).deriv]
      positivity
  exact hmono ⟨ha, hxy.trans hb⟩ ⟨ha.trans hxy, hb⟩ hxy

/-- `tan` interval enclosure (every real member whose cosine is nonzero; at a pole
    `Real.tan = 0`, also covered when the interval is the whole line). -/
theorem tan_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.tan x ∈ (Interval64.tan X).toSet := by
  unfold Interval64.tan
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rcases hlo : bitsToRat? X.lo.toBits with _ | qa
  · exact mem_toSet_whole _
  rcases hhi : bitsToRat? X.hi.toBits with _ | qb
  · exact mem_toSet_whole _
  dsimp only
  split_ifs with hav
  · simp only [Bool.and_eq_true] at hav
    have hea := bitsToEVal_rat_of_bitsToRat? hlo
    have heb := bitsToEVal_rat_of_bitsToRat? hhi
    have hqa : (qa : ℝ) ≤ x := by have := hx.1; rw [hea] at this; exact this
    have hqb : x ≤ (qb : ℝ) := by have := hx.2; rw [heb] at this; exact this
    exact ⟨loR_mono (tanDown_loR hea) (tan_mono_of_avoids hav.1 hav.2 le_rfl hqa hqb),
      hiR_mono (tanUp_hiR heb) (tan_mono_of_avoids hav.1 hav.2 hqa hqb le_rfl)⟩
  · exact mem_toSet_whole _

end RealFP.Tan
