/-
Real enclosures for the directed `asin`, `acos` of `Interval64.Asin` and the intervals.
-/
import RealFPMathlib.Tan
import Interval64.Asin

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

end RealFP.Asin
