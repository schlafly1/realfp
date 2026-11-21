/-
Real enclosures for the directed `sin` / `cos` of `Interval64.Trig`.

* `trigSmall_spec` : Taylor enclosures for `|r| ≤ 1` (from `Complex.exp_bound`).
* `piCheck_spec`, `piBounds_spec` : the certified rational enclosures of `π`.
* `trigBounds_spec` : argument reduction + quadrant + Lipschitz widening.
* `sinDown_loR` … `cosUp_hiR` : pointwise (finite input).
* `sin_mem_toSet`, `cos_mem_toSet` : interval enclosure (any interval).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import RealFPMathlib.Transc
import Interval64Proofs.Div

open Interval64 Interval64.Spec Interval64.Transc Interval64.Trig
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pow2
open Finset Complex

namespace RealFP.Trig

open RealFP.Transc

/-! ### Taylor enclosures -/

theorem cisTaylor_eq (r : ℚ) (n : ℕ) :
    (((cisTaylor r n).1 : ℚ) : ℂ) + (((cisTaylor r n).2 : ℚ) : ℂ) * I =
      ∑ m ∈ range n, ((r : ℂ) * I) ^ m / m.factorial := by
  induction n with
  | zero => simp [cisTaylor]
  | succ n ih =>
    rw [sum_range_succ, ← ih, mul_pow, I_pow_eq_pow_mod]
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    simp only [cisTaylor]
    rcases h4 with h | h | h | h <;> simp [h, fact_eq, pow_succ] <;> ring

theorem trigSmall_spec {r : ℚ} (hr : |r| ≤ 1) {n : ℕ} (hn : 0 < n) :
    ((trigSmall r n).sl : ℝ) ≤ Real.sin r ∧ Real.sin r ≤ (trigSmall r n).sh ∧
    ((trigSmall r n).cl : ℝ) ≤ Real.cos r ∧ Real.cos r ≤ (trigSmall r n).ch := by
  have hr' : |(r : ℝ)| ≤ 1 := by
    have : ((|r| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hr
    rwa [Rat.cast_abs, Rat.cast_one] at this
  have hnorm : ‖(r : ℂ) * I‖ = |(r : ℝ)| := by simp
  have hb := Complex.exp_bound (x := (r : ℂ) * I) (by rw [hnorm]; exact hr') hn
  rw [hnorm, ← cisTaylor_eq] at hb
  have hexp : Complex.exp ((r : ℂ) * I) = (Real.cos r : ℂ) + (Real.sin r : ℂ) * I := by
    rw [Complex.exp_mul_I]; push_cast; ring_nf
  rw [hexp] at hb
  set D := ((Real.cos r : ℂ) + (Real.sin r : ℂ) * I) -
    ((((cisTaylor r n).1 : ℚ) : ℂ) + (((cisTaylor r n).2 : ℚ) : ℂ) * I) with hD
  have hre : D.re = Real.cos r - (cisTaylor r n).1 := by
    rw [hD]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im]
    ring
  have him : D.im = Real.sin r - (cisTaylor r n).2 := by
    rw [hD]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im]
    ring
  have h1 := Complex.abs_re_le_norm D
  have h2 := Complex.abs_im_le_norm D
  have he : (expErr (ratAbs' r) n : ℝ) = |(r : ℝ)| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
    simp [expErr, fact_eq, ratAbs'_eq, div_eq_mul_inv]
  rw [hre] at h1; rw [him] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.mp (le_trans h1 hb)
  obtain ⟨h2a, h2b⟩ := abs_le.mp (le_trans h2 hb)
  rw [← he] at h1a h1b h2a h2b
  simp only [trigSmall]
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem trigTerms_pos (p : ℕ) : 0 < trigTerms p := by unfold trigTerms; omega

/-! ### π -/

theorem piCheck_spec (P : ℕ) : ((piCheck P).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piCheck P).2 := by
  unfold piCheck
  dsimp only
  split_ifs with h
  · obtain ⟨h3a, hab, hb, hca, hca2, hcb, hcb2⟩ := h
    set a := floorP (machinPi P - 1 / 2 ^ P) P
    set b := ceilP (machinPi P + 1 / 2 ^ P) P
    have hn : 0 < P / 5 + 20 := by omega
    have hpi3 := Real.pi_gt_three
    have ha4 : |a / 4| ≤ 1 := by
      rw [abs_le]; constructor <;> [linarith; linarith]
    have hb4 : |b / 4| ≤ 1 := by
      rw [abs_le]; constructor <;> [linarith; linarith]
    obtain ⟨-, -, hca', -⟩ := trigSmall_spec ha4 hn
    obtain ⟨-, -, -, hcb'⟩ := trigSmall_spec hb4 hn
    push_cast at hca' hcb'
    have hA : (3 : ℝ) ≤ a := by exact_mod_cast h3a
    have hB : (b : ℝ) ≤ 63 / 20 := by
      have := Rat.cast_le (K := ℝ) |>.mpr hb; push_cast at this; exact this
    have hAB : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hpi4 := Real.pi_lt_d2
    constructor
    · -- `cos (a/2) = 2 cos² (a/4) - 1 > 0` forces `a < π`
      have hca0 : (0 : ℝ) < (trigSmall (a / 4) (P / 5 + 20)).cl := by exact_mod_cast hca
      have hca2' : (1 : ℝ) < 2 * (trigSmall (a / 4) (P / 5 + 20)).cl * (trigSmall (a / 4) (P / 5 + 20)).cl := by
        exact_mod_cast hca2
      have hcos : 0 < Real.cos ((a : ℝ) / 2) := by
        have e : (a : ℝ) / 2 = 2 * ((a : ℝ) / 4) := by ring
        rw [e, Real.cos_two_mul]
        have := mul_le_mul hca' hca' hca0.le (le_trans hca0.le hca')
        nlinarith
      by_contra hlt
      rw [not_le] at hlt
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := (a : ℝ) / 2) (by linarith) (by linarith)
      linarith
    · -- `cos (b/2) = 2 cos² (b/4) - 1 < 0` forces `b > π`
      have hcb0 : (0 : ℝ) ≤ Real.cos ((b : ℝ) / 4) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have hcb2' : 2 * ((trigSmall (b / 4) (P / 5 + 20)).ch : ℝ) * (trigSmall (b / 4) (P / 5 + 20)).ch < 1 := by
        exact_mod_cast hcb2
      have hcos : Real.cos ((b : ℝ) / 2) < 0 := by
        have e : (b : ℝ) / 2 = 2 * ((b : ℝ) / 4) := by ring
        rw [e, Real.cos_two_mul]
        have := mul_le_mul hcb' hcb' hcb0 (le_trans hcb0 hcb')
        nlinarith
      by_contra hlt
      rw [not_le] at hlt
      have := Real.cos_nonneg_of_mem_Icc (x := (b : ℝ) / 2) ⟨by linarith, by linarith⟩
      linarith
  · constructor
    · push_cast; linarith [Real.pi_gt_three]
    · push_cast; linarith [Real.pi_lt_d2]


theorem piCache_get {i : ℕ} {t : Thunk (ℚ × ℚ)} (h : piCache[i]? = some t) :
    ∃ P, t.get = piCheck P := by
  unfold piCache at h
  simp only [Array.getElem?_map, List.getElem?_toArray] at h
  obtain ⟨j, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨_, rfl⟩

theorem piBounds_spec (p : ℕ) (big : Bool) :
    ((piBounds p big).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piBounds p big).2 := by
  unfold piBounds
  split_ifs
  · split
    · rename_i t ht
      obtain ⟨P, hP⟩ := piCache_get ht
      rw [hP]; exact piCheck_spec P
    · exact piCheck_spec _
  · exact piCheck_spec _

/-! ### Quadrants -/

theorem sin_add_three_pi_div_two (x : ℝ) : Real.sin (x + 3 * (Real.pi / 2)) = -Real.cos x := by
  rw [show x + 3 * (Real.pi / 2) = (x + Real.pi / 2) + Real.pi by ring, Real.sin_add_pi,
    Real.sin_add_pi_div_two]

theorem cos_add_three_pi_div_two (x : ℝ) : Real.cos (x + 3 * (Real.pi / 2)) = Real.sin x := by
  rw [show x + 3 * (Real.pi / 2) = (x + Real.pi / 2) + Real.pi by ring, Real.cos_add_pi,
    Real.cos_add_pi_div_two, neg_neg]

/-- `q = r + k π/2` reduces to the quadrant `k mod 4`. -/
theorem sin_cos_quadrant (r : ℝ) (k : ℤ) :
    (Real.sin (r + k * (Real.pi / 2)) = Real.sin (r + (k % 4 : ℤ) * (Real.pi / 2))) ∧
    (Real.cos (r + k * (Real.pi / 2)) = Real.cos (r + (k % 4 : ℤ) * (Real.pi / 2))) := by
  have hk : (k : ℝ) = (k % 4 : ℤ) + (k / 4 : ℤ) * 4 := by
    have h : k = k % 4 + k / 4 * 4 := by omega
    exact_mod_cast h
  have e : r + k * (Real.pi / 2) = (r + (k % 4 : ℤ) * (Real.pi / 2)) + (k / 4 : ℤ) * (2 * Real.pi) := by
    rw [hk]; ring
  rw [e, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

theorem quad_cases (k : ℤ) : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega

theorem quadSin_spec {t : TB} {r0 r : ℝ} {w : ℚ} (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3)
    (hw : |r - r0| ≤ w)
    (hs1 : (t.sl : ℝ) ≤ Real.sin r0) (hs2 : Real.sin r0 ≤ t.sh)
    (hc1 : (t.cl : ℝ) ≤ Real.cos r0) (hc2 : Real.cos r0 ≤ t.ch) :
    ((quadSin t j w).1 : ℝ) ≤ Real.sin (r + j * (Real.pi / 2)) ∧
      Real.sin (r + j * (Real.pi / 2)) ≤ (quadSin t j w).2 := by
  have hs := abs_le.mp (le_trans (Real.abs_sin_sub_sin_le r r0) hw)
  have hc := abs_le.mp (le_trans (Real.abs_cos_sub_cos_le r r0) hw)
  unfold quadSin
  rcases hj with h | h | h | h <;> subst h <;> simp
  · constructor <;> linarith
  · rw [Real.sin_add_pi_div_two]; constructor <;> linarith
  · rw [show r + 2 * (Real.pi / 2) = r + Real.pi by ring, Real.sin_add_pi]
    constructor <;> linarith
  · rw [sin_add_three_pi_div_two]; constructor <;> linarith

theorem quadCos_spec {t : TB} {r0 r : ℝ} {w : ℚ} (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3)
    (hw : |r - r0| ≤ w)
    (hs1 : (t.sl : ℝ) ≤ Real.sin r0) (hs2 : Real.sin r0 ≤ t.sh)
    (hc1 : (t.cl : ℝ) ≤ Real.cos r0) (hc2 : Real.cos r0 ≤ t.ch) :
    ((quadCos t j w).1 : ℝ) ≤ Real.cos (r + j * (Real.pi / 2)) ∧
      Real.cos (r + j * (Real.pi / 2)) ≤ (quadCos t j w).2 := by
  have hs := abs_le.mp (le_trans (Real.abs_sin_sub_sin_le r r0) hw)
  have hc := abs_le.mp (le_trans (Real.abs_cos_sub_cos_le r r0) hw)
  unfold quadCos
  rcases hj with h | h | h | h <;> subst h <;> simp
  · constructor <;> linarith
  · rw [Real.cos_add_pi_div_two]; constructor <;> linarith
  · rw [show r + 2 * (Real.pi / 2) = r + Real.pi by ring, Real.cos_add_pi]
    constructor <;> linarith
  · rw [cos_add_three_pi_div_two]; constructor <;> linarith


/-! ### Argument reduction -/

theorem trigBounds_spec (q : ℚ) (p : ℕ) :
    (((trigBounds q p).1.1 : ℝ) ≤ Real.sin q ∧ Real.sin q ≤ (trigBounds q p).1.2) ∧
    (((trigBounds q p).2.1 : ℝ) ≤ Real.cos q ∧ Real.cos q ≤ (trigBounds q p).2.2) := by
  unfold trigBounds
  dsimp only
  by_cases hs : ratAbs' q ≤ 3 / 4
  · simp only [hs, ↓reduceIte]
    rw [ratAbs'_eq] at hs
    obtain ⟨a, b, c, d⟩ := trigSmall_spec (by linarith : |q| ≤ 1) (trigTerms_pos p)
    exact ⟨⟨a, b⟩, ⟨c, d⟩⟩
  · simp only [hs, ↓reduceIte]
    generalize hpb : piBounds p (!decide (ratAbs' q < 2 ^ 30)) = pb
    have hpi : (pb.1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ pb.2 := hpb ▸ piBounds_spec p _
    generalize (q * 4 / (pb.1 + pb.2) + 1 / 2).floor = k
    set r : ℝ := (q : ℝ) - k * (Real.pi / 2) with hr
    generalize hrl : (if 0 ≤ k then q - k * pb.2 / 2 else q - k * pb.1 / 2) = rl
    generalize hrh : (if 0 ≤ k then q - k * pb.1 / 2 else q - k * pb.2 / 2) = rh
    have hbounds : (rl : ℝ) ≤ r ∧ r ≤ rh := by
      rw [← hrl, ← hrh]
      by_cases hk : 0 ≤ k
      · simp only [hk, ↓reduceIte]
        have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
        have h1 := mul_le_mul_of_nonneg_left hpi.1 hk'
        have h2 := mul_le_mul_of_nonneg_left hpi.2 hk'
        push_cast
        constructor <;> linarith
      · simp only [hk, ↓reduceIte]
        have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hk).le
        have h1 := mul_le_mul_of_nonpos_left hpi.1 hk'
        have h2 := mul_le_mul_of_nonpos_left hpi.2 hk'
        push_cast
        constructor <;> linarith
    have hr0 : ((floorP rl (p + 40) : ℚ) : ℝ) ≤ rl := by exact_mod_cast floorP_le rl (p + 40)
    have hw : |r - (floorP rl (p + 40) : ℚ)| ≤ (((rh - floorP rl (p + 40)) : ℚ) : ℝ) := by
      rw [abs_le]; push_cast; constructor <;> linarith [hbounds.1, hbounds.2]
    have hq : ((q : ℚ) : ℝ) = r + k * (Real.pi / 2) := by rw [hr]; ring
    by_cases h1 : ratAbs' (floorP rl (p + 40)) ≤ 1
    · simp only [h1, ↓reduceIte]
      rw [ratAbs'_eq] at h1
      obtain ⟨a, b, c, d⟩ := trigSmall_spec h1 (trigTerms_pos p)
      rw [hq, (sin_cos_quadrant r k).1, (sin_cos_quadrant r k).2]
      exact ⟨quadSin_spec _ (quad_cases k) hw a b c d, quadCos_spec _ (quad_cases k) hw a b c d⟩
    · simp only [h1, ↓reduceIte]
      push_cast
      exact ⟨⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩, ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩⟩


/-! ### Pointwise directed sin / cos -/

theorem sinRat_down (q : ℚ) : loR (bitsToEVal (sinRat q false).1) (Real.sin q) := by
  unfold sinRat; simp only [Bool.false_eq_true, ↓reduceIte]
  exact zivDown_loR (fun p => (trigBounds_spec q p).1.1)

theorem sinRat_up (q : ℚ) : hiR (bitsToEVal (sinRat q true).1) (Real.sin q) := by
  unfold sinRat; simp only [↓reduceIte]
  exact zivUp_hiR (fun p => (trigBounds_spec q p).1.2)

theorem cosRat_down (q : ℚ) : loR (bitsToEVal (cosRat q false).1) (Real.cos q) := by
  unfold cosRat; simp only [Bool.false_eq_true, ↓reduceIte]
  exact zivDown_loR (fun p => (trigBounds_spec q p).2.1)

theorem cosRat_up (q : ℚ) : hiR (bitsToEVal (cosRat q true).1) (Real.cos q) := by
  unfold cosRat; simp only [↓reduceIte]
  exact zivUp_hiR (fun p => (trigBounds_spec q p).2.2)

theorem zero_of_unpack_zero {b : UInt64} {s : Float.Model.UnpackedFloat.Sign} {q : ℚ}
    (hu : unpackBits b = .zero s) (h : bitsToEVal b = some (.rat q)) : q = 0 := by
  simp [bitsToEVal, hu, toEVal] at h; exact h.symm

theorem val_of_unpack_finite {b : UInt64} {s : Float.Model.UnpackedFloat.Sign} {m : ℕ} {e : ℤ}
    {hm : 0 < m} {q : ℚ} (hu : unpackBits b = .finite s m e hm) (h : bitsToEVal b = some (.rat q)) :
    signedVal s m e = q := by
  rw [bitsToEVal_of_finite hu] at h; simpa using h

/-- `sinDown a ≤ sin a` for a finite double `a` (value `q`). -/
theorem sinDown_loR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    loR (bitsToEVal (Directed.sinDown a).toBits) (Real.sin q) := by
  apply loR_ofBits
  unfold sinDownBits sinBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show loR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact sinRat_down _

theorem sinUp_hiR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    hiR (bitsToEVal (Directed.sinUp a).toBits) (Real.sin q) := by
  apply hiR_ofBits
  unfold sinUpBits sinBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    show hiR (bitsToEVal a.toBits) _
    rw [h, zero_of_unpack_zero hu h]; simp
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact sinRat_up _

theorem cosDown_loR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    loR (bitsToEVal (Directed.cosDown a).toBits) (Real.cos q) := by
  apply loR_ofBits
  unfold cosDownBits cosBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [zero_of_unpack_zero hu h]
    exact ofRatDown_loR (by simp)
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact cosRat_down _

theorem cosUp_hiR {a : Float} {q : ℚ} (h : bitsToEVal a.toBits = some (.rat q)) :
    hiR (bitsToEVal (Directed.cosUp a).toBits) (Real.cos q) := by
  apply hiR_ofBits
  unfold cosUpBits cosBitsD
  cases hu : unpackBits a.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at h
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at h
  | zero s =>
    simp only [↓reduceIte]
    rw [zero_of_unpack_zero hu h]
    exact ofRatUp_hiR (by simp)
  | finite s m e hm =>
    simp only [bitsToRat?_of_finite hu]
    rw [← val_of_unpack_finite hu h]; exact cosRat_up _


/-! ### `fmin` / `fmax` against real bounds -/

theorem loR_exists_rat {v : Option EVal} {x : ℝ} (h : loR v x) :
    ∃ z : ℚ, loEncloses? v z ∧ (z : ℝ) ≤ x := by
  rcases v with _ | (_ | r | _)
  · exact h.elim
  · exact ⟨⌊x⌋, by simp [loEncloses?, loEncloses], by push_cast; exact Int.floor_le x⟩
  · exact ⟨r, by simp [loEncloses?, loEncloses], h⟩
  · exact h.elim

theorem hiR_exists_rat {v : Option EVal} {x : ℝ} (h : hiR v x) :
    ∃ z : ℚ, hiEncloses? v z ∧ x ≤ (z : ℝ) := by
  rcases v with _ | (_ | r | _)
  · exact h.elim
  · exact h.elim
  · exact ⟨r, by simp [hiEncloses?, hiEncloses], h⟩
  · exact ⟨⌈x⌉, by simp [hiEncloses?, hiEncloses], by push_cast; exact Int.le_ceil x⟩

theorem loR_fmin {a b : Float} {xa xb z : ℝ} (ha : loR (bitsToEVal a.toBits) xa)
    (hb : loR (bitsToEVal b.toBits) xb) (hz : min xa xb ≤ z) :
    loR (bitsToEVal (fmin a b).toBits) z := by
  obtain ⟨za, hza, hza'⟩ := loR_exists_rat ha
  obtain ⟨zb, hzb, hzb'⟩ := loR_exists_rat hb
  have h := Interval64Proofs.Div.loEncloses_fmin hza hzb (le_refl _)
  rw [← loR_cast] at h
  apply loR_mono h
  have h1 : ((Interval64Proofs.IntervalMem.rmin za zb : ℚ) : ℝ) ≤ za := by
    exact_mod_cast Interval64Proofs.IntervalMem.rmin_le_left za zb
  have h2 : ((Interval64Proofs.IntervalMem.rmin za zb : ℚ) : ℝ) ≤ zb := by
    exact_mod_cast Interval64Proofs.IntervalMem.rmin_le_right za zb
  calc _ ≤ min (za : ℝ) zb := le_min h1 h2
    _ ≤ min xa xb := min_le_min hza' hzb'
    _ ≤ z := hz

theorem hiR_fmax {a b : Float} {xa xb z : ℝ} (ha : hiR (bitsToEVal a.toBits) xa)
    (hb : hiR (bitsToEVal b.toBits) xb) (hz : z ≤ max xa xb) :
    hiR (bitsToEVal (fmax a b).toBits) z := by
  obtain ⟨za, hza, hza'⟩ := hiR_exists_rat ha
  obtain ⟨zb, hzb, hzb'⟩ := hiR_exists_rat hb
  have h := Interval64Proofs.Div.hiEncloses_fmax hza hzb (le_refl _)
  rw [← hiR_cast] at h
  apply hiR_mono h
  have h1 : (za : ℝ) ≤ ((Interval64Proofs.IntervalMem.rmax za zb : ℚ) : ℝ) := by
    exact_mod_cast Interval64Proofs.IntervalMem.le_rmax_left za zb
  have h2 : (zb : ℝ) ≤ ((Interval64Proofs.IntervalMem.rmax za zb : ℚ) : ℝ) := by
    exact_mod_cast Interval64Proofs.IntervalMem.le_rmax_right za zb
  calc z ≤ max xa xb := hz
    _ ≤ max (za : ℝ) zb := max_le_max hza' hzb'
    _ ≤ _ := max_le h1 h2

/-! ### Monotonicity between consecutive extrema -/

/-- On `[(4n+3)π/2, (4n+7)π/2]` (one period from a minimum to the next),
    `sin` is unimodal, so its minimum over `[a, b]` is at an endpoint. -/
theorem sin_min_le {a b x : ℝ} (n : ℤ) (ha : ((4 * n + 3 : ℤ) : ℝ) * (Real.pi / 2) ≤ a)
    (hb : b ≤ ((4 * n + 3 + 4 : ℤ) : ℝ) * (Real.pi / 2)) (hax : a ≤ x) (hxb : x ≤ b) :
    min (Real.sin a) (Real.sin b) ≤ Real.sin x := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((n + 1 : ℤ) : ℝ) * (2 * Real.pi) := ⟨_, rfl⟩
  have shift : ∀ y, Real.sin y = Real.sin (y - c) := fun y => by
    have := Real.sin_add_int_mul_two_pi (y - c) (n + 1)
    rw [← hc, sub_add_cancel] at this; exact this
  have e1 : ((4 * n + 3 : ℤ) : ℝ) * (Real.pi / 2) - c = -(Real.pi / 2) := by
    rw [hc]; push_cast; ring
  have e2 : ((4 * n + 3 + 4 : ℤ) : ℝ) * (Real.pi / 2) - c = 3 * (Real.pi / 2) := by
    rw [hc]; push_cast; ring
  have hpi := Real.pi_pos
  rw [shift a, shift b, shift x]
  rcases le_total (x - c) (Real.pi / 2) with hx | hx
  · exact (min_le_left _ _).trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx (by linarith))
  · refine (min_le_right _ _).trans ?_
    rw [← Real.sin_pi_sub (b - c), ← Real.sin_pi_sub (x - c)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

theorem sin_le_max {a b x : ℝ} (n : ℤ) (ha : ((4 * n + 1 : ℤ) : ℝ) * (Real.pi / 2) ≤ a)
    (hb : b ≤ ((4 * n + 1 + 4 : ℤ) : ℝ) * (Real.pi / 2)) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.sin x ≤ max (Real.sin a) (Real.sin b) := by
  have h := sin_min_le (a := a + Real.pi) (b := b + Real.pi) (x := x + Real.pi) n
    (by push_cast at ha ⊢; linarith) (by push_cast at hb ⊢; linarith) (by linarith) (by linarith)
  simp only [Real.sin_add_pi] at h
  rw [min_neg_neg] at h
  linarith

theorem cos_min_le {a b x : ℝ} (n : ℤ) (ha : ((4 * n + 2 : ℤ) : ℝ) * (Real.pi / 2) ≤ a)
    (hb : b ≤ ((4 * n + 2 + 4 : ℤ) : ℝ) * (Real.pi / 2)) (hax : a ≤ x) (hxb : x ≤ b) :
    min (Real.cos a) (Real.cos b) ≤ Real.cos x := by
  have h := sin_min_le (a := a + Real.pi / 2) (b := b + Real.pi / 2) (x := x + Real.pi / 2) n
    (by push_cast at ha ⊢; linarith) (by push_cast at hb ⊢; linarith) (by linarith) (by linarith)
  simpa only [Real.sin_add_pi_div_two] using h

theorem cos_le_max {a b x : ℝ} (n : ℤ) (ha : ((4 * n + 0 : ℤ) : ℝ) * (Real.pi / 2) ≤ a)
    (hb : b ≤ ((4 * n + 0 + 4 : ℤ) : ℝ) * (Real.pi / 2)) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.cos x ≤ max (Real.cos a) (Real.cos b) := by
  have h := sin_min_le (a := a + 3 * (Real.pi / 2)) (b := b + 3 * (Real.pi / 2))
    (x := x + 3 * (Real.pi / 2)) n
    (by push_cast at ha ⊢; linarith) (by push_cast at hb ⊢; linarith) (by linarith) (by linarith)
  simp only [sin_add_three_pi_div_two] at h
  rw [min_neg_neg] at h
  linarith

/-! ### Extremum-avoidance certificate -/

theorem halfPiMul_spec (m : ℤ) {pb : ℚ × ℚ} (hpi : (pb.1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ pb.2) :
    ((halfPiMul m pb).1 : ℝ) ≤ (m : ℝ) * (Real.pi / 2) ∧
      (m : ℝ) * (Real.pi / 2) ≤ (halfPiMul m pb).2 := by
  unfold halfPiMul
  by_cases hm : 0 ≤ m
  · simp only [hm, ↓reduceIte]
    have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
    have h1 := mul_le_mul_of_nonneg_left hpi.1 hm'
    have h2 := mul_le_mul_of_nonneg_left hpi.2 hm'
    push_cast
    constructor <;> linarith
  · simp only [hm, ↓reduceIte]
    have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hm).le
    have h1 := mul_le_mul_of_nonpos_left hpi.1 hm'
    have h2 := mul_le_mul_of_nonpos_left hpi.2 hm'
    push_cast
    constructor <;> linarith

theorem avoids_spec {a b : ℚ} {c : ℤ} (h : avoids a b c = true) :
    ∃ n : ℤ, ((4 * n + c : ℤ) : ℝ) * (Real.pi / 2) ≤ a ∧
      (b : ℝ) ≤ ((4 * n + c + 4 : ℤ) : ℝ) * (Real.pi / 2) := by
  unfold avoids at h
  dsimp only at h
  generalize hpb : piBounds 128 _ = pb at h
  have hpi : (pb.1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ pb.2 := hpb ▸ piBounds_spec _ _
  generalize (((a * 4 / (pb.1 + pb.2) - c) / 4).floor) = n at h
  rw [decide_eq_true_iff] at h
  refine ⟨n, ?_, ?_⟩
  · exact (halfPiMul_spec _ hpi).2.trans (by exact_mod_cast h.1)
  · exact (show (b : ℝ) ≤ _ by exact_mod_cast h.2).trans (halfPiMul_spec _ hpi).1

/-! ### Interval enclosures -/

theorem minusOne_loR {y : ℝ} (hy : -1 ≤ y) : loR (bitsToEVal minusOne.toBits) y :=
  loR_ofBits (ofRatDown_loR (by push_cast; exact hy))

theorem plusOne_hiR {y : ℝ} (hy : y ≤ 1) : hiR (bitsToEVal plusOne.toBits) y :=
  hiR_ofBits (ofRatUp_hiR (by push_cast; exact hy))

/-- `sin` interval enclosure: every real member `x` of `X` has `sin x ∈ sin X`. -/
theorem sin_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.sin x ∈ (Interval64.sin X).toSet := by
  unfold Interval64.sin
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hdef : Real.sin x ∈ (⟨minusOne, plusOne⟩ : Interval64).toSet :=
    ⟨minusOne_loR (Real.neg_one_le_sin x), plusOne_hiR (Real.sin_le_one x)⟩
  rcases hlo : bitsToRat? X.lo.toBits with _ | qa
  · exact hdef
  rcases hhi : bitsToRat? X.hi.toBits with _ | qb
  · exact hdef
  have hea := bitsToEVal_rat_of_bitsToRat? hlo
  have heb := bitsToEVal_rat_of_bitsToRat? hhi
  have hqa : (qa : ℝ) ≤ x := by have := hx.1; rw [hea] at this; exact this
  have hqb : x ≤ (qb : ℝ) := by have := hx.2; rw [heb] at this; exact this
  constructor
  · dsimp only
    split_ifs with hav
    · obtain ⟨n, h1, h2⟩ := avoids_spec hav
      exact loR_fmin (sinDown_loR hea) (sinDown_loR heb) (sin_min_le n h1 h2 hqa hqb)
    · exact minusOne_loR (Real.neg_one_le_sin x)
  · dsimp only
    split_ifs with hav
    · obtain ⟨n, h1, h2⟩ := avoids_spec hav
      exact hiR_fmax (sinUp_hiR hea) (sinUp_hiR heb) (sin_le_max n h1 h2 hqa hqb)
    · exact plusOne_hiR (Real.sin_le_one x)

/-- `cos` interval enclosure: every real member `x` of `X` has `cos x ∈ cos X`. -/
theorem cos_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.cos x ∈ (Interval64.cos X).toSet := by
  unfold Interval64.cos
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hdef : Real.cos x ∈ (⟨minusOne, plusOne⟩ : Interval64).toSet :=
    ⟨minusOne_loR (Real.neg_one_le_cos x), plusOne_hiR (Real.cos_le_one x)⟩
  rcases hlo : bitsToRat? X.lo.toBits with _ | qa
  · exact hdef
  rcases hhi : bitsToRat? X.hi.toBits with _ | qb
  · exact hdef
  have hea := bitsToEVal_rat_of_bitsToRat? hlo
  have heb := bitsToEVal_rat_of_bitsToRat? hhi
  have hqa : (qa : ℝ) ≤ x := by have := hx.1; rw [hea] at this; exact this
  have hqb : x ≤ (qb : ℝ) := by have := hx.2; rw [heb] at this; exact this
  constructor
  · dsimp only
    split_ifs with hav
    · obtain ⟨n, h1, h2⟩ := avoids_spec hav
      exact loR_fmin (cosDown_loR hea) (cosDown_loR heb) (cos_min_le n h1 h2 hqa hqb)
    · exact minusOne_loR (Real.neg_one_le_cos x)
  · dsimp only
    split_ifs with hav
    · obtain ⟨n, h1, h2⟩ := avoids_spec hav
      exact hiR_fmax (cosUp_hiR hea) (cosUp_hiR heb) (cos_le_max n h1 h2 hqa hqb)
    · exact plusOne_hiR (Real.cos_le_one x)

end RealFP.Trig
