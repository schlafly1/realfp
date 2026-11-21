/-
Real enclosures for the directed `atan` / `atan2` and `π` of `Interval64.InvTrig`.

* `atanCheck_spec` : the `sin`/`cos` certificate implies `a ≤ arctan q ≤ b`.
* `arctan_series_bounds` : `x - x³/3 ≤ arctan x ≤ x - x³/3 + x⁵/5` for `x ≥ 0`.
* `atanBounds_spec`, `atan2Bounds_spec` : the rational enclosures.
* `arg_eq_arctan_of_re_pos`, `arg_eq_pi_div_two_sub_arctan`, … : `Complex.arg` via `arctan`.
* `atanDown_loR`, `atanUp_hiR`, `atan2Down_le`, `le_atan2Up` : pointwise.
* `pi_mem_toSet`, `atan_mem_toSet`, `atan2_mem_toSet` : interval enclosures.
-/
import RealFPMathlib.Trig
import RealFPMathlib.Unbounded
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open Interval64 Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Pow2

namespace RealFP.InvTrig

open RealFP.Transc RealFP.Trig

/-! ### Analytic facts -/

theorem one_lt_pi_div_two : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]

/-- `a ≤ arctan q` from `sin a ≤ q cos a`, `|a| ≤ 1`. -/
theorem le_arctan_of_sin_le {a q : ℝ} (ha0 : -1 ≤ a) (ha1 : a ≤ 1)
    (h : Real.sin a ≤ q * Real.cos a) : a ≤ Real.arctan q := by
  have h1 := one_lt_pi_div_two
  have hc : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ht : Real.tan a ≤ q := by rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hc]; exact h
  calc a = Real.arctan (Real.tan a) := (Real.arctan_tan (by linarith) (by linarith)).symm
    _ ≤ Real.arctan q := Real.arctan_mono ht

theorem arctan_le_of_le_sin {b q : ℝ} (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (h : q * Real.cos b ≤ Real.sin b) : Real.arctan q ≤ b := by
  have h1 := one_lt_pi_div_two
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ht : q ≤ Real.tan b := by rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc]; exact h
  calc Real.arctan q ≤ Real.arctan (Real.tan b) := Real.arctan_mono ht
    _ = b := Real.arctan_tan (by linarith) (by linarith)

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y).deriv]; exact hd y (le_of_lt hy)
  have := hmono (Set.mem_Ici.2 le_rfl) hx hx
  rw [← h0]; exact this

theorem arctan_series_bounds {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x ∧ Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  constructor
  · have := nonneg_of_deriv_nonneg (f := fun t => Real.arctan t - (t - t ^ 3 / 3))
      (f' := fun t => 1 / (1 + t ^ 2) - (1 - t ^ 2))
      (fun t => by
        have := (Real.hasDerivAt_arctan t).sub
          ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3))
        convert this using 1
        · funext u; simp only [Pi.sub_apply, Pi.add_apply, id]
        · push_cast; ring)
      (by simp)
      (fun t _ => by
        have hp : 0 < 1 + t ^ 2 := by positivity
        rw [sub_nonneg, le_div_iff₀ hp]
        nlinarith [sq_nonneg (t ^ 2)]) hx
    linarith
  · have := nonneg_of_deriv_nonneg (f := fun t => (t - t ^ 3 / 3 + t ^ 5 / 5) - Real.arctan t)
      (f' := fun t => (1 - t ^ 2 + t ^ 4) - 1 / (1 + t ^ 2))
      (fun t => by
        have := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).add
          ((hasDerivAt_pow 5 t).div_const 5)).sub (Real.hasDerivAt_arctan t)
        convert this using 1
        · funext u; simp only [Pi.sub_apply, Pi.add_apply, id]
        · push_cast; ring)
      (by simp)
      (fun t _ => by
        have hp : 0 < 1 + t ^ 2 := by positivity
        rw [sub_nonneg, div_le_iff₀ hp]
        nlinarith [sq_nonneg (t ^ 3), sq_nonneg t]) hx
    linarith

theorem abs_arctan_lt_two (x : ℝ) : -2 ≤ Real.arctan x ∧ Real.arctan x ≤ 2 := by
  have := Real.arctan_lt_pi_div_two x
  have := Real.neg_pi_div_two_lt_arctan x
  have := Real.pi_lt_four
  constructor <;> linarith

/-! ### Rational enclosures -/

theorem atanCheck_spec {q a b : ℚ} {p : ℕ} (hq : 0 ≤ q) (h : atanCheck q a b p = true) :
    (a : ℝ) ≤ Real.arctan q ∧ Real.arctan q ≤ b := by
  unfold atanCheck at h
  obtain ⟨ha0, hab, hb1, hsa, hsb⟩ := of_decide_eq_true h
  obtain ⟨⟨-, sa⟩, ⟨ca, -⟩⟩ := trigBounds_spec a p
  obtain ⟨⟨sb, -⟩, ⟨-, cb⟩⟩ := trigBounds_spec b p
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have ha0' : (-1 : ℝ) ≤ a := by exact_mod_cast ha0
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsa' : ((trigBounds a p).1.2 : ℝ) ≤ q * (trigBounds a p).2.1 := by exact_mod_cast hsa
  have hsb' : (q : ℝ) * (trigBounds b p).2.2 ≤ (trigBounds b p).1.1 := by exact_mod_cast hsb
  constructor
  · apply le_arctan_of_sin_le ha0' (by linarith)
    have := mul_le_mul_of_nonneg_left ca hq'
    linarith
  · apply arctan_le_of_le_sin (by linarith) hb1'
    have := mul_le_mul_of_nonneg_left cb hq'
    linarith

theorem atanSmallBounds_spec {q : ℚ} (hq : 0 ≤ q) (p : ℕ) :
    ((atanSmallBounds q p).1 : ℝ) ≤ Real.arctan q ∧ Real.arctan q ≤ (atanSmallBounds q p).2 := by
  unfold atanSmallBounds
  dsimp only
  split
  · have := arctan_series_bounds (x := (q : ℝ)) (by exact_mod_cast hq)
    push_cast; exact this
  · split
    · exact atanCheck_spec hq (by assumption)
    · push_cast; exact abs_arctan_lt_two _

theorem atanBounds_spec (q : ℚ) (p : ℕ) :
    ((atanBounds q p).1 : ℝ) ≤ Real.arctan q ∧ Real.arctan q ≤ (atanBounds q p).2 := by
  have pos : ∀ r : ℚ, 0 ≤ r →
      ((if r = 0 then ((0 : ℚ), (0 : ℚ)) else if r ≤ 1 then atanSmallBounds r p else
        ((piBounds p false).1 / 2 - (atanSmallBounds (1 / r) p).2,
         (piBounds p false).2 / 2 - (atanSmallBounds (1 / r) p).1)).1 : ℝ) ≤ Real.arctan r ∧
      Real.arctan r ≤ ((if r = 0 then ((0 : ℚ), (0 : ℚ)) else if r ≤ 1 then atanSmallBounds r p else
        ((piBounds p false).1 / 2 - (atanSmallBounds (1 / r) p).2,
         (piBounds p false).2 / 2 - (atanSmallBounds (1 / r) p).1)).2 : ℝ) := by
    intro r hr
    split
    · subst_vars; simp
    · split
      · exact atanSmallBounds_spec hr p
      · rename_i h0 h1
        have hr1 : (1 : ℚ) < r := lt_of_not_ge h1
        have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_trans one_pos hr1)
        obtain ⟨l, u⟩ := atanSmallBounds_spec (q := 1 / r) (by positivity) p
        obtain ⟨pl, pu⟩ := piBounds_spec p false
        have key : Real.arctan r = Real.pi / 2 - Real.arctan ((r : ℝ)⁻¹) := by
          have := Real.arctan_inv_of_pos (inv_pos.2 hrpos)
          rw [inv_inv] at this; exact this
        push_cast at l u ⊢
        rw [key, ← one_div]
        constructor <;> linarith
  unfold atanBounds
  dsimp only
  have hq := pos (ratAbs' q) (by rw [ratAbs'_eq]; exact abs_nonneg q)
  split
  · rename_i hneg
    have : (ratAbs' q : ℝ) = -(q : ℝ) := by
      rw [ratAbs'_eq, abs_of_neg hneg]; push_cast; ring
    rw [this, Real.arctan_neg] at hq
    push_cast
    constructor <;> linarith [hq.1, hq.2]
  · rename_i hneg
    have : (ratAbs' q : ℝ) = (q : ℝ) := by
      rw [ratAbs'_eq, abs_of_nonneg (le_of_not_gt hneg)]
    rw [this] at hq
    exact hq

theorem piMul_spec (c : ℚ) (p : ℕ) :
    ((piMul c p).1 : ℝ) ≤ c * Real.pi ∧ c * Real.pi ≤ (piMul c p).2 := by
  unfold piMul
  obtain ⟨pl, pu⟩ := piBounds_spec p false
  split
  · rename_i hc
    have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left pl hc', mul_le_mul_of_nonneg_left pu hc'⟩
  · rename_i hc
    have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left pu hc', mul_le_mul_of_nonpos_left pl hc'⟩

/-! ### `Complex.arg` through `arctan` -/

open Complex in
theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h))
  rw [← Complex.tan_arg, Real.arctan_tan ha.1 ha.2]

open Complex in
theorem arg_eq_arctan_add_pi {z : ℂ} (hre : z.re < 0) (him : 0 < z.im) :
    arg z = Real.arctan (z.im / z.re) + Real.pi := by
  have h1 : Real.pi / 2 < arg z := by
    have hn : ¬ |arg z| ≤ Real.pi / 2 := fun h => absurd (Complex.abs_arg_le_pi_div_two_iff.1 h) (not_le.2 hre)
    have h0 : 0 ≤ arg z := Complex.arg_nonneg_iff.2 him.le
    rw [abs_of_nonneg h0] at hn; exact lt_of_not_ge hn
  have h2 : arg z < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi z)
    (fun h => by have := (Complex.arg_eq_pi_iff.1 h).2; linarith)
  have ht : Real.tan (arg z - Real.pi) = z.im / z.re := by
    rw [Real.tan_periodic.sub_eq, Complex.tan_arg]
  rw [← ht, Real.arctan_tan (by linarith) (by linarith)]; ring

open Complex in
theorem arg_eq_arctan_sub_pi {z : ℂ} (hre : z.re < 0) (him : z.im < 0) :
    arg z = Real.arctan (z.im / z.re) - Real.pi := by
  have h1 : arg z < -(Real.pi / 2) := by
    have hn : ¬ |arg z| ≤ Real.pi / 2 := fun h => absurd (Complex.abs_arg_le_pi_div_two_iff.1 h) (not_le.2 hre)
    have h0 : arg z < 0 := Complex.arg_neg_iff.2 him
    rw [abs_of_neg h0] at hn; linarith [lt_of_not_ge hn]
  have h2 : -Real.pi < arg z := Complex.neg_pi_lt_arg z
  have ht : Real.tan (arg z + Real.pi) = z.im / z.re := by
    rw [Real.tan_periodic, Complex.tan_arg]
  rw [← ht, Real.arctan_tan (by linarith) (by linarith)]; ring

theorem re_xy (x y : ℝ) : ((x : ℂ) + y * Complex.I).re = x := by simp
theorem im_xy (x y : ℝ) : ((x : ℂ) + y * Complex.I).im = y := by simp

/-- Upper half-plane: `arg (x + y i) = π/2 - arctan (x/y)`. -/
theorem arg_upper {x y : ℝ} (hy : 0 < y) :
    Complex.arg (x + y * Complex.I) = Real.pi / 2 - Real.arctan (x / y) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [arg_eq_arctan_add_pi (by rw [re_xy]; exact hx) (by rw [im_xy]; exact hy), re_xy, im_xy]
    have := Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hx hy)
    rw [inv_div] at this; rw [this]; ring
  · have : ((0 : ℝ) : ℂ) + y * Complex.I = (y : ℂ) * Complex.I := by simp
    rw [this, Complex.arg_real_mul _ hy, Complex.arg_I]; simp
  · rw [arg_eq_arctan_of_re_pos (by rw [re_xy]; exact hx), re_xy, im_xy]
    have := Real.arctan_inv_of_pos (div_pos hx hy)
    rw [inv_div] at this; exact this

/-- Lower half-plane: `arg (x + y i) = -π/2 - arctan (x/y)`. -/
theorem arg_lower {x y : ℝ} (hy : y < 0) :
    Complex.arg (x + y * Complex.I) = -(Real.pi / 2) - Real.arctan (x / y) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [arg_eq_arctan_sub_pi (by rw [re_xy]; exact hx) (by rw [im_xy]; exact hy), re_xy, im_xy]
    have := Real.arctan_inv_of_pos (div_pos_of_neg_of_neg hx hy)
    rw [inv_div] at this; rw [this]; ring
  · have : ((0 : ℝ) : ℂ) + y * Complex.I = ((-y : ℝ) : ℂ) * (-Complex.I) := by push_cast; ring
    rw [this, Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]; simp
  · rw [arg_eq_arctan_of_re_pos (by rw [re_xy]; exact hx), re_xy, im_xy]
    have := Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hx hy)
    rw [inv_div] at this; exact this

/-- Right half-plane. -/
theorem arg_right {x y : ℝ} (hx : 0 < x) :
    Complex.arg (x + y * Complex.I) = Real.arctan (y / x) := by
  rw [arg_eq_arctan_of_re_pos (by rw [re_xy]; exact hx), re_xy, im_xy]

theorem atan2Bounds_spec {y x : ℚ} (hy : y ≠ 0) (p : ℕ) :
    ((atan2Bounds y x p).1 : ℝ) ≤ Complex.arg (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) ∧
      Complex.arg (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) ≤ (atan2Bounds y x p).2 := by
  unfold atan2Bounds
  dsimp only
  split
  · rename_i hx0
    subst hx0
    have hm := piMul_spec (if 0 < y then 1 / 2 else -1 / 2) p
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have : ¬ (0 < y) := not_lt.2 hneg.le
      simp only [this, ↓reduceIte] at hm ⊢
      have := arg_lower (x := 0) (y := (y : ℝ)) (by exact_mod_cast hneg)
      push_cast at hm this ⊢; rw [this]; simp only [zero_div, Real.arctan_zero, sub_zero]
      constructor <;> linarith [hm.1, hm.2]
    · simp only [hpos, ↓reduceIte] at hm ⊢
      have := arg_upper (x := 0) (y := (y : ℝ)) (by exact_mod_cast hpos)
      push_cast at hm this ⊢; rw [this]; simp only [zero_div, Real.arctan_zero, sub_zero]
      constructor <;> linarith [hm.1, hm.2]
  · rename_i hx0
    have ht := atanBounds_spec (y / x) p
    push_cast at ht
    split
    · rename_i hxp
      rw [arg_right (by exact_mod_cast hxp)]; exact ht
    · rename_i hxp
      have hxn : (x : ℝ) < 0 := by
        have : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
        exact_mod_cast this
      have hm := piMul_spec (if 0 < y then 1 else -1) p
      rcases lt_or_gt_of_ne hy with hneg | hpos
      · have : ¬ (0 < y) := not_lt.2 hneg.le
        simp only [this, ↓reduceIte] at hm ⊢
        rw [arg_eq_arctan_sub_pi (by rw [re_xy]; exact hxn) (by rw [im_xy]; exact_mod_cast hneg),
          re_xy, im_xy]
        push_cast at hm ⊢
        constructor <;> linarith [hm.1, hm.2, ht.1, ht.2]
      · simp only [hpos, ↓reduceIte] at hm ⊢
        rw [arg_eq_arctan_add_pi (by rw [re_xy]; exact hxn) (by rw [im_xy]; exact_mod_cast hpos),
          re_xy, im_xy]
        push_cast at hm ⊢
        constructor <;> linarith [hm.1, hm.2, ht.1, ht.2]

/-! ### Pointwise directed atan / atan2 -/

theorem atanRat_down (q : ℚ) : loR (bitsToEVal (rndD (atanBounds q) false).1) (Real.arctan q) := by
  unfold rndD; simp only [Bool.false_eq_true, ↓reduceIte]
  exact zivDown_loR (fun p => (atanBounds_spec q p).1)

theorem atanRat_up (q : ℚ) : hiR (bitsToEVal (rndD (atanBounds q) true).1) (Real.arctan q) := by
  unfold rndD; simp only [↓reduceIte]
  exact zivUp_hiR (fun p => (atanBounds_spec q p).2)

theorem rndD_down_loR {f : ℕ → ℚ × ℚ} {y : ℝ} (hf : ∀ p, ((f p).1 : ℝ) ≤ y) :
    loR (bitsToEVal (rndD f false).1) y := by
  unfold rndD; simp only [Bool.false_eq_true, ↓reduceIte]; exact zivDown_loR hf

theorem rndD_up_hiR {f : ℕ → ℚ × ℚ} {y : ℝ} (hf : ∀ p, y ≤ ((f p).2 : ℝ)) :
    hiR (bitsToEVal (rndD f true).1) y := by
  unfold rndD; simp only [↓reduceIte]; exact zivUp_hiR hf

theorem atanDownBits_loR {b : UInt64} {x : ℝ} (h : loR (bitsToEVal b) x) :
    loR (bitsToEVal (atanDownBits b)) (Real.arctan x) := by
  unfold atanDownBits atanBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, loR] at h
  | infinity s =>
    cases s with
    | negative =>
      dsimp only
      refine rndD_down_loR (fun p => ?_)
      have := (piMul_spec (-1 / 2) p).1
      have := Real.neg_pi_div_two_lt_arctan x
      push_cast at *; linarith
    | positive => simp [bitsToEVal, hu, toEVal, loR] at h
  | zero s =>
    have h0 : (0 : ℝ) ≤ x := by simpa [bitsToEVal, hu, toEVal, loR] using h
    simpa [bitsToEVal, hu, toEVal, loR] using Real.arctan_nonneg.2 h0
  | finite s m e hm =>
    have hq : ((signedVal s m e : ℚ) : ℝ) ≤ x := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact loR_mono (atanRat_down _) (Real.arctan_mono hq)

theorem atanUpBits_hiR {b : UInt64} {x : ℝ} (h : hiR (bitsToEVal b) x) :
    hiR (bitsToEVal (atanUpBits b)) (Real.arctan x) := by
  unfold atanUpBits atanBitsD
  cases hu : unpackBits b with
  | notANumber => simp [bitsToEVal, hu, toEVal, hiR] at h
  | infinity s =>
    cases s with
    | negative => simp [bitsToEVal, hu, toEVal, hiR] at h
    | positive =>
      dsimp only
      refine rndD_up_hiR (fun p => ?_)
      have := (piMul_spec (1 / 2) p).2
      have := Real.arctan_lt_pi_div_two x
      push_cast at *; linarith
  | zero s =>
    have h0 : x ≤ 0 := by simpa [bitsToEVal, hu, toEVal, hiR] using h
    simpa [bitsToEVal, hu, toEVal, hiR] using Real.arctan_le_zero.2 h0
  | finite s m e hm =>
    have hq : x ≤ ((signedVal s m e : ℚ) : ℝ) := by
      rw [bitsToEVal_of_finite hu] at h; exact h
    simp only [bitsToRat?_of_finite hu]
    exact hiR_mono (atanRat_up _) (Real.arctan_mono hq)

/-- `atanDown` is a lower bound for `arctan` (any input, extended reals). -/
theorem atanDown_loR {a : Float} {x : ℝ} (h : loR (bitsToEVal a.toBits) x) :
    loR (bitsToEVal (Directed.atanDown a).toBits) (Real.arctan x) :=
  loR_ofBits (atanDownBits_loR h)

/-- `atanUp` is an upper bound for `arctan` (any input, extended reals). -/
theorem atanUp_hiR {a : Float} {x : ℝ} (h : hiR (bitsToEVal a.toBits) x) :
    hiR (bitsToEVal (Directed.atanUp a).toBits) (Real.arctan x) :=
  hiR_ofBits (atanUpBits_hiR h)

theorem signedVal_pos {m : ℕ} {e : ℤ} (hm : 0 < m) : (0 : ℝ) < ((signedVal .positive m e : ℚ) : ℝ) := by
  have : ((signedVal .positive m e : ℚ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    simp [signedVal, Interval64Proofs.Pow2.mag, pow2_cast]
  rw [this]; have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem signedVal_neg' {m : ℕ} {e : ℤ} (hm : 0 < m) : ((signedVal .negative m e : ℚ) : ℝ) < 0 := by
  rw [signedVal_neg]; push_cast; linarith [signedVal_pos (e := e) hm]

theorem bitsToEVal_zeroBits (s : Float.Model.UnpackedFloat.Sign) :
    bitsToEVal (zeroBits s) = some (.rat 0) := by
  cases s <;> decide

theorem arg_xy_rat_zero {x : ℝ} (hx : 0 < x) : Complex.arg ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = 0 := by
  simp [Complex.arg_ofReal_of_nonneg hx.le]

/-- Pointwise: `atan2Down y x ≤ arg (x + y i)` for finite `y`, `x` (values `qy`, `qx`) off the
    branch-cut convention cases (`qy ≠ 0` or `qx > 0`). -/
theorem atan2Down_loR {y x : Float} {qy qx : ℚ} (hy : bitsToEVal y.toBits = some (.rat qy))
    (hx : bitsToEVal x.toBits = some (.rat qx)) (h : qy ≠ 0 ∨ 0 < qx) :
    loR (bitsToEVal (Directed.atan2Down y x).toBits)
      (Complex.arg (((qx : ℝ) : ℂ) + ((qy : ℝ) : ℂ) * Complex.I)) := by
  apply loR_ofBits
  unfold atan2DownBits atan2BitsD
  cases hu : unpackBits y.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at hy
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at hy
  | zero sy =>
    have hqy : qy = 0 := zero_of_unpack_zero hu hy
    have hqx : 0 < qx := by rcases h with h | h; exact absurd hqy h; exact h
    cases hv : unpackBits x.toBits with
    | notANumber => simp [bitsToEVal, hv, toEVal] at hx
    | infinity s => cases s <;> simp [bitsToEVal, hv, toEVal] at hx
    | zero sx => have := zero_of_unpack_zero hv hx; subst this; exact absurd hqx (lt_irrefl _)
    | finite sx m e hm =>
      have hv' := val_of_unpack_finite hv hx
      cases sx with
      | negative =>
        have := signedVal_neg' (e := e) hm; rw [hv'] at this
        have : (0 : ℝ) < qx := by exact_mod_cast hqx
        linarith
      | positive =>
        simp only [isNeg, Bool.false_eq_true, ↓reduceIte]
        rw [bitsToEVal_zeroBits, hqy]
        have : (0 : ℝ) < (qx : ℝ) := by exact_mod_cast hqx
        simp only [Rat.cast_zero, Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.arg_ofReal_of_nonneg this.le]; simp
  | finite sy my ey hmy =>
    have hy' := val_of_unpack_finite hu hy
    cases hv : unpackBits x.toBits with
    | notANumber => simp [bitsToEVal, hv, toEVal] at hx
    | infinity s => cases s <;> simp [bitsToEVal, hv, toEVal] at hx
    | zero sx =>
      have hqx := zero_of_unpack_zero hv hx
      dsimp only
      refine rndD_down_loR (fun p => ?_)
      have hm := (piMul_spec (sgnQ sy / 2) p).1
      rw [hqx]
      cases sy with
      | positive =>
        have hp := signedVal_pos (e := ey) hmy; rw [hy'] at hp
        rw [arg_upper hp]; simp [sgnQ] at hm ⊢; linarith
      | negative =>
        have hp := signedVal_neg' (e := ey) hmy; rw [hy'] at hp
        rw [arg_lower hp]; simp [sgnQ] at hm ⊢; linarith
    | finite sx mx ex hmx =>
      have hx' := val_of_unpack_finite hv hx
      dsimp only
      simp only [bitsToRat?_of_finite hu, bitsToRat?_of_finite hv]
      rw [hy', hx']
      have hqy : qy ≠ 0 := by
        intro h0
        cases sy with
        | positive => have := signedVal_pos (e := ey) hmy; rw [hy', h0] at this; simp at this
        | negative => have := signedVal_neg' (e := ey) hmy; rw [hy', h0] at this; simp at this
      exact rndD_down_loR (fun p => (atan2Bounds_spec hqy p).1)

/-- Pointwise: `arg (x + y i) ≤ atan2Up y x` for finite `y`, `x` (values `qy`, `qx`) off the
    branch-cut convention cases (`qy ≠ 0` or `qx > 0`). -/
theorem atan2Up_hiR {y x : Float} {qy qx : ℚ} (hy : bitsToEVal y.toBits = some (.rat qy))
    (hx : bitsToEVal x.toBits = some (.rat qx)) (h : qy ≠ 0 ∨ 0 < qx) :
    hiR (bitsToEVal (Directed.atan2Up y x).toBits)
      (Complex.arg (((qx : ℝ) : ℂ) + ((qy : ℝ) : ℂ) * Complex.I)) := by
  apply hiR_ofBits
  unfold atan2UpBits atan2BitsD
  cases hu : unpackBits y.toBits with
  | notANumber => simp [bitsToEVal, hu, toEVal] at hy
  | infinity s => cases s <;> simp [bitsToEVal, hu, toEVal] at hy
  | zero sy =>
    have hqy : qy = 0 := zero_of_unpack_zero hu hy
    have hqx : 0 < qx := by rcases h with h | h; exact absurd hqy h; exact h
    cases hv : unpackBits x.toBits with
    | notANumber => simp [bitsToEVal, hv, toEVal] at hx
    | infinity s => cases s <;> simp [bitsToEVal, hv, toEVal] at hx
    | zero sx => have := zero_of_unpack_zero hv hx; subst this; exact absurd hqx (lt_irrefl _)
    | finite sx m e hm =>
      have hv' := val_of_unpack_finite hv hx
      cases sx with
      | negative =>
        have := signedVal_neg' (e := e) hm; rw [hv'] at this
        have : (0 : ℝ) < qx := by exact_mod_cast hqx
        linarith
      | positive =>
        simp only [isNeg, Bool.false_eq_true, ↓reduceIte]
        rw [bitsToEVal_zeroBits, hqy]
        have : (0 : ℝ) < (qx : ℝ) := by exact_mod_cast hqx
        simp only [Rat.cast_zero, Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.arg_ofReal_of_nonneg this.le]; simp
  | finite sy my ey hmy =>
    have hy' := val_of_unpack_finite hu hy
    cases hv : unpackBits x.toBits with
    | notANumber => simp [bitsToEVal, hv, toEVal] at hx
    | infinity s => cases s <;> simp [bitsToEVal, hv, toEVal] at hx
    | zero sx =>
      have hqx := zero_of_unpack_zero hv hx
      dsimp only
      refine rndD_up_hiR (fun p => ?_)
      have hm := (piMul_spec (sgnQ sy / 2) p).2
      rw [hqx]
      cases sy with
      | positive =>
        have hp := signedVal_pos (e := ey) hmy; rw [hy'] at hp
        rw [arg_upper hp]; simp [sgnQ] at hm ⊢; linarith
      | negative =>
        have hp := signedVal_neg' (e := ey) hmy; rw [hy'] at hp
        rw [arg_lower hp]; simp [sgnQ] at hm ⊢; linarith
    | finite sx mx ex hmx =>
      have hx' := val_of_unpack_finite hv hx
      dsimp only
      simp only [bitsToRat?_of_finite hu, bitsToRat?_of_finite hv]
      rw [hy', hx']
      have hqy : qy ≠ 0 := by
        intro h0
        cases sy with
        | positive => have := signedVal_pos (e := ey) hmy; rw [hy', h0] at this; simp at this
        | negative => have := signedVal_neg' (e := ey) hmy; rw [hy', h0] at this; simp at this
      exact rndD_up_hiR (fun p => (atan2Bounds_spec hqy p).2)

/-! ### Interval enclosures -/

theorem ofBits_down_loR {c : ℚ} {y : ℝ} (h : (c : ℝ) ≤ y) :
    loR (bitsToEVal (Float.ofBits (ofRatDown c)).toBits) y := loR_ofBits (ofRatDown_loR h)

theorem ofBits_up_hiR {c : ℚ} {y : ℝ} (h : y ≤ (c : ℝ)) :
    hiR (bitsToEVal (Float.ofBits (ofRatUp c)).toBits) y := hiR_ofBits (ofRatUp_hiR h)

/-- `π ∈ Interval64.pi`. -/
theorem pi_mem_toSet : Real.pi ∈ Interval64.pi.toSet := by
  obtain ⟨l, u⟩ := piBounds_spec 128 false
  exact ⟨ofBits_down_loR l, ofBits_up_hiR u⟩

theorem halfPi_mem_toSet : Real.pi / 2 ∈ halfPi.toSet := by
  obtain ⟨l, u⟩ := piBounds_spec 128 false
  exact ⟨ofBits_down_loR (by push_cast; linarith), ofBits_up_hiR (by push_cast; linarith)⟩

theorem negHalfPi_mem_toSet : -(Real.pi / 2) ∈ negHalfPi.toSet := by
  obtain ⟨l, u⟩ := piBounds_spec 128 false
  exact ⟨ofBits_down_loR (by push_cast; linarith), ofBits_up_hiR (by push_cast; linarith)⟩

theorem arg_mem_argHull (z : ℂ) : Complex.arg z ∈ argHull.toSet := by
  obtain ⟨l, u⟩ := piBounds_spec 128 false
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  exact ⟨ofBits_down_loR (by push_cast; linarith), ofBits_up_hiR (by push_cast; linarith)⟩

/-- `atan` interval enclosure (any interval, extended endpoints). -/
theorem atan_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) :
    Real.arctan x ∈ (Interval64.atan X).toSet := by
  unfold Interval64.atan
  rw [isNaN_false_of_loR hx.1, isNaN_false_of_hiR hx.2]
  exact ⟨atanDown_loR hx.1, atanUp_hiR hx.2⟩

/-- `atan2` interval enclosure: `Complex.arg (x + y i) ∈ atan2 Y X` for every `x ∈ X`,
    `y ∈ Y` (C argument order; boxes meeting the branch cut give `[-π, π]`). -/
theorem atan2_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) ∈ (Interval64.atan2 Y X).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan Y X = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  unfold Interval64.atan2
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : X.lo > 0
  · simp only [h1, decide_true, ↓reduceIte]
    have h0 : (0 : EReal) < X.lo.toE := (zero_lt_iff_toE hXl).1 h1
    have hxp : 0 < x := EReal.coe_pos.1 (lt_of_lt_of_le h0 hXl')
    rw [arg_right hxp]
    exact atan_mem_toSet (mem_toSet_div hy hx hxp.ne')
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : Y.lo > 0
    · simp only [h2, decide_true, ↓reduceIte]
      have h0 : (0 : EReal) < Y.lo.toE := (zero_lt_iff_toE hYl).1 h2
      have hyp : 0 < y := EReal.coe_pos.1 (lt_of_lt_of_le h0 hYl')
      rw [arg_upper hyp]
      exact sub_mem_toSet halfPi_mem_toSet (atan_mem_toSet (mem_toSet_div hx hy hyp.ne'))
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : Y.hi < 0
      · simp only [h3, decide_true, ↓reduceIte]
        have h0 : Y.hi.toE < (0 : EReal) := (lt_zero_iff_toE hYh).1 h3
        have hyn : y < 0 := EReal.coe_neg'.1 (lt_of_le_of_lt hYh' h0)
        rw [arg_lower hyn]
        exact sub_mem_toSet negHalfPi_mem_toSet (atan_mem_toSet (mem_toSet_div hx hy hyn.ne))
      · simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact arg_mem_argHull _

end RealFP.InvTrig
