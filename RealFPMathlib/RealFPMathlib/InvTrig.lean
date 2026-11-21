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
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open Interval64 Interval64.Spec Interval64.Transc Interval64.Trig Interval64.InvTrig
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits

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

end RealFP.InvTrig
