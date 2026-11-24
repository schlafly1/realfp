/-
The error function as a realfp extension: the first function plugged in through the
registry (`RealFPMathlib/Registry.lean`), with no change to the tactics.

Mathlib has no `erf`, so it is defined here by its integral,
`erf x = 2/√π · ∫₀ˣ e^{-t²} dt`, and everything is proved from that definition:

* `erf_hasDerivAt` : `erf' x = 2/√π · e^{-x²}` (fundamental theorem of calculus);
* `erf_monotone`, `erf_neg` (odd), `neg_one_le_erf`, `erf_le_one` (Gaussian integral);
* `Erf.alt_bound` : the Taylor polynomials of `e^{-u}` alternate around it for `u ≥ 0`
  (remainder sign, by induction on the degree), so the integrated polynomials
  `Σ_{k ≤ n} (-1)^k x^{2k+1}/(k!(2k+1))` bound `∫₀ˣ e^{-t²}` from below (`n` odd) and above
  (`n` even) for every `x ≥ 0`;
* `erfLo`/`erfHi` : rational point bounds (input rounded to `2^-30`, odd symmetry, enough terms
  for `|x| ≤ 6`, clamped above), `erfExt := ExtFn.ofMono …` and `erf_sound`, tagged
  `@[realfp_fn]`.

After this, `RealFP.erf` can be used in `interval`, `realfp`, `root_exists`, `root_unique`,
`integral_bound`, `#realfp_min`, … like a built-in function.
-/
import RealFPMathlib.Registry
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

open Real intervalIntegral MeasureTheory Set
open Interval64.KF

namespace RealFP

/-- The error function, `erf x = 2/√π · ∫₀ˣ e^{-t²} dt` (Mathlib has none). -/
noncomputable def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

namespace Erf

/-- `Φ x = ∫₀ˣ e^{-t²}`. -/
noncomputable def Φ (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

theorem erf_eq (x : ℝ) : erf x = 2 / √π * Φ x := rfl

theorem cont : Continuous fun t : ℝ => exp (-t ^ 2) := by fun_prop

theorem hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (exp (-x ^ 2)) x :=
  (cont.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem Φ_zero : Φ 0 = 0 := integral_same

theorem Φ_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Φ x :=
  integral_nonneg hx fun _ _ => (exp_pos _).le

theorem Φ_neg (x : ℝ) : Φ (-x) = -Φ x := by
  unfold Φ
  have h := integral_comp_neg (a := 0) (b := -x) (fun t : ℝ => exp (-t ^ 2))
  simp only [neg_sq, neg_neg, neg_zero] at h
  rw [h, integral_symm]

theorem Φ_le {x : ℝ} : Φ x ≤ √π / 2 := by
  rcases le_or_gt 0 x with hx | hx
  · have hi : IntegrableOn (fun t : ℝ => exp (-t ^ 2)) (Ioi 0) := by
      have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi 0)
      simpa using this
    calc Φ x = ∫ t in Ioc 0 x, exp (-t ^ 2) := integral_of_le hx
      _ ≤ ∫ t in Ioi 0, exp (-t ^ 2) :=
          setIntegral_mono_set hi (Filter.Eventually.of_forall fun _ => (exp_pos _).le)
            (Filter.Eventually.of_forall fun _ h => h.1)
      _ = √π / 2 := by simpa using integral_gaussian_Ioi 1
  · have : Φ x ≤ 0 := by
      have := Φ_nonneg (neg_nonneg.2 hx.le); rw [Φ_neg] at this; linarith
    have : 0 ≤ √π / 2 := by positivity
    linarith

end Erf

open Erf

theorem erf_hasDerivAt (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x :=
  (hasDerivAt_Φ x).const_mul _

/-- `erf` is continuous (registered for `fun_prop`/`continuity`, used by the optimisation
forms of `realfp`). -/
@[fun_prop, continuity] theorem continuous_erf : Continuous erf :=
  continuous_iff_continuousAt.2 fun x => (erf_hasDerivAt x).continuousAt

theorem erf_monotone : Monotone erf :=
  monotone_of_deriv_nonneg (fun x => (erf_hasDerivAt x).differentiableAt)
    fun x => by rw [(erf_hasDerivAt x).deriv]; positivity

theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  rw [erf_eq, erf_eq, Φ_neg]; ring

theorem erf_le_one (x : ℝ) : erf x ≤ 1 := by
  have hp : 0 < √π := sqrt_pos.2 pi_pos
  rw [erf_eq]
  calc 2 / √π * Φ x ≤ 2 / √π * (√π / 2) := by gcongr; exact Φ_le
    _ = 1 := by field_simp

theorem neg_one_le_erf (x : ℝ) : -1 ≤ erf x := by
  have := erf_le_one (-x); rw [erf_neg] at this; linarith

theorem erf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ erf x := by
  rw [erf_eq]; exact mul_nonneg (by positivity) (Φ_nonneg hx)

namespace Erf

/-! ### Taylor bounds -/

/-- Taylor polynomial of `e^{-u}` of degree `n`. -/
noncomputable def S (n : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Finset.range (n + 1), (-u) ^ k / k.factorial

theorem hasDerivAt_T (k : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => (-y) ^ (k + 1) / (k + 1).factorial) (-((-u) ^ k / k.factorial)) u := by
  have h := ((hasDerivAt_neg u).pow (k + 1)).div_const ((k + 1).factorial : ℝ)
  convert h using 1
  rw [Nat.factorial_succ]; push_cast
  field_simp

theorem hasDerivAt_S (n : ℕ) (u : ℝ) : HasDerivAt (S (n + 1)) (-S n u) u := by
  have hS : S (n + 1) = fun y : ℝ => 1 + ∑ k ∈ Finset.range (n + 1), (-y) ^ (k + 1) / (k + 1).factorial := by
    funext y; unfold S; rw [Finset.sum_range_succ']; simp [add_comm]
  rw [hS]
  have := (HasDerivAt.sum (u := Finset.range (n + 1)) fun k _ => hasDerivAt_T k u).const_add 1
  convert this using 1
  · funext y; simp
  · unfold S; rw [← Finset.sum_neg_distrib]

theorem hasDerivAt_S0 (u : ℝ) : HasDerivAt (S 0) 0 u := by
  have : S 0 = fun _ => 1 := by funext y; simp [S]
  rw [this]; exact hasDerivAt_const _ _

theorem S_zero (n : ℕ) : S n 0 = 1 := by
  unfold S; rw [Finset.sum_range_succ']; simp

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_deriv {F F' : ℝ → ℝ} (h0 : F 0 = 0) (hd : ∀ x, HasDerivAt F (F' x) x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ F' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F x := by
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]; exact hpos y (le_of_lt hy)
  have := hm (Set.mem_Ici.2 (le_refl (0:ℝ))) hx hx
  rw [h0] at this; exact this

/-- The Taylor remainder of `e^{-u}` has the sign of `(-1)^{n+1}` for `u ≥ 0`. -/
theorem alt_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (-1) ^ (n + 1) * (exp (-u) - S n u) := by
  induction n generalizing u with
  | zero =>
    have : S 0 u = 1 := by simp [S]
    rw [this]
    have h1 : exp (-u) ≤ 1 := exp_le_one_iff.2 (by linarith)
    have h2 : (-1 : ℝ) ^ (0 + 1) * (exp (-u) - 1) = 1 - exp (-u) := by ring
    rw [h2]; linarith
  | succ n ih =>
    apply nonneg_of_deriv (F' := fun y => (-1) ^ (n + 1) * (exp (-y) - S n y)) _ _ _ hu
    · simp [S_zero]
    · intro y
      have h := (((hasDerivAt_neg y).exp).sub (hasDerivAt_S n y)).const_mul ((-1 : ℝ) ^ (n + 1 + 1))
      convert h using 1
      ring
    · exact fun y hy => ih hy

/-- Integrated Taylor polynomial: `P n x = ∫₀ˣ S n (t²) dt`. -/
noncomputable def P (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * x ^ (2 * k + 1) / (k.factorial * (2 * k + 1))

theorem hasDerivAt_P (n : ℕ) (x : ℝ) : HasDerivAt (P n) (S n (x ^ 2)) x := by
  unfold P S
  have : ∀ k ∈ Finset.range (n + 1), HasDerivAt
      (fun y : ℝ => (-1) ^ k * y ^ (2 * k + 1) / (k.factorial * (2 * k + 1)))
      ((-(x ^ 2)) ^ k / k.factorial) x := by
    intro k _
    have h := (((hasDerivAt_id x).pow (2 * k + 1)).const_mul ((-1 : ℝ) ^ k)).div_const
      ((k.factorial : ℝ) * (2 * k + 1))
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    convert h using 1
    · funext y; simp
    · simp only [id, Nat.add_sub_cancel]
      rw [neg_pow, ← pow_mul]
      push_cast
      field_simp
  convert HasDerivAt.sum this using 1
  funext y; simp

theorem P_zero (n : ℕ) : P n 0 = 0 := by simp [P]

/-- `(-1)^{n+1} (Φ x - P n x) ≥ 0` for `x ≥ 0`. -/
theorem Φ_P (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (-1) ^ (n + 1) * (Φ x - P n x) := by
  apply nonneg_of_deriv (F' := fun y => (-1) ^ (n + 1) * (exp (-y ^ 2) - S n (y ^ 2))) _ _ _ hx
  · simp [Φ_zero, P_zero]
  · intro y; exact ((hasDerivAt_Φ y).sub (hasDerivAt_P n y)).const_mul _
  · intro y _; exact alt_bound n (sq_nonneg y)

theorem P_le_Φ (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : P (2 * m + 1) x ≤ Φ x := by
  have h := Φ_P (2 * m + 1) hx
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul] at h
  simp at h; linarith

theorem Φ_le_P (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : Φ x ≤ P (2 * m) x := by
  have h := Φ_P (2 * m) hx
  rw [pow_succ, pow_mul] at h
  simp at h; linarith

/-! ### Rational point bounds (computable) -/

/-- `P n` on rationals (structural recursion, cheap in the kernel). -/
def Pq : ℕ → ℚ → ℚ
  | 0, x => x
  | n + 1, x => Pq n x + (-1) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
      ((n + 1).factorial * (2 * (n + 1) + 1))

theorem Pq_eq (n : ℕ) (x : ℚ) : ((Pq n x : ℚ) : ℝ) = P n x := by
  induction n with
  | zero => simp [Pq, P]
  | succ n ih =>
    rw [Pq, P, Finset.sum_range_succ, ← P, ← ih]; push_cast; ring

/-- Lower bound of `2/√π`. -/
def cLo : ℚ := 2 / 1.7724538509055161
/-- Upper bound of `2/√π`. -/
def cHi : ℚ := 2 / 1.7724538509055160

theorem sqrt_pi_lo : ((1.7724538509055160 : ℚ) : ℝ) ≤ √π := by
  apply le_sqrt_of_sq_le
  have := pi_gt_d20
  push_cast; nlinarith

theorem sqrt_pi_hi : √π ≤ ((1.7724538509055161 : ℚ) : ℝ) := by
  apply sqrt_le_iff.2
  have := pi_lt_d20
  refine ⟨by norm_num, ?_⟩
  push_cast; nlinarith

theorem cLo_le : (cLo : ℝ) ≤ 2 / √π := by
  have h := sqrt_pi_hi
  have hp : 0 < √π := sqrt_pos.2 pi_pos
  unfold cLo; push_cast at h ⊢
  exact div_le_div_of_nonneg_left (by norm_num) hp h

theorem le_cHi : 2 / √π ≤ (cHi : ℝ) := by
  have h := sqrt_pi_lo
  unfold cHi; push_cast at h ⊢
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h

/-- Number of Taylor pairs used at `r` (`2m+1` terms; any value is sound). -/
def nTerms (r : ℚ) : ℕ := ⌈2 * r * r⌉.toNat + 10

/-- Lower bound of `erf r` for `0 ≤ r` (clamped at `6`). -/
def loPos (r : ℚ) : ℚ := let r := min r 6; cLo * max 0 (Pq (2 * nTerms r + 1) r)

/-- Upper bound of `erf r` for `0 ≤ r`. -/
def hiPos (r : ℚ) : ℚ := if 6 ≤ r then 1 else min 1 (cHi * Pq (2 * nTerms r) r)

theorem loPos_le {r : ℚ} (hr : 0 ≤ r) : (loPos r : ℝ) ≤ erf r := by
  unfold loPos
  set r' := min r 6
  have h0 : (0 : ℝ) ≤ r' := by exact_mod_cast le_min hr (by norm_num)
  have hle : (r' : ℝ) ≤ r := by exact_mod_cast min_le_left r 6
  refine le_trans ?_ (erf_monotone hle)
  rw [erf_eq]
  have hP := P_le_Φ (nTerms r') h0
  rw [← Pq_eq] at hP
  have hΦ := Φ_nonneg h0
  have hc := cLo_le
  have hc0 : (0 : ℝ) ≤ cLo := by unfold cLo; norm_num
  push_cast
  calc (cLo : ℝ) * max 0 (Pq (2 * nTerms r' + 1) r' : ℝ) ≤ cLo * Φ r' :=
        mul_le_mul_of_nonneg_left (max_le hΦ hP) hc0
    _ ≤ 2 / √π * Φ r' := mul_le_mul_of_nonneg_right hc hΦ

theorem le_hiPos {r : ℚ} (hr : 0 ≤ r) : erf r ≤ (hiPos r : ℝ) := by
  unfold hiPos
  split_ifs
  · push_cast; exact erf_le_one _
  · have h0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    refine le_min (erf_le_one _) ?_
    rw [erf_eq]
    have hP := Φ_le_P (nTerms r) h0
    rw [← Pq_eq] at hP
    have hΦ := Φ_nonneg h0
    calc 2 / √π * Φ r ≤ cHi * Φ r := mul_le_mul_of_nonneg_right le_cHi hΦ
      _ ≤ cHi * (Pq (2 * nTerms r) r : ℝ) :=
          mul_le_mul_of_nonneg_left hP (le_trans (by positivity) le_cHi)

/-- `q` rounded down / up to a multiple of `2^-30` (keeps the kernel's rationals small). -/
def rdn (q : ℚ) : ℚ := (⌊q * 2 ^ 30⌋ : ℚ) / 2 ^ 30
def rup (q : ℚ) : ℚ := (⌈q * 2 ^ 30⌉ : ℚ) / 2 ^ 30

theorem rdn_le (q : ℚ) : rdn q ≤ q := by
  unfold rdn; rw [div_le_iff₀ (by norm_num)]; exact Int.floor_le _

theorem le_rup (q : ℚ) : q ≤ rup q := by
  unfold rup; rw [le_div_iff₀ (by norm_num)]; exact Int.le_ceil _

theorem rdn_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ rdn q := by
  unfold rdn; apply div_nonneg _ (by norm_num)
  exact_mod_cast Int.floor_nonneg.2 (by positivity)

theorem rup_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ rup q := h.trans (le_rup q)

end Erf

open Erf

/-- Rational lower bound of `erf q`. -/
def erfLo (q : ℚ) : ℚ := if 0 ≤ q then loPos (rdn q) else -hiPos (rup (-q))

/-- Rational upper bound of `erf q`. -/
def erfHi (q : ℚ) : ℚ := if 0 ≤ q then hiPos (rup q) else -loPos (rdn (-q))

theorem erfLo_le (q : ℚ) : (erfLo q : ℝ) ≤ erf q := by
  unfold erfLo
  split_ifs with h
  · exact (loPos_le (rdn_nonneg h)).trans (erf_monotone (by exact_mod_cast rdn_le q))
  · have h' : 0 ≤ -q := by linarith
    have := (erf_monotone (show ((-q : ℚ) : ℝ) ≤ rup (-q) by exact_mod_cast le_rup _)).trans
      (le_hiPos (rup_nonneg h'))
    push_cast at this ⊢
    rw [erf_neg] at this; linarith

theorem le_erfHi (q : ℚ) : erf q ≤ (erfHi q : ℝ) := by
  unfold erfHi
  split_ifs with h
  · exact (erf_monotone (by exact_mod_cast le_rup q)).trans (le_hiPos (rup_nonneg h))
  · have h' : 0 ≤ -q := by linarith
    have := (loPos_le (rdn_nonneg h')).trans
      (erf_monotone (show ((rdn (-q) : ℚ) : ℝ) ≤ ((-q : ℚ) : ℝ) by exact_mod_cast rdn_le _))
    push_cast at this ⊢
    rw [erf_neg] at this; linarith

/-- Derivative template `2/√π · exp(-x²)` (built-in functions only). -/
def erfDeriv : IExpr := .mul (.div (.rat 2) (.sqrt .pi)) (.exp (.neg (.pow (.var 0) 2)))

/-- The kernel implementation of `erf`: monotone, from the rational point bounds. -/
def erfExt : ExtFn :=
  ExtFn.ofMono "erf" erfLo erfHi (-1) 1 (fun _ => true) erfDeriv

/-- `erfExt` is a sound implementation of `erf`; registers `erf` for all realfp tactics. -/
@[realfp_fn] theorem erf_sound : ExtSound erf (fun _ => True) erfExt :=
  ExtSound.ofMono erf_monotone erfLo_le le_erfHi
    (fun x => by push_cast; exact neg_one_le_erf x) (fun x => by push_cast; exact erf_le_one x)
    (fun _ _ _ _ _ _ _ => trivial) rfl
    (fun x _ => by simpa [erfDeriv, IExpr.denoteB] using erf_hasDerivAt x)

end RealFP
