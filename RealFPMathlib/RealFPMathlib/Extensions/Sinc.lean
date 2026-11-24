/-
`Real.sinc` (Mathlib: `sinc x = sin x / x`, `sinc 0 = 1`) as a realfp extension.

Enclosure of `sinc` on a box `X = [a, b]`:
* `X ⊆ [-3, 3]`: `sinc` is even and decreasing in `|x|` on `[0, π] ⊇ [0, 3]`, so the bounds come
  from point enclosures at the endpoints: the lower bound at the endpoint of larger `|·|`, the upper
  bound `1` if `0 ∈ X`, else at the endpoint of smaller `|·|`. The point enclosure is `[1, 1]` at
  `0` and the kernel's `sin q / q` elsewhere, so the removable singularity costs nothing and the
  relative error is a few ulps (no cancellation for `|q| ≤ 3`);
* `0 ∉ X` otherwise: the kernel's interval `sin x / x` on `X`;
* otherwise `[-1, 1]`.
Derivative `(x cos x - sin x)/x²`, valid for `x ≠ 0` only: the template is not defined at `0`, so
`domK` rejects boxes containing `0` and derivative-based modes (monotonicity, centred forms, Taylor
quadrature, Newton/Krawczyk) are unavailable there; zeroth-order (plain interval) modes still work.
-/
import RealFPMathlib.Registry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real Filter Topology
open Interval64 Interval64.KF

namespace RealFP.Sinc

theorem hasDerivAt_sinc {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sinc ((x * cos x - sin x) / x ^ 2) x := by
  have h := (hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have hev : sinc =ᶠ[𝓝 x] fun y => sin y / id y :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy => sinc_of_ne_zero hy
  convert h.congr_of_eventuallyEq hev using 1
  simp; ring

theorem sin_sub_mul_cos_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) : 0 ≤ sin x - x * cos x := by
  have := nonneg_of_hasDerivAt (F := fun y => sin y - y * cos y) (F' := fun y => y * sin y)
    (by simp)
    (fun y _ _ => by
      have := (hasDerivAt_sin y).sub ((hasDerivAt_id y).mul (hasDerivAt_cos y))
      convert this using 1
      · funext z; simp
      · simp)
    (fun y hy0 hy1 => mul_nonneg hy0 (sin_nonneg_of_nonneg_of_le_pi hy0 (hy1.trans h1))) h0
  simpa using this

theorem sinc_antitoneOn : AntitoneOn sinc (Set.Icc 0 π) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 π) continuous_sinc.continuousOn
  · intro y hy; rw [interior_Icc] at hy
    exact (hasDerivAt_sinc hy.1.ne').differentiableAt.differentiableWithinAt
  · intro y hy; rw [interior_Icc] at hy
    rw [(hasDerivAt_sinc hy.1.ne').deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg y)
    linarith [sin_sub_mul_cos_nonneg hy.1.le hy.2.le]

theorem sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; exact sinc_neg x

theorem sinc_le_of_abs {y z : ℝ} (hyz : |y| ≤ |z|) (hz : |z| ≤ 3) : sinc z ≤ sinc y := by
  rw [← sinc_abs z, ← sinc_abs y]
  have hp := pi_gt_three
  exact sinc_antitoneOn ⟨abs_nonneg y, by linarith⟩ ⟨abs_nonneg z, by linarith⟩ hyz

/-- `sin x / x`. -/
def g : IExpr := .div (.sin (.var 0)) (.var 0)

/-- Point enclosure of `sinc` at the bit pattern `b`. -/
def pt (b : Nat) : KI :=
  match ratOfBits b with
  | some q => if q = 0 then KI.ofRatInterval 1 1 else evalK [ptK b] g
  | none => KI.whole

theorem pt_mem {b : Nat} {q : ℚ} (hb : b < 2 ^ 64) (hq : ratOfBits b = some q) :
    sinc q ∈ (toI (pt b)).toSet := by
  unfold pt; rw [hq]; dsimp only
  split_ifs with h
  · rw [(KF.ofRatInterval_toI _ _).1]; subst h
    apply mem_toSet_ofRatInterval <;> simp
  · have := denote_mem_evalK_pt hb hq g
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast h
    rw [sinc_of_ne_zero hq0]; simpa [g, IExpr.denote] using this

/-- `[-1, 1]`. -/
def pm1 : KI := KI.ofRatInterval (-1) 1

theorem mem_pm1 (x : ℝ) : sinc x ∈ (toI pm1).toSet := by
  unfold pm1; rw [(KF.ofRatInterval_toI _ _).1]
  apply mem_toSet_ofRatInterval <;> push_cast
  · exact neg_one_le_sinc x
  · exact sinc_le_one x

/-- The interval extension of `sinc`. -/
def evK (X : KI) : KI :=
  match ratOfBits X.lo, ratOfBits X.hi with
  | some a, some c =>
    if -3 ≤ a ∧ c ≤ 3 then
      ⟨if |c| ≤ |a| then (pt X.lo).lo else (pt X.hi).lo,
       if a ≤ 0 ∧ 0 ≤ c then (KI.ofRatInterval 1 1).hi
       else if |a| ≤ |c| then (pt X.lo).hi else (pt X.hi).hi⟩
    else if 0 < a ∨ c < 0 then evalK [X] g
    else pm1
  | _, _ => pm1

/-- `0 ∉ X`, checked on the endpoints' exact values. -/
def domK (X : KI) : Bool :=
  match ratOfBits X.lo, ratOfBits X.hi with
  | some a, some c => decide (0 < a) || decide (c < 0)
  | _, _ => false

theorem one_mem : (1 : ℝ) ∈ (toI (KI.ofRatInterval 1 1)).toSet := by
  rw [(KF.ofRatInterval_toI _ _).1]; apply mem_toSet_ofRatInterval <;> simp

theorem cast_abs_le {a c : ℚ} (h : |c| ≤ |a|) : |(c : ℝ)| ≤ |(a : ℝ)| := by
  have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this

theorem min_abs_le {a c x : ℝ} (h1 : a ≤ x) (h2 : x ≤ c) (h : ¬(a ≤ 0 ∧ 0 ≤ c)) :
    min |a| |c| ≤ |x| := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [abs_of_pos ha, abs_of_pos (by linarith : 0 < x)]; exact (min_le_left _ _).trans h1
  · have hc : c < 0 := by by_contra hc; exact h ⟨ha, le_of_not_gt hc⟩
    rw [abs_of_neg hc, abs_of_neg (by linarith : x < 0)]
    exact (min_le_right _ _).trans (by linarith)

theorem evK_mem {X : KI} (hX : WF X) (hlo : isNaN X.lo = false) (hhi : isNaN X.hi = false)
    {x : ℝ} (hx : x ∈ (toI X).toSet) : sinc x ∈ (toI (evK X)).toSet := by
  unfold evK
  split
  · rename_i a c ha hc
    have h1 : (a : ℝ) ≤ x := le_of_mem_lo hX hlo ha hx
    have h2 : x ≤ (c : ℝ) := ge_of_mem_hi hX hhi hc hx
    have hPa := mem_toSet_iff_toE.1 (pt_mem hX.1 ha)
    have hPc := mem_toSet_iff_toE.1 (pt_mem hX.2 hc)
    have hmax : |x| ≤ max |(a : ℝ)| |(c : ℝ)| := abs_le_max_abs_abs h1 h2
    by_cases h3 : -3 ≤ a ∧ c ≤ 3
    · simp only [h3.1, h3.2, and_self, ↓reduceIte]
      have e1 : (-3 : ℝ) ≤ a := by exact_mod_cast h3.1
      have e2 : (c : ℝ) ≤ 3 := by exact_mod_cast h3.2
      have ha3 : |(a : ℝ)| ≤ 3 := abs_le.2 ⟨e1, by linarith⟩
      have hc3 : |(c : ℝ)| ≤ 3 := abs_le.2 ⟨by linarith, e2⟩
      have hL : ∀ l, l = (if |c| ≤ |a| then (pt X.lo).lo else (pt X.hi).lo) →
          (toF l).isNaN = false ∧ (toF l).toE ≤ ((sinc x : ℝ) : EReal) := by
        intro l hl; subst hl
        split_ifs with h4
        · have h4' := cast_abs_le h4
          refine ⟨hPa.1.1, hPa.1.2.trans ?_⟩
          exact_mod_cast sinc_le_of_abs (hmax.trans (max_le le_rfl h4')) ha3
        · have h4' : |(a : ℝ)| ≤ |(c : ℝ)| := cast_abs_le (le_of_lt (not_le.1 h4))
          refine ⟨hPc.1.1, hPc.1.2.trans ?_⟩
          exact_mod_cast sinc_le_of_abs (hmax.trans (max_le h4' le_rfl)) hc3
      have hU : ∀ u, u = (if a ≤ 0 ∧ 0 ≤ c then (KI.ofRatInterval 1 1).hi
          else if |a| ≤ |c| then (pt X.lo).hi else (pt X.hi).hi) →
          (toF u).isNaN = false ∧ ((sinc x : ℝ) : EReal) ≤ (toF u).toE := by
        intro u hu; subst hu
        split_ifs with h5 h6
        · exact ⟨(mem_toSet_iff_toE.1 one_mem).2.1,
            (by exact_mod_cast sinc_le_one x : ((sinc x : ℝ) : EReal) ≤ ((1 : ℝ) : EReal)).trans
              (mem_toSet_iff_toE.1 one_mem).2.2⟩
        · have h5' : ¬((a : ℝ) ≤ 0 ∧ 0 ≤ (c : ℝ)) := fun h => h5 ⟨by exact_mod_cast h.1,
            by exact_mod_cast h.2⟩
          have hm := min_abs_le h1 h2 h5'
          rw [min_eq_left (cast_abs_le h6)] at hm
          refine ⟨hPa.2.1, le_trans ?_ hPa.2.2⟩
          exact_mod_cast sinc_le_of_abs hm (hmax.trans (max_le ha3 hc3))
        · have h5' : ¬((a : ℝ) ≤ 0 ∧ 0 ≤ (c : ℝ)) := fun h => h5 ⟨by exact_mod_cast h.1,
            by exact_mod_cast h.2⟩
          have hm := min_abs_le h1 h2 h5'
          rw [min_eq_right (cast_abs_le (le_of_lt (not_le.1 h6)))] at hm
          refine ⟨hPc.2.1, le_trans ?_ hPc.2.2⟩
          exact_mod_cast sinc_le_of_abs hm (hmax.trans (max_le ha3 hc3))
      exact mem_toSet_iff_toE.2 ⟨hL _ rfl, hU _ rfl⟩
    · simp only [h3, ↓reduceIte]
      split_ifs with h4
      · have hx0 : x ≠ 0 := by
          rcases h4 with h4 | h4
          · have : (0 : ℝ) < a := by exact_mod_cast h4
            exact (by linarith : 0 < x).ne'
          · have : (c : ℝ) < 0 := by exact_mod_cast h4
            exact (by linarith : x < 0).ne
        rw [sinc_of_ne_zero hx0]
        simpa [g, IExpr.denote] using denote_mem_evalK hX hx g
      · exact mem_pm1 x
  · exact mem_pm1 x

theorem domK_ne {X : KI} (hX : WF X) (hlo : isNaN X.lo = false) (hhi : isNaN X.hi = false)
    (h : domK X = true) {x : ℝ} (hx : x ∈ (toI X).toSet) : x ≠ 0 := by
  unfold domK at h
  split at h
  · rename_i a c ha hc
    have h1 := le_of_mem_lo hX hlo ha hx
    have h2 := ge_of_mem_hi hX hhi hc hx
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · have : (0 : ℝ) < a := by exact_mod_cast h
      exact (by linarith : 0 < x).ne'
    · have : (c : ℝ) < 0 := by exact_mod_cast h
      exact (by linarith : x < 0).ne
  · simp at h

/-- Derivative template `(x cos x - sin x)/x²` (for `x ≠ 0`). -/
def sincDeriv : IExpr := .div (.sub (.mul (.var 0) (.cos (.var 0))) (.sin (.var 0))) (.pow (.var 0) 2)

end RealFP.Sinc

namespace RealFP
open Sinc

/-- The kernel implementation of `Real.sinc`. -/
def sincExt : ExtFn where
  name := "sinc"
  evK := Sinc.evK
  domK := Sinc.domK
  deriv := sincDeriv

/-- Registers `Real.sinc` for all realfp tactics (derivative only away from `0`). -/
@[realfp_fn] theorem sinc_sound : ExtSound sinc (fun x => x ≠ 0) sincExt where
  enc _ hX hlo hhi _ _ hx := evK_mem hX hlo hhi hx
  dom _ hX hlo hhi h _ hx := domK_ne hX hlo hhi h hx
  deriv_extFree := rfl
  deriv x hx := by simpa [sincExt, sincDeriv, IExpr.denoteB] using hasDerivAt_sinc hx

end RealFP
