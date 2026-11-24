/-
`Real.artanh` (Mathlib: `artanh x = log √((1 + x) / (1 - x))`, `= ½ log ((1 + x)/(1 - x))` on
`[-1, 1]`) as a realfp extension, on its natural domain `(-1, 1)`.

Enclosure: `artanh` is increasing on `(-1, 1)`, so a box `[a, b]` with `-1 < a`, `b < 1` maps to
`[artanh a, artanh b]` (`ExtFn.ofMonoK`); boxes touching `±1` (or beyond) give `whole`, and the
domain check `domK` rejects them, so derivative-based modes only run strictly inside `(-1, 1)`.
Point enclosures:
* `|q| ≤ 2⁻¹²`: rational bounds `q + q³/3 ≤ artanh q ≤ q + q³/3 + q⁵/4` (`q ≥ 0`, odd symmetry
  for `q < 0`) — relative width `≤ q⁴/4 < 2⁻⁵⁰`;
* otherwise the kernel's `½ log ((1 + q)/(1 - q))`, relative error `≲ 10⁻¹²` just above `2⁻¹²`,
  a few ulps (relative) away from `0`; near `±1` the absolute error grows like `ulp/(1 - |q|)`.
Derivative `1/(1 - x²)` on `(-1, 1)` (proved here: Mathlib has no `HasDerivAt` for `artanh`).
-/
import RealFPMathlib.Registry
import Mathlib.Analysis.SpecialFunctions.Artanh

open Real Filter Topology
open Interval64 Interval64.KF

namespace RealFP.Artanh

theorem artanh_neg_eq (x : ℝ) : artanh (-x) = -artanh x := by
  unfold artanh
  rw [show (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ by rw [inv_div]; ring_nf,
    Real.sqrt_inv, Real.log_inv]

theorem artanh_eq_logs {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    artanh x = 1 / 2 * (Real.log (1 + x) - Real.log (1 - x)) := by
  rw [artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, log_div (by linarith [hx.1]) (by linarith [hx.2])]

theorem hasDerivAt_artanh {x : ℝ} (h1 : -1 < x) (h2 : x < 1) :
    HasDerivAt artanh (1 - x ^ 2)⁻¹ x := by
  have ha : HasDerivAt (fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)))
      (1 / 2 * (1 / (1 + x) - (-1) / (1 - x))) x := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.sub
    · exact ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    · exact ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
  have hev : artanh =ᶠ[𝓝 x] fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds h1 h2) fun y hy => artanh_eq_logs hy
  convert ha.congr_of_eventuallyEq hev using 1
  have : (1 + x) ≠ 0 := by linarith
  have : (1 - x) ≠ 0 := by linarith
  rw [show (1 - x ^ 2) = (1 + x) * (1 - x) by ring]
  field_simp; ring

theorem lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : x + x ^ 3 / 3 ≤ artanh x := by
  have := nonneg_of_hasDerivAt (F := fun y => artanh y - (y + y ^ 3 / 3))
    (F' := fun y => (1 - y ^ 2)⁻¹ - (1 + y ^ 2)) (by simp)
    (fun y h0 h1 => by
      have := (hasDerivAt_artanh (by linarith) (by linarith)).sub
        ((hasDerivAt_id y).add ((hasDerivAt_pow 3 y).div_const 3))
      convert this using 1
      · funext z; simp
      · norm_num)
    (fun y h0 h1 => by
      have hp : 0 < 1 - y ^ 2 := by nlinarith
      rw [sub_nonneg, le_inv_comm₀ (by positivity) hp, ← one_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_nonneg (sq_nonneg y) 2]) hx
  beta_reduce at this; linarith

theorem upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : artanh x ≤ x + x ^ 3 / 3 + x ^ 5 / 4 := by
  have := nonneg_of_hasDerivAt (F := fun y => (y + y ^ 3 / 3 + y ^ 5 / 4) - artanh y)
    (F' := fun y => (1 + y ^ 2 + 5 * y ^ 4 / 4) - (1 - y ^ 2)⁻¹) (by simp)
    (fun y h0 h1 => by
      have := (((hasDerivAt_id y).add ((hasDerivAt_pow 3 y).div_const 3)).add
        ((hasDerivAt_pow 5 y).div_const 4)).sub (hasDerivAt_artanh (by linarith) (by linarith))
      convert this using 1
      · funext z; simp
      · norm_num)
    (fun y h0 h1 => by
      have hp : 0 < 1 - y ^ 2 := by nlinarith
      rw [sub_nonneg, inv_le_comm₀ hp (by positivity), ← one_div, div_le_iff₀ (by positivity)]
      have h4 : 0 ≤ y ^ 4 := by positivity
      nlinarith [mul_nonneg h4 (by nlinarith : (0:ℝ) ≤ 1 - 5 * y ^ 2)]) hx
  beta_reduce at this; linarith

theorem between {q : ℝ} (hq : |q| ≤ 1 / 4) :
    min (q + q ^ 3 / 3) (q + q ^ 3 / 3 + q ^ 5 / 4) ≤ artanh q ∧
    artanh q ≤ max (q + q ^ 3 / 3) (q + q ^ 3 / 3 + q ^ 5 / 4) := by
  rcases le_or_gt 0 q with h | h
  · rw [abs_of_nonneg h] at hq
    exact ⟨min_le_left _ _ |>.trans (lower h hq), (upper h hq).trans (le_max_right _ _)⟩
  · rw [abs_of_neg h] at hq
    have h' : 0 ≤ -q := by linarith
    have l := lower h' hq; have u := upper h' hq
    rw [artanh_neg_eq] at l u
    constructor
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (by nlinarith : artanh q ≤ q + q ^ 3 / 3).trans (le_max_left _ _)

/-- `½ log ((1 + x)/(1 - x))`. -/
def g : IExpr := .mul (.rat (1 / 2)) (.log (.div (.add (.rat 1) (.var 0)) (.sub (.rat 1) (.var 0))))

/-- Point enclosure of `artanh` at the bit pattern `b`. -/
def pt (b : Nat) : KI :=
  match ratOfBits b with
  | some q =>
    if |q| ≤ 1 / 4096 then
      let A := q + q ^ 3 / 3
      let B := A + q ^ 5 / 4
      KI.ofRatInterval (min A B) (max A B)
    else evalK [ptK b] g
  | none => KI.whole

theorem pt_mem (b : Nat) (q : ℚ) (hb : b < 2 ^ 64) (hq : ratOfBits b = some q)
    (hS : (q : ℝ) ∈ Set.Ioo (-1 : ℝ) 1) : artanh q ∈ (toI (pt b)).toSet := by
  unfold pt; rw [hq]; dsimp only
  split_ifs with h1
  · rw [(KF.ofRatInterval_toI _ _).1]
    have h1' : |(q : ℝ)| ≤ 1 / 4 := by
      have : |(q : ℝ)| ≤ 1 / 4096 := by
        have := (Rat.cast_le (K := ℝ)).2 h1; push_cast at this; exact this
      linarith
    have := between h1'
    apply mem_toSet_ofRatInterval <;> push_cast
    · exact this.1
    · exact this.2
  · have := denote_mem_evalK_pt hb hq g
    rw [artanh_eq_half_log ⟨hS.1.le, hS.2.le⟩]
    simpa [g, IExpr.denote] using this

/-- `X ⊆ (-1, 1)`, checked on the endpoints' exact values. -/
def inside (X : KI) : Bool :=
  match ratOfBits X.lo, ratOfBits X.hi with
  | some a, some c => decide (-1 < a) && decide (c < 1)
  | _, _ => false

theorem inside_sub {X : KI} (hX : WF X) (hlo : isNaN X.lo = false) (hhi : isNaN X.hi = false)
    (h : inside X = true) {x : ℝ} (hx : x ∈ (toI X).toSet) : x ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold inside at h
  split at h
  · rename_i a c ha hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := le_of_mem_lo hX hlo ha hx
    have h2 := ge_of_mem_hi hX hhi hc hx
    have e1 : (-1 : ℝ) < a := by exact_mod_cast h.1
    have e2 : (c : ℝ) < 1 := by exact_mod_cast h.2
    exact ⟨by linarith, by linarith⟩
  · simp at h

/-- Derivative template `1/(1 - x²)`. -/
def artanhDeriv : IExpr := .inv (.sub (.rat 1) (.pow (.var 0) 2))

end RealFP.Artanh

namespace RealFP
open Artanh

/-- The kernel implementation of `Real.artanh` on `(-1, 1)`. -/
def artanhExt : ExtFn := ExtFn.ofMonoK "artanh" Artanh.pt inside inside artanhDeriv

/-- Registers `Real.artanh` (domain `(-1, 1)`) for all realfp tactics. -/
@[realfp_fn] theorem artanh_sound : ExtSound artanh (fun x => -1 < x ∧ x < 1) artanhExt :=
  ExtSound.ofMonoK (S := Set.Ioo (-1) 1) strictMonoOn_artanh.monotoneOn
    (fun _ hX hlo hhi hg _ hx => inside_sub hX hlo hhi hg hx) (fun b q hb hq hS => pt_mem b q hb hq hS)
    (fun _ hX hlo hhi hg _ hx => inside_sub hX hlo hhi hg hx) rfl
    (fun x hx => by
      simpa [artanhDeriv, IExpr.denoteB] using hasDerivAt_artanh hx.1 hx.2)

/-- `artanh` is continuous on `(-1, 1)`. -/
theorem continuousOn_artanh : ContinuousOn artanh (Set.Ioo (-1) 1) :=
  fun _ hx => (hasDerivAt_artanh hx.1 hx.2).continuousAt.continuousWithinAt

end RealFP
