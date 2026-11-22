/-
Soundness of 2D quadrature over rectangles (core `Interval64/Quad2.lean`).

* `integral2_mem_integrate2` : `∫_a^b ∫_c^d f x y dy dx ∈ integrate2 F a b c d tol fuel` for an
  interval extension `F` of `f`, `f` continuous on the rectangle.
* `integral2_mem_integrate2E0`, `integral2_mem_integrate2E1` : `IExpr` integrands.
* `setIntegral_rect_eq` : Fubini, `∫_{[a,b]×[c,d]} f = ∫_a^b ∫_c^d f`.
-/
import RealFPMathlib.Quad
import RealFPMathlib.IntervalDeriv
import Interval64.Quad2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Interval64 Interval64.Quad Interval64.KF Set intervalIntegral MeasureTheory

noncomputable section

namespace RealFP.Quad2

open RealFP.Quad

section
variable {f : ℝ → ℝ} {F : Interval64 → Interval64}

/-- `cell0` with a local extension hypothesis. -/
theorem integral_mem_cell0' {lo hi : Float} (hF : ∀ x ∈ Icc lo.toReal hi.toReal, f x ∈ F ⟨lo, hi⟩)
    (hlo : finite lo = true) (hhi : finite hi = true) (hle : lo.toReal ≤ hi.toReal)
    (hc : ContinuousOn f (Icc lo.toReal hi.toReal)) :
    (∫ x in lo.toReal..hi.toReal, f x) ∈ cell0 F lo hi := by
  show _ ∈ F ⟨lo, hi⟩ * (point hi - point lo)
  have hW : hi.toReal - lo.toReal ∈ point hi - point lo :=
    Iv.sub_mem (toReal_mem hhi) (toReal_mem hlo)
  rcases hle.lt_or_eq with hlt | heq
  · have hK : (∫ _ in lo.toReal..hi.toReal, (1 : ℝ)) = hi.toReal - lo.toReal := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact integral_mem_mul (w := fun _ => 1) hlt hW (sub_pos.2 hlt) hK
      (fun _ _ => zero_le_one) (hc.intervalIntegrable_of_Icc hle) intervalIntegrable_const
      (fun x hx => ⟨f x, hF x hx, (mul_one _).symm⟩)
  · have h0 : (∫ x in lo.toReal..hi.toReal, f x) = f lo.toReal * (hi.toReal - lo.toReal) := by
      rw [← heq, integral_same, sub_self, mul_zero]
    rw [h0]
    exact Iv.mem_mul (hF _ ⟨le_rfl, hle⟩) hW

theorem integral_mem_integrate0' {a b : Float}
    (hF : ∀ lo hi : Float, finite lo = true → finite hi = true → a.toReal ≤ lo.toReal →
      lo.toReal ≤ hi.toReal → hi.toReal ≤ b.toReal →
      ∀ x ∈ Icc lo.toReal hi.toReal, f x ∈ F ⟨lo, hi⟩)
    (hc : ContinuousOn f (uIcc a.toReal b.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, f x) ∈ integrate (cell0 F) a b tol fuel := by
  refine integral_mem_integrate (fun lo hi h1 h2 h3 h4 h5 =>
    integral_mem_cell0' (hF lo hi h1 h2 h3 h4 h5) h1 h2 h4 ?_) hc tol fuel
  refine hc.mono fun x hx => ?_
  rw [uIcc_of_le (le_trans h3 (le_trans h4 h5))]
  exact ⟨le_trans h3 hx.1, le_trans hx.2 h5⟩

end

/-! ### Continuity of the inner integral -/

/-- Clamp to `uIcc a b`. -/
def clamp (a b x : ℝ) : ℝ := max (a ⊓ b) (min (a ⊔ b) x)

theorem continuous_clamp (a b : ℝ) : Continuous (clamp a b) := by
  unfold clamp; fun_prop

theorem clamp_mem (a b x : ℝ) : clamp a b x ∈ uIcc a b :=
  ⟨le_max_left _ _, max_le inf_le_sup (min_le_left _ _)⟩

theorem clamp_eq {a b x : ℝ} (hx : x ∈ uIcc a b) : clamp a b x = x := by
  unfold clamp; rw [min_eq_right hx.2, max_eq_right hx.1]

theorem continuousOn_inner {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hc : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ uIcc c d)) :
    ContinuousOn (fun x => ∫ y in c..d, f x y) (uIcc a b) := by
  set g : ℝ → ℝ → ℝ := fun x y => f (clamp a b x) (clamp c d y)
  have hg : Continuous (Function.uncurry g) := by
    have : Function.uncurry g =
        Function.uncurry f ∘ fun p : ℝ × ℝ => (clamp a b p.1, clamp c d p.2) := rfl
    rw [this]
    exact hc.comp_continuous (((continuous_clamp a b).comp continuous_fst).prodMk
      ((continuous_clamp c d).comp continuous_snd))
      fun p => ⟨clamp_mem a b p.1, clamp_mem c d p.2⟩
  refine (continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hg c d).continuousOn.congr
    fun x hx => ?_
  refine integral_congr fun y hy => ?_
  simp only [g, clamp_eq hx, clamp_eq hy]

/-! ### 2D rules -/

/-- **2D quadrature** (iterated integral) for an interval extension `F` of `f`. -/
theorem integral2_mem_integrate2 {f : ℝ → ℝ → ℝ} {F : Interval64 → Interval64 → Interval64}
    (hF : ∀ X Y x y, x ∈ X → y ∈ Y → f x y ∈ F X Y) {a b c d : Float}
    (hc : ContinuousOn (Function.uncurry f) (uIcc a.toReal b.toReal ×ˢ uIcc c.toReal d.toReal))
    (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, ∫ y in c.toReal..d.toReal, f x y) ∈
      integrate2 F a b c d tol fuel := by
  refine integral_mem_integrate0' (fun lo hi h1 h2 h3 h4 h5 x hx => ?_)
    (continuousOn_inner hc) tol fuel
  have hxab : x ∈ uIcc a.toReal b.toReal := by
    rw [uIcc_of_le (le_trans h3 (le_trans h4 h5))]
    exact ⟨le_trans h3 hx.1, le_trans hx.2 h5⟩
  refine integral_mem_integrate0 (f := f x) (F := F ⟨lo, hi⟩)
    (fun Y y hy => hF _ Y x y (mem_box h1 h2 hx) hy) ?_ tol fuel
  exact hc.comp (continuousOn_const.prodMk continuousOn_id) fun y hy => ⟨hxab, hy⟩

theorem integral2_mem_integrate2E0 (e : IExpr) {a b c d : Float}
    (hc : ContinuousOn (fun p : ℝ × ℝ => e.denote [p.1, p.2])
      (uIcc a.toReal b.toReal ×ˢ uIcc c.toReal d.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, ∫ y in c.toReal..d.toReal, e.denote [x, y]) ∈
      integrate2E0 e a b c d tol fuel :=
  integral2_mem_integrate2 (f := fun x y => e.denote [x, y])
    (fun _ _ _ _ hx hy => eval_sound (List.Forall₂.cons hx (List.Forall₂.cons hy List.Forall₂.nil)) e)
    hc tol fuel

/-- Inner second-order cells (derivative in `y` from `e.diff 1`, defined where `Dom`). -/
theorem integral2_mem_integrate2E1 (e : IExpr) {a b c d : Float}
    (hdom : ∀ x ∈ uIcc a.toReal b.toReal, ∀ y ∈ uIcc c.toReal d.toReal, Dom [x, y] e)
    (hc : ContinuousOn (fun p : ℝ × ℝ => e.denote [p.1, p.2])
      (uIcc a.toReal b.toReal ×ˢ uIcc c.toReal d.toReal)) (tol : Float) (fuel : ℕ) :
    (∫ x in a.toReal..b.toReal, ∫ y in c.toReal..d.toReal, e.denote [x, y]) ∈
      integrate2E1 e a b c d tol fuel := by
  refine integral_mem_integrate0' (fun lo hi h1 h2 h3 h4 h5 x hx => ?_)
    (continuousOn_inner (f := fun x y => e.denote [x, y]) hc) tol fuel
  have hxab : x ∈ uIcc a.toReal b.toReal := by
    rw [uIcc_of_le (le_trans h3 (le_trans h4 h5))]
    exact ⟨le_trans h3 hx.1, le_trans hx.2 h5⟩
  have hX := mem_box h1 h2 hx
  refine integral_mem_integrate1 (f := fun y => e.denote [x, y])
    (f' := fun y => (e.diff 1).denote [x, y])
    (fun Y y hy => eval_sound (List.Forall₂.cons hX (List.Forall₂.cons hy List.Forall₂.nil)) e)
    (fun Y y hy => eval_sound (List.Forall₂.cons hX (List.Forall₂.cons hy List.Forall₂.nil)) _)
    (fun y hy => ?_) tol fuel
  have := hasDerivAt_denote (xs := [x, y]) (i := 1) (by simp) e (hdom x hxab y hy)
  simpa using this

/-! ### Fubini -/

theorem setIntegral_rect_eq {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hc : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    (∫ p in Icc a b ×ˢ Icc c d, f p.1 p.2) = ∫ x in a..b, ∫ y in c..d, f x y := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc c d) :=
    hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  simp only
  rw [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]

end RealFP.Quad2
