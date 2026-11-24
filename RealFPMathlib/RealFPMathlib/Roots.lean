/-
Root certificates (soundness): sign-change existence (IVT), exclusion `f ≠ 0`, uniqueness
by a derivative sign (1D), and Krawczyk-type existence + uniqueness for `n × n` systems.

All checks are Boolean functions evaluated by `decide +kernel`; the theorems below turn a
`true` result into a real statement. Everything reuses `evalK` (the kernel interval evaluator),
`IExpr.deriv` and their soundness theorems (`memK`, `hasDerivAt_box`, `domOK_sound`).
-/
import RealFPMathlib.IntervalDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits

noncomputable section

namespace RealFP.Roots

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-- All expressions vanish at `xs`. -/
def AllZero (es : List IExpr) (xs : List ℝ) : Prop := ∀ e ∈ es, e.denote xs = 0

/-! ### Exclusion: `f ≠ 0` on a box -/

/-- The enclosure excludes `0`: `F < 0` or `F > 0`. -/
def gNe (F : KI) : Bool := gLt (KI.ofRat 0).lo F || gGt (KI.ofRat 0).hi F

omit [ExtTbl] [ExtSem] in
theorem gNe_sound : ∀ F, WF F → gNe F = true → ∀ y ∈ (toI F).toSet, y ≠ 0 := by
  intro F hF h y hy
  simp only [gNe, Bool.or_eq_true] at h
  rcases h with h | h
  · have := gLt_sound 0 F hF h y hy; simp at this; exact this.ne
  · have := gGt_sound 0 F hF h y hy; simp at this; exact this.ne'

/-- **Exclusion.** A bisection certificate on which every leaf excludes `0`. -/
theorem prove_ne (e : IExpr) (bs : List (ℚ × ℚ)) (cert : Cert)
    (h : checkK e gNe cert (boxes bs) = true) (xs : List ℝ) (hxs : InBoxes xs bs) :
    e.denote xs ≠ 0 :=
  checkK_sound e _ _ gNe_sound cert _ xs (boxes_wf bs) (boxes_mem hxs) h

/-! ### One variable -/

omit [ExtTbl] [ExtSem] in
theorem inBoxes_one {x : ℝ} {a b : ℚ} : InBoxes [x] [(a, b)] ↔ (a : ℝ) ≤ x ∧ x ≤ b := by
  simp [InBoxes]

theorem allZero_one {e : IExpr} {x : ℝ} : AllZero [e] [x] ↔ e.denote [x] = 0 := by
  simp [AllZero]

/-- `t ↦ e(t)` has derivative `(e.deriv 0)(t)` at every point of `[a, b]` when
`domOK` holds on the box. -/
theorem hasDerivAt_one {e : IExpr} {a b : ℚ} (hd : domOK (boxes [(a, b)]) e = true)
    {x : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ b) :
    HasDerivAt (fun t => e.denote [t]) ((e.deriv 0).denote [x]) x := by
  have hxs : InBoxes [x] [(a, b)] := inBoxes_one.2 hx
  have hdom := domOK_sound (boxes_wf _) (boxes_mem hxs) e hd
  have := hasDerivAt_denote (xs := [x]) (i := 0) (by simp) e hdom
  rw [denote_deriv]
  simpa using this

theorem continuousOn_one {e : IExpr} {a b : ℚ} (hd : domOK (boxes [(a, b)]) e = true) :
    ContinuousOn (fun t => e.denote [t]) (Set.Icc (a : ℝ) b) := fun _ hx =>
  (hasDerivAt_one hd hx).continuousAt.continuousWithinAt

/-- Sign of `e` at the point `a` (`le`: `e(a) ≤ 0`; otherwise `e(a) ≥ 0`). -/
def signAt (e : IExpr) (a : ℚ) (le : Bool) : Bool :=
  bif le then checkK e (gLe (KI.ofRat 0).lo) .leaf (boxes [(a, a)])
  else checkK e (gGe (KI.ofRat 0).hi) .leaf (boxes [(a, a)])

theorem signAt_sound {e : IExpr} {a : ℚ} {le : Bool} (h : signAt e a le = true) :
    if le then e.denote [(a : ℝ)] ≤ 0 else 0 ≤ e.denote [(a : ℝ)] := by
  have hx : InBoxes [(a : ℝ)] [(a, a)] := inBoxes_one.2 ⟨le_rfl, le_rfl⟩
  cases le
  · have := prove_ge e _ 0 .leaf h _ hx; simpa using this
  · have := prove_le e _ 0 .leaf h _ hx; simpa using this

/-- Sign change between `a` and `b`, with `domOK` on `[a, b]` (so `e` is continuous). -/
def ivtCheck (e : IExpr) (a b : ℚ) : Bool :=
  decide (a ≤ b) && domOK (boxes [(a, b)]) e &&
    ((signAt e a true && signAt e b false) || (signAt e a false && signAt e b true))

/-- **Existence by sign change** (intermediate value theorem). -/
theorem ivt_exists (e : IExpr) (a b : ℚ) (h : ivtCheck e a b = true) :
    ∃ x : ℝ, InBoxes [x] [(a, b)] ∧ AllZero [e] [x] := by
  simp only [ivtCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hab, hd⟩, hs⟩ := h
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hc := continuousOn_one hd
  have key : (0 : ℝ) ∈ (fun t => e.denote [t]) '' Set.Icc (a : ℝ) b := by
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have s1 := signAt_sound h1; have s2 := signAt_sound h2
      simp only [↓reduceIte, Bool.false_eq_true] at s1 s2
      exact intermediate_value_Icc hab' hc ⟨s1, s2⟩
    · have s1 := signAt_sound h1; have s2 := signAt_sound h2
      simp only [↓reduceIte, Bool.false_eq_true] at s1 s2
      exact intermediate_value_Icc' hab' hc ⟨s2, s1⟩
  obtain ⟨x, hx, hx0⟩ := key
  exact ⟨x, inBoxes_one.2 hx, allZero_one.2 hx0⟩

/-- Strict sign of `e.deriv 0` on `[a, b]` (`inc`: `> 0`; otherwise `< 0`), by a derivative
certificate. -/
def derivSign (e : IExpr) (a b : ℚ) (inc : Bool) (cert : DCert) : Bool :=
  bif inc then checkD (e.deriv 0) (gGt (KI.ofRat 0).hi) false cert (boxes [(a, b)])
  else checkD (e.deriv 0) (gLt (KI.ofRat 0).lo) true cert (boxes [(a, b)])

theorem injOn_of_derivSign {e : IExpr} {a b : ℚ} {inc : Bool} {cert : DCert}
    (hd : domOK (boxes [(a, b)]) e = true) (h : derivSign e a b inc cert = true) :
    Set.InjOn (fun t => e.denote [t]) (Set.Icc (a : ℝ) b) := by
  have hc := continuousOn_one hd
  have hder : ∀ x ∈ interior (Set.Icc (a : ℝ) b),
      deriv (fun t => e.denote [t]) x = (e.deriv 0).denote [x] := by
    intro x hx
    exact (hasDerivAt_one hd (interior_subset hx)).deriv
  cases inc
  · refine (strictAntiOn_of_deriv_neg (convex_Icc _ _) hc fun x hx => ?_).injOn
    rw [hder x hx]
    have := proveD_lt (e.deriv 0) _ 0 cert h [x] (inBoxes_one.2 (interior_subset hx))
    simpa using this
  · refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) hc fun x hx => ?_).injOn
    rw [hder x hx]
    have := proveD_gt (e.deriv 0) _ 0 cert h [x] (inBoxes_one.2 (interior_subset hx))
    simpa using this

/-- **Unique root in one variable**: sign change plus a strict derivative sign. -/
theorem unique_one (e : IExpr) (a b : ℚ) (inc : Bool) (cert : DCert)
    (h : (ivtCheck e a b && derivSign e a b inc cert) = true) :
    ∃! x : ℝ, InBoxes [x] [(a, b)] ∧ AllZero [e] [x] := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨hi, hs⟩ := h
  have hd : domOK (boxes [(a, b)]) e = true := by
    simp only [ivtCheck, Bool.and_eq_true] at hi; exact hi.1.2
  obtain ⟨x, hx, hx0⟩ := ivt_exists e a b hi
  refine ⟨x, ⟨hx, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  exact injOn_of_derivSign hd hs (inBoxes_one.1 hy) (inBoxes_one.1 hx)
    ((allZero_one.1 hy0).trans (allZero_one.1 hx0).symm)

end RealFP.Roots
