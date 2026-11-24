/-
`≠` goals and one-variable roots at precision 128 (mirror of `RealFPMathlib/Roots.lean` with the
dyadic evaluator): exclusion by bisection (`prove_neQ`), existence by a sign change
(`ivt_existsQ`), uniqueness from a strict derivative sign (`unique_oneQ`).
-/
import RealFPMathlib.I128Deriv
import RealFPMathlib.Roots

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open RealFP.Roots (AllZero)

noncomputable section

namespace RealFP.I128Q

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-! ### Exclusion -/

omit [ExtTbl] [ExtSem] in
theorem nzQ_sound : ∀ F, Interval128.Dy.nzQ F = true → ∀ y, mem y F → y ≠ 0 :=
  fun _ h _ hy => ne_of_nzQ h hy

/-- **Exclusion** at 128: a bisection certificate on which every leaf excludes `0`. -/
theorem prove_neQ (e : IExpr) (bs : List (ℚ × ℚ)) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e Interval128.Dy.nzQ cert (Interval128.Dy.boxes bs) = true)
    (xs : List ℝ) (hxs : InBoxes xs bs) : e.denote xs ≠ 0 :=
  checkQ_sound e _ (fun y => y ≠ 0) nzQ_sound cert _ xs (boxes_mem hxs) h

/-! ### One variable -/

theorem hasDerivAt_oneQ {e : IExpr} {a b : ℚ}
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(a, b)]) e = true)
    {x : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ b) :
    HasDerivAt (fun t => e.denote [t]) ((e.deriv 0).denote [x]) x := by
  have hxs : InBoxes [x] [(a, b)] := Roots.inBoxes_one.2 hx
  have hdom := domOKQ_sound (boxes_mem hxs) e hd
  have := hasDerivAt_denote (xs := [x]) (i := 0) (by simp) e hdom
  rw [denote_deriv]
  simpa using this

theorem continuousOn_oneQ {e : IExpr} {a b : ℚ}
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(a, b)]) e = true) :
    ContinuousOn (fun t => e.denote [t]) (Set.Icc (a : ℝ) b) := fun _ hx =>
  (hasDerivAt_oneQ hd hx).continuousAt.continuousWithinAt

/-- Sign of `e` at the point `a` (`le`: `e(a) ≤ 0`; otherwise `e(a) ≥ 0`). -/
def signAtQ (e : IExpr) (a : ℚ) (le : Bool) : Bool :=
  bif le then Interval128.Dy.gLe 0 (Interval128.Dy.evalQ (Interval128.Dy.boxes [(a, a)]) e)
  else Interval128.Dy.gGe 0 (Interval128.Dy.evalQ (Interval128.Dy.boxes [(a, a)]) e)

theorem signAtQ_sound {e : IExpr} {a : ℚ} {le : Bool} (h : signAtQ e a le = true) :
    if le then e.denote [(a : ℝ)] ≤ 0 else 0 ≤ e.denote [(a : ℝ)] := by
  have hx : InBoxes [(a : ℝ)] [(a, a)] := Roots.inBoxes_one.2 ⟨le_rfl, le_rfl⟩
  have hm := evalQ_sound (boxes_mem hx) e
  cases le
  · have := gGe_sound 0 _ h _ hm; simpa using this
  · have := gLe_sound 0 _ h _ hm; simpa using this

/-- Sign change between `a` and `b`, with `domOKQ` on `[a, b]` (so `e` is continuous). -/
def ivtCheckQ (e : IExpr) (a b : ℚ) : Bool :=
  decide (a ≤ b) && Interval128.Dy.domOKQ (Interval128.Dy.boxes [(a, b)]) e &&
    ((signAtQ e a true && signAtQ e b false) || (signAtQ e a false && signAtQ e b true))

theorem ivt_existsQ (e : IExpr) (a b : ℚ) (h : ivtCheckQ e a b = true) :
    ∃ x : ℝ, InBoxes [x] [(a, b)] ∧ AllZero [e] [x] := by
  simp only [ivtCheckQ, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hab, hd⟩, hs⟩ := h
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hc := continuousOn_oneQ hd
  have key : (0 : ℝ) ∈ (fun t => e.denote [t]) '' Set.Icc (a : ℝ) b := by
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have s1 := signAtQ_sound h1; have s2 := signAtQ_sound h2
      simp only [↓reduceIte, Bool.false_eq_true] at s1 s2
      exact intermediate_value_Icc hab' hc ⟨s1, s2⟩
    · have s1 := signAtQ_sound h1; have s2 := signAtQ_sound h2
      simp only [↓reduceIte, Bool.false_eq_true] at s1 s2
      exact intermediate_value_Icc' hab' hc ⟨s2, s1⟩
  obtain ⟨x, hx, hx0⟩ := key
  exact ⟨x, Roots.inBoxes_one.2 hx, Roots.allZero_one.2 hx0⟩

/-- Existence on a sub-interval `[a', b'] ⊆ [a, b]`. -/
theorem ivt_exists_inQ (e : IExpr) (a b a' b' : ℚ)
    (h : (decide (a ≤ a' ∧ b' ≤ b) && ivtCheckQ e a' b') = true) :
    ∃ x : ℝ, InBoxes [x] [(a, b)] ∧ AllZero [e] [x] := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h⟩ := h
  obtain ⟨x, hx, hz⟩ := ivt_existsQ e a' b' h
  refine ⟨x, Roots.inBoxes_one.2 ?_, hz⟩
  have := Roots.inBoxes_one.1 hx
  have h1' : (a : ℝ) ≤ a' := by exact_mod_cast h1
  have h2' : (b' : ℝ) ≤ b := by exact_mod_cast h2
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Strict sign of `e.deriv 0` on `[a, b]` (`inc`: `> 0`; otherwise `< 0`). -/
def derivSignQ (e : IExpr) (a b : ℚ) (inc : Bool) (cert : Interval128.Dy.DCert) : Bool :=
  bif inc then Interval128.Dy.checkDQ (e.deriv 0) (Interval128.Dy.gGt 0) false cert
    (Interval128.Dy.boxes [(a, b)])
  else Interval128.Dy.checkDQ (e.deriv 0) (Interval128.Dy.gLt 0) true cert
    (Interval128.Dy.boxes [(a, b)])

theorem injOn_of_derivSignQ {e : IExpr} {a b : ℚ} {inc : Bool} {cert : Interval128.Dy.DCert}
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(a, b)]) e = true)
    (h : derivSignQ e a b inc cert = true) :
    Set.InjOn (fun t => e.denote [t]) (Set.Icc (a : ℝ) b) := by
  have hc := continuousOn_oneQ hd
  have hder : ∀ x ∈ interior (Set.Icc (a : ℝ) b),
      deriv (fun t => e.denote [t]) x = (e.deriv 0).denote [x] := by
    intro x hx
    exact (hasDerivAt_oneQ hd (interior_subset hx)).deriv
  cases inc
  · refine (strictAntiOn_of_deriv_neg (convex_Icc _ _) hc fun x hx => ?_).injOn
    rw [hder x hx]
    have := proveD_lt (e.deriv 0) _ 0 cert h [x] (Roots.inBoxes_one.2 (interior_subset hx))
    simpa using this
  · refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) hc fun x hx => ?_).injOn
    rw [hder x hx]
    have := proveD_gt (e.deriv 0) _ 0 cert h [x] (Roots.inBoxes_one.2 (interior_subset hx))
    simpa using this

/-- **Unique root in one variable** at 128: sign change plus a strict derivative sign. -/
theorem unique_oneQ (e : IExpr) (a b : ℚ) (inc : Bool) (cert : Interval128.Dy.DCert)
    (h : (ivtCheckQ e a b && derivSignQ e a b inc cert) = true) :
    ∃! x : ℝ, InBoxes [x] [(a, b)] ∧ AllZero [e] [x] := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨hi, hs⟩ := h
  have hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(a, b)]) e = true := by
    simp only [ivtCheckQ, Bool.and_eq_true] at hi; exact hi.1.2
  obtain ⟨x, hx, hx0⟩ := ivt_existsQ e a b hi
  refine ⟨x, ⟨hx, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  exact injOn_of_derivSignQ hd hs (Roots.inBoxes_one.1 hy) (Roots.inBoxes_one.1 hx)
    ((Roots.allZero_one.1 hy0).trans (Roots.allZero_one.1 hx0).symm)

end RealFP.I128Q
