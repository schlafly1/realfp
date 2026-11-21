/-
Soundness of derivative-based certificates (`Interval64.KF.checkD`): monotonicity and the
mean-value (centred) form, using `IExpr.diff` and Mathlib's `HasDerivAt`.
-/
import RealFPMathlib.IntervalSound
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits

noncomputable section

namespace RealFP

/-! ### Lists -/

theorem getD_set_eq {xs : List ℝ} {i : Nat} (hi : i < xs.length) (t : ℝ) (j : Nat) :
    (xs.set i t).getD j 0 = if j = i then t else xs.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [Ne.symm h, h]

theorem set_getD_self {xs : List ℝ} {i : Nat} (hi : i < xs.length) : xs.set i (xs.getD i 0) = xs := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_set]
  split_ifs with h
  · subst h; simp [List.getD_eq_getElem?_getD, hi]
  · rfl

/-! ### Real domain of differentiability -/

/-- `e` is differentiable at `xs` (denominators `≠ 0`, `√`/`log` arguments `> 0`, no `|·|`). -/
def Dom (xs : List ℝ) : IExpr → Prop
  | .var _ => True
  | .rat _ => True
  | .add a b => Dom xs a ∧ Dom xs b
  | .sub a b => Dom xs a ∧ Dom xs b
  | .mul a b => Dom xs a ∧ Dom xs b
  | .div a b => Dom xs a ∧ Dom xs b ∧ b.denote xs ≠ 0
  | .neg a => Dom xs a
  | .inv a => Dom xs a ∧ a.denote xs ≠ 0
  | .sqrt a => Dom xs a ∧ 0 < a.denote xs
  | .abs _ => False
  | .pow a _ => Dom xs a
  | .exp a => Dom xs a
  | .log a => Dom xs a ∧ 0 < a.denote xs
  | .sin a => Dom xs a
  | .cos a => Dom xs a

theorem hasDerivAt_denote {xs : List ℝ} {i : Nat} (hi : i < xs.length) :
    ∀ e : IExpr, Dom xs e →
      HasDerivAt (fun t => e.denote (xs.set i t)) ((e.diff i).denote xs) (xs.getD i 0) := by
  have hs := set_getD_self hi
  intro e
  induction e with
  | var j =>
    intro _
    by_cases h : j = i
    · subst h
      have : (fun t => (IExpr.var j).denote (xs.set j t)) = id := by
        funext t; show (xs.set j t).getD j 0 = t; rw [getD_set_eq hi]; simp
      rw [this]; simpa [IExpr.diff, IExpr.denote] using hasDerivAt_id (xs.getD j 0)
    · have : (fun t => (IExpr.var j).denote (xs.set i t)) = fun _ => xs.getD j 0 := by
        funext t; show (xs.set i t).getD j 0 = xs.getD j 0; rw [getD_set_eq hi]; simp [h]
      rw [this]
      have hb : Nat.beq j i = false := Bool.eq_false_iff.2 (fun h' => h (Nat.eq_of_beq_eq_true h'))
      simpa [IExpr.diff, IExpr.denote, hb] using hasDerivAt_const (xs.getD i 0) (xs.getD j 0)
  | rat q =>
    intro _; simpa [IExpr.diff, IExpr.denote] using hasDerivAt_const (xs.getD i 0) (q : ℝ)
  | add a b iha ihb => intro h; exact (iha h.1).add (ihb h.2)
  | sub a b iha ihb => intro h; exact (iha h.1).sub (ihb h.2)
  | mul a b iha ihb =>
    intro h
    have := (iha h.1).mul (ihb h.2)
    simp only [hs] at this
    exact this
  | div a b iha ihb =>
    intro h
    have := (iha h.1).div (ihb h.2.1) (by rw [hs]; exact h.2.2)
    simp only [hs] at this
    exact this
  | neg a iha => intro h; exact (iha h).neg
  | inv a iha =>
    intro h
    have := (iha h.1).inv (by rw [hs]; exact h.2)
    simp only [hs] at this
    convert this using 1
    · funext t; simp [IExpr.denote]
    · show -((a.diff i).denote xs / a.denote xs ^ 2) = _
      ring
  | sqrt a iha =>
    intro h
    have := (iha h.1).sqrt (by rw [hs]; exact h.2.ne')
    simp only [hs] at this
    refine this.congr_deriv ?_
    show _ = (a.diff i).denote xs / (((2 : ℚ) : ℝ) * Real.sqrt (a.denote xs))
    push_cast; rfl
  | abs a _ => intro h; exact h.elim
  | pow a n iha =>
    intro h
    have := (iha h).pow n
    simp only [hs] at this
    convert this using 1
    · funext t; simp [IExpr.denote]
    · show ((n : ℚ) : ℝ) * a.denote xs ^ (n - 1) * (a.diff i).denote xs = _
      push_cast; rfl
  | exp a iha =>
    intro h
    have := (iha h).exp
    simp only [hs] at this
    exact this
  | log a iha =>
    intro h
    have := (iha h.1).log (by rw [hs]; exact h.2.ne')
    simp only [hs] at this
    exact this
  | sin a iha =>
    intro h
    have := (iha h).sin
    simp only [hs] at this
    exact this
  | cos a iha =>
    intro h
    have := (iha h).cos
    simp only [hs] at this
    refine this.congr_deriv ?_
    show _ = -(Real.sin (a.denote xs) * (a.diff i).denote xs)
    ring

end RealFP
