/-
Soundness of the dyadic `(precision := 128)` checker (`Interval128/Dyadic.lean`) over `ℝ`.

* `evalQ_sound` — `e.denote xs` lies in `evalQ env e` whenever each `xs[i]` lies in `env[i]`.
* `checkQ_sound`, `prove_le` / `prove_lt` / `prove_ge` / `prove_gt` — what the tactic uses.

Number and interval lemmas: `I128DyBase.lean`; elementary functions: `I128DyTransc.lean`.
-/
import RealFPMathlib.I128DyTransc

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open Interval64.Spec Interval64Proofs.FloatBits

noncomputable section

namespace RealFP.I128Q

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-! ### Evaluation -/

omit [ExtTbl] [ExtSem] in
theorem getD_mem {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : ℕ) :
    mem (xs.getD i 0) (env.getD i DI.zero) := by
  induction h generalizing i with
  | nil =>
    simp only [List.getD_nil]
    exact ⟨by rintro l ⟨⟩; rw [val_zero], by rintro l ⟨⟩; rw [val_zero]⟩
  | cons hxX _ ih =>
    cases i with
    | zero => simpa using hxX
    | succ n => simpa using ih n

theorem evalQ_sound {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) :
    ∀ e : IExpr, mem (e.denote xs) (Interval128.Dy.evalQ env e) := by
  intro e
  induction e with
  | var i => exact getD_mem h i
  | rat q => exact mem_ofRat q
  | add a b iha ihb => exact mem_add iha ihb
  | sub a b iha ihb => exact mem_sub iha ihb
  | mul a b iha ihb => exact mem_mul iha ihb
  | div a b iha ihb => exact mem_div iha ihb
  | neg a iha => exact mem_neg iha
  | inv a iha => exact mem_inv iha
  | sqrt a iha => exact mem_sqrt iha
  | abs a iha => exact mem_abs iha
  | pow a n iha => exact mem_pow iha n
  | exp a iha => exact mem_exp iha
  | log a iha =>
    simp only [Interval128.Dy.evalQ]
    split
    · rename_i Y hY; exact mem_log? iha hY
    · exact mem_lift1 (.log (.var 0)) iha
  | sin a iha => exact mem_sin iha
  | cos a iha => exact mem_cos iha
  | pi => exact mem_pi
  | atan a iha => exact mem_lift1 (.atan (.var 0)) iha
  | atan2 a b iha ihb => exact mem_lift2 (.atan2 (.var 0) (.var 1)) iha ihb
  | sinh a iha => exact mem_sinh iha
  | cosh a iha => exact mem_cosh iha
  | tanh a iha => exact mem_tanh iha
  | log2 a iha =>
    simp only [Interval128.Dy.evalQ]
    split
    · rename_i Y hY
      have := mem_div (mem_log? iha hY) (mem_logConst (q := 2) (by norm_num))
      simpa [IExpr.denote, Real.logb] using this
    · exact mem_lift1 (.log2 (.var 0)) iha
  | log10 a iha =>
    simp only [Interval128.Dy.evalQ]
    split
    · rename_i Y hY
      have := mem_div (mem_log? iha hY) (mem_logConst (q := 10) (by norm_num))
      simpa [IExpr.denote, Real.logb] using this
    · exact mem_lift1 (.log10 (.var 0)) iha
  | tan a iha => exact mem_lift1 (.tan (.var 0)) iha
  | asin a iha => exact mem_lift1 (.asin (.var 0)) iha
  | acos a iha => exact mem_lift1 (.acos (.var 0)) iha
  | ext k d a _ iha => exact mem_lift1 (.ext k d (.var 0)) iha

/-! ### Bisection -/

omit [ExtTbl] [ExtSem] in
theorem split_mem {X : DI} {y : ℝ} (d : Dy) (hy : mem y X) :
    mem y (Interval128.Dy.leftAt X d) ∨ mem y (Interval128.Dy.rightAt X d) := by
  rcases le_total y (val d) with h | h
  · exact Or.inl ⟨hy.1, by rintro u ⟨⟩; exact h⟩
  · exact Or.inr ⟨by rintro l ⟨⟩; exact h, hy.2⟩

omit [ExtTbl] [ExtSem] in
theorem forall2_set {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : ℕ) {Y : DI}
    (hY : mem (xs.getD i 0) Y) : List.Forall₂ mem xs (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX _ ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using hY) (by assumption)
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using hY))

theorem checkQ_sound (e : IExpr) (g : DI → Bool) (P : ℝ → Prop)
    (hg : ∀ F, g F = true → ∀ y, mem y F → P y) :
    ∀ (c : Interval128.Dy.Cert) (env : List DI) (xs : List ℝ),
      List.Forall₂ mem xs env → Interval128.Dy.checkQ e g c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro env xs hxs hc
    exact hg _ hc _ (evalQ_sound hxs e)
  | split i q l r ihl ihr =>
    intro env xs hxs hc
    simp only [Interval128.Dy.checkQ, Bool.and_eq_true] at hc
    rcases split_mem q (getD_mem hxs i) with h1 | h1
    · exact ihl _ xs (forall2_set hxs i h1) hc.1
    · exact ihr _ xs (forall2_set hxs i h1) hc.2

omit [ExtSem] in
theorem checkQ_split_of (e : IExpr) (g : DI → Bool) (i : ℕ) (q : Dy)
    (l r : Interval128.Dy.Cert) (env : List DI)
    (hl : Interval128.Dy.checkQ e g l (env.set i (Interval128.Dy.leftAt (env.getD i DI.zero) q)) = true)
    (hr : Interval128.Dy.checkQ e g r (env.set i (Interval128.Dy.rightAt (env.getD i DI.zero) q)) = true) :
    Interval128.Dy.checkQ e g (.split i q l r) env = true := by
  simp only [Interval128.Dy.checkQ, hl, hr, Bool.and_self]

/-! ### Goal predicates -/

omit [ExtTbl] [ExtSem] in
theorem gLe_sound (c : ℚ) : ∀ F, Interval128.Dy.gLe c F = true → ∀ y, mem y F → y ≤ (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Dy.gLe at hg
  split at hg
  · rename_i u hu
    have h2 : ((Interval128.Dy.toRat u : ℚ) : ℝ) ≤ c := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.2 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gLt_sound (c : ℚ) : ∀ F, Interval128.Dy.gLt c F = true → ∀ y, mem y F → y < (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Dy.gLt at hg
  split at hg
  · rename_i u hu
    have h2 : ((Interval128.Dy.toRat u : ℚ) : ℝ) < c := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.2 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGe_sound (c : ℚ) : ∀ F, Interval128.Dy.gGe c F = true → ∀ y, mem y F → (c : ℝ) ≤ y := by
  intro F hg y hy
  unfold Interval128.Dy.gGe at hg
  split at hg
  · rename_i u hu
    have h2 : (c : ℝ) ≤ ((Interval128.Dy.toRat u : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.1 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGt_sound (c : ℚ) : ∀ F, Interval128.Dy.gGt c F = true → ∀ y, mem y F → (c : ℝ) < y := by
  intro F hg y hy
  unfold Interval128.Dy.gGt at hg
  split at hg
  · rename_i u hu
    have h2 : (c : ℝ) < ((Interval128.Dy.toRat u : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.1 u hu]
  · simp at hg

/-! ### Entry points for the tactic -/

omit [ExtTbl] [ExtSem] in
theorem boxes_mem {xs : List ℝ} {bs : List (ℚ × ℚ)} (h : InBoxes xs bs) :
    List.Forall₂ mem xs (Interval128.Dy.boxes bs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons (mem_ofRatI hx.1 hx.2) ih

theorem prove_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gLe c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkQ_sound e _ _ (gLe_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gLt c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkQ_sound e _ _ (gLt_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gGe c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkQ_sound e _ _ (gGe_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gGt c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkQ_sound e _ _ (gGt_sound c) cert _ xs (boxes_mem hxs) h

end RealFP.I128Q
