/-
`evalK` (kernel fast path) computes the same interval as `evalI` (`Interval64` semantics).
-/
import Interval64Proofs.KernelInterval
import Interval64.Kernel.Reflect

set_option linter.unusedSimpArgs false

namespace Interval64.KF

theorem toI_zeroK : toI zeroK = zeroI := by
  show (⟨toF 0, toF 0⟩ : Interval64) = ⟨0, 0⟩; rw [toF_zero]

theorem wf_zeroK : WF zeroK := ⟨zero_lt, zero_lt⟩

theorem getD_toI (env : List KI) (i : Nat) :
    toI (env.getD i zeroK) = (env.map toI).getD i zeroI := by
  induction env generalizing i with
  | nil => simp [toI_zeroK]
  | cons X t ih =>
    cases i with
    | zero => simp
    | succ n => simp only [List.getD_cons_succ, List.map_cons]; exact ih n

theorem getD_wf {env : List KI} (h : ∀ X ∈ env, WF X) (i : Nat) : WF (env.getD i zeroK) := by
  induction env generalizing i with
  | nil => exact wf_zeroK
  | cons X t ih =>
    cases i
    · exact h X (by simp)
    · exact ih (fun Y hY => h Y (by simp [hY])) _

theorem sqrtK_toI {X : KI} (h : WF X) : toI (sqrtK X) = sqrtI (toI X) ∧ WF (sqrtK X) := by
  unfold sqrtK sqrtI
  have e : decide ((toI X).lo < 0) = lt X.lo 0 := by
    show decide (toF X.lo < 0) = _; rw [← toF_zero, lt_toF h.1 zero_lt]
  rw [e]
  cases lt X.lo 0
  · exact ⟨sqrt_toI h, sqrt_wf h⟩
  · simp only [Bool.cond_true, ite_true]
    exact ⟨by rw [hull_toI wf_zeroK (sqrt_wf h), toI_zeroK, sqrt_toI h],
      hull_wf wf_zeroK (sqrt_wf h)⟩

theorem logK_toI {X : KI} (h : WF X) : toI (logK X) = logI (toI X) ∧ WF (logK X) := by
  unfold logK logI
  have e : decide (0 < (toI X).lo) = lt 0 X.lo := by
    show decide (0 < toF X.lo) = _; rw [← toF_zero, lt_toF zero_lt h.1]
  rw [e]
  cases lt 0 X.lo
  · exact ⟨toI_whole, wf_whole⟩
  · exact log_toI h

theorem evalK_toI {env : List KI} (h : ∀ X ∈ env, WF X) :
    ∀ e : IExpr, toI (evalK env e) = evalI (env.map toI) e ∧ WF (evalK env e) := by
  intro e
  induction e with
  | var i => exact ⟨getD_toI env i, getD_wf h i⟩
  | rat q => exact ofRat_toI q
  | add a b iha ihb =>
    exact ⟨by simp only [evalK, evalI]; rw [add_toI iha.2 ihb.2, iha.1, ihb.1],
      add_wf iha.2 ihb.2⟩
  | sub a b iha ihb =>
    exact ⟨by simp only [evalK, evalI]; rw [sub_toI iha.2 ihb.2, iha.1, ihb.1],
      sub_wf iha.2 ihb.2⟩
  | mul a b iha ihb =>
    exact ⟨by simp only [evalK, evalI]; rw [mul_toI iha.2 ihb.2, iha.1, ihb.1],
      mul_wf iha.2 ihb.2⟩
  | div a b iha ihb =>
    exact ⟨by simp only [evalK, evalI]; rw [mul_toI iha.2 (inv_wf ihb.2), inv_toI ihb.2, iha.1, ihb.1],
      mul_wf iha.2 (inv_wf ihb.2)⟩
  | neg a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [neg_toI iha.2, iha.1], neg_wf iha.2⟩
  | inv a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [inv_toI iha.2, iha.1], inv_wf iha.2⟩
  | sqrt a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(sqrtK_toI iha.2).1, iha.1], (sqrtK_toI iha.2).2⟩
  | abs a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [abs_toI iha.2, iha.1], abs_wf iha.2⟩
  | pow a n iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(pown_toI iha.2 n).1, iha.1], (pown_toI iha.2 n).2⟩
  | exp a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(exp_toI iha.2).1, iha.1], (exp_toI iha.2).2⟩
  | log a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(logK_toI iha.2).1, iha.1], (logK_toI iha.2).2⟩
  | sin a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(sin_toI iha.2).1, iha.1], (sin_toI iha.2).2⟩
  | cos a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(cos_toI iha.2).1, iha.1], (cos_toI iha.2).2⟩

theorem boxes_wf (bs : List (Rat × Rat)) : ∀ X ∈ boxes bs, WF X := by
  induction bs with
  | nil => simp [boxes]
  | cons b t ih =>
    intro X hX
    simp only [boxes, List.mem_cons] at hX
    rcases hX with rfl | hX
    · exact (ofRatInterval_toI _ _).2
    · exact ih X hX

theorem set_wf {env : List KI} (h : ∀ X ∈ env, WF X) (i : Nat) {Y : KI} (hY : WF Y) :
    ∀ X ∈ env.set i Y, WF X := by
  intro X hX
  rcases List.mem_or_eq_of_mem_set hX with h1 | h1
  · exact h X h1
  · rw [h1]; exact hY

end Interval64.KF
