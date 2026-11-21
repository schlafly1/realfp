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

theorem atan_toI {a : KI} (ha : WF a) : toI (KI.atan a) = Interval64.atan (toI a) ∧ WF (KI.atan a) := by
  unfold Interval64.atan KI.atan
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
    simp only [Directed.atanDown, Directed.atanUp, Directed.atanDownSpec, Directed.atanUpSpec,
      toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem const_toI (l h : UInt64) : toI ⟨l.toNat, h.toNat⟩ = ⟨Float.ofBits l, Float.ofBits h⟩ ∧
    WF ⟨l.toNat, h.toNat⟩ := by
  refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
  simp only [toI, toF_ofBits]

theorem pi_toI : toI KI.pi = Interval64.pi ∧ WF KI.pi := const_toI _ _
theorem halfPi_toI : toI KI.halfPi = halfPi ∧ WF KI.halfPi := const_toI _ _
theorem negHalfPi_toI : toI KI.negHalfPi = negHalfPi ∧ WF KI.negHalfPi := const_toI _ _
theorem argHull_toI : toI KI.argHull = argHull ∧ WF KI.argHull := const_toI _ _

theorem atan2K_toI {y x : KI} (hy : WF y) (hx : WF x) :
    toI (atan2K y x) = atan2I (toI y) (toI x) ∧ WF (atan2K y x) := by
  unfold atan2K atan2I
  rw [anyNan_toI hy hx]
  have e1 : decide (0 < (toI x).lo) = lt 0 x.lo := by
    show decide (0 < toF x.lo) = _; rw [← toF_zero, lt_toF zero_lt hx.1]
  have e2 : decide (0 < (toI y).lo) = lt 0 y.lo := by
    show decide (0 < toF y.lo) = _; rw [← toF_zero, lt_toF zero_lt hy.1]
  have e3 : decide ((toI y).hi < 0) = lt y.hi 0 := by
    show decide (toF y.hi < 0) = _; rw [← toF_zero, lt_toF hy.2 zero_lt]
  rw [e1, e2, e3]
  have hyx := mul_wf hy (inv_wf hx)
  have hxy := mul_wf hx (inv_wf hy)
  cases KI.anyNan y x
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    cases lt 0 x.lo
    · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
      cases lt 0 y.lo
      · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
        cases lt y.hi 0
        · exact argHull_toI
        · simp only [Bool.cond_true, ite_true]
          refine ⟨?_, sub_wf negHalfPi_toI.2 (atan_toI hxy).2⟩
          rw [sub_toI negHalfPi_toI.2 (atan_toI hxy).2, negHalfPi_toI.1, (atan_toI hxy).1,
            mul_toI hx (inv_wf hy), inv_toI hy]
      · simp only [Bool.cond_true, ite_true]
        refine ⟨?_, sub_wf halfPi_toI.2 (atan_toI hxy).2⟩
        rw [sub_toI halfPi_toI.2 (atan_toI hxy).2, halfPi_toI.1, (atan_toI hxy).1,
          mul_toI hx (inv_wf hy), inv_toI hy]
    · simp only [Bool.cond_true, ite_true]
      refine ⟨?_, (atan_toI hyx).2⟩
      rw [(atan_toI hyx).1, mul_toI hy (inv_wf hx), inv_toI hx]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

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
  | pi => exact pi_toI
  | atan a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(atan_toI iha.2).1, iha.1], (atan_toI iha.2).2⟩
  | atan2 a b iha ihb =>
    exact ⟨by simp only [evalK, evalI]; rw [(atan2K_toI iha.2 ihb.2).1, iha.1, ihb.1],
      (atan2K_toI iha.2 ihb.2).2⟩

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
