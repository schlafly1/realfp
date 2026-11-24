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

theorem sinh_toI {a : KI} (ha : WF a) : toI (KI.sinh a) = Interval64.sinh (toI a) ∧ WF (KI.sinh a) := by
  unfold Interval64.sinh KI.sinh
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
    simp only [Directed.sinhDown, Directed.sinhUp, Directed.sinhDownSpec, Directed.sinhUpSpec,
      toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem tanh_toI {a : KI} (ha : WF a) : toI (KI.tanh a) = Interval64.tanh (toI a) ∧ WF (KI.tanh a) := by
  unfold Interval64.tanh KI.tanh
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
    simp only [Directed.tanhDown, Directed.tanhUp, Directed.tanhDownSpec, Directed.tanhUpSpec,
      toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem coshD_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    Directed.coshDown (toF x) = toF (KI.coshD x) := by
  simp only [KI.coshD, Directed.coshDown, Directed.coshDownSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]

theorem coshU_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    Directed.coshUp (toF x) = toF (KI.coshU x) := by
  simp only [KI.coshU, Directed.coshUp, Directed.coshUpSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]

theorem cosh_toI {a : KI} (ha : WF a) : toI (KI.cosh a) = Interval64.cosh (toI a) ∧ WF (KI.cosh a) := by
  unfold Interval64.cosh KI.cosh
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    have b1 : KI.coshD a.lo < 2 ^ 64 := UInt64.toNat_lt _
    have b2 : KI.coshD a.hi < 2 ^ 64 := UInt64.toNat_lt _
    have b3 : KI.coshU a.lo < 2 ^ 64 := UInt64.toNat_lt _
    have b4 : KI.coshU a.hi < 2 ^ 64 := UInt64.toNat_lt _
    have o1 : KI.oneDown < 2 ^ 64 := UInt64.toNat_lt _
    simp only [← toF_zero, le_toF zero_lt ha.1, le_toF ha.2 zero_lt, coshD_toF ha.1 h.1,
      coshD_toF ha.2 h.2, coshU_toF ha.1 h.1, coshU_toF ha.2 h.2, fmax_toF b3 b4]
    cases le 0 a.lo
    · cases le a.hi 0
      · refine ⟨?_, o1, fmax_lt b3 b4⟩
        simp only [Bool.cond_false, Bool.false_eq_true, ite_false, decide_false]
        rw [KI.oneDown, toF_toNat]
      · exact ⟨by simp, b2, b3⟩
    · exact ⟨by simp, b1, b4⟩
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem logBLo_toF (ten : Bool) {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    logBLo ten (toF x) = toF (KI.logBLo ten x) ∧ KI.logBLo ten x < 2 ^ 64 := by
  unfold logBLo KI.logBLo
  rw [toBits_toF_of_not_nan hx hn]
  have hb : (Hyp.logBBitsD ten (UInt64.ofNat x) false).1.toNat < 2 ^ 64 := UInt64.toNat_lt _
  generalize Spec.unpackBits (UInt64.ofNat x) = u
  cases u
  all_goals first | (rename_i s m e h; cases s) | (rename_i s; cases s) | skip
  all_goals cases ten
  all_goals simp [Directed.log2Down, Directed.log2DownSpec, Directed.log10Down,
      Directed.log10DownSpec, Hyp.log2DownBits, Hyp.log10DownBits, toF_ofBits,
      toBits_toF_of_not_nan hx hn, posInf_toNat, negInf_toNat, qNaN_toNat, hb]
  all_goals decide

theorem logB_toI (ten : Bool) {a : KI} (ha : WF a) :
    toI (KI.logB ten a) = Interval64.logB ten (toI a) ∧ WF (KI.logB ten a) := by
  unfold Interval64.logB KI.logB
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    rw [toBits_toF_of_not_nan ha.2 h.2]
    have hl := logBLo_toF ten ha.1 h.1
    have hb : (Hyp.logBBitsD ten (UInt64.ofNat a.hi) true).1.toNat < 2 ^ 64 := UInt64.toNat_lt _
    generalize Spec.unpackBits (UInt64.ofNat a.hi) = u
    cases u
    all_goals first | (rename_i s m e h'; cases s) | (rename_i s; cases s) | skip
    all_goals cases ten
    all_goals simp [Directed.log2Up, Directed.log2UpSpec, Directed.log10Up, Directed.log10UpSpec,
        Hyp.log2UpBits, Hyp.log10UpBits, toF_ofBits, toBits_toF_of_not_nan ha.2 h.2,
        posInf_toNat, negInf_toNat, qNaN_toNat, hb, hl.1, hl.2, toI_invalid, toI, KI.invalid,
        toF_qNaN, invalid, WF]
    all_goals decide
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem const_toI (l h : UInt64) : toI ⟨l.toNat, h.toNat⟩ = ⟨Float.ofBits l, Float.ofBits h⟩ ∧
    WF ⟨l.toNat, h.toNat⟩ := by
  refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
  simp only [toI, toF_ofBits]

theorem pi_toI : toI KI.pi = Interval64.pi ∧ WF KI.pi := const_toI _ _
theorem halfPi_toI : toI KI.halfPi = halfPi ∧ WF KI.halfPi := const_toI _ _
theorem negHalfPi_toI : toI KI.negHalfPi = negHalfPi ∧ WF KI.negHalfPi := const_toI _ _
theorem argHull_toI : toI KI.argHull = argHull ∧ WF KI.argHull := const_toI _ _

theorem tan_toI {a : KI} (ha : WF a) : toI (KI.tan a) = Interval64.tan (toI a) ∧ WF (KI.tan a) := by
  unfold Interval64.tan KI.tan
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    simp only [toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2]
    generalize Spec.bitsToRat? (UInt64.ofNat a.lo) = qa
    generalize Spec.bitsToRat? (UInt64.ofNat a.hi) = qb
    rcases qa with _ | x <;> rcases qb with _ | y
    · exact ⟨toI_whole, wf_whole⟩
    · exact ⟨toI_whole, wf_whole⟩
    · exact ⟨toI_whole, wf_whole⟩
    · dsimp only
      cases Trig.avoids x y 1 && Trig.avoids x y 3
      · exact ⟨toI_whole, wf_whole⟩
      · refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
        simp only [toI, Directed.tanDown, Directed.tanUp, Directed.tanDownSpec, Directed.tanUpSpec,
          toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits, ite_true]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem lo_toI' (X : KI) : (toI X).lo = toF X.lo := rfl
theorem hi_toI' (X : KI) : (toI X).hi = toF X.hi := rfl

theorem negOne_toF : (-1 : Float) = toF KI.negOneBits := by
  rw [← toF_one, neg_toF oneBits_lt]; rfl

theorem negOneBits_lt : KI.negOneBits < 2 ^ 64 := negBits_lt oneBits_lt

theorem asinLo_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    asinLo (toF x) = toF (KI.asinLo x) ∧ KI.asinLo x < 2 ^ 64 := by
  unfold asinLo KI.asinLo
  simp only [negOne_toF]
  simp only [← toF_one]
  rw [lt_toF hx negOneBits_lt, lt_toF oneBits_lt hx]
  cases lt x KI.negOneBits <;> cases lt KI.oneBits x
  · rw [Bool.cond_false, Bool.cond_false, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_false _ _ (eq_false Bool.false_ne_true)]
    refine ⟨?_, UInt64.toNat_lt _⟩
    simp only [Directed.asinDown, Directed.asinDownSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]
  · rw [Bool.cond_false, Bool.cond_true, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show halfPi.lo = toF KI.halfPi.lo by rw [← halfPi_toI.1, lo_toI']), halfPi_toI.2.1⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show negHalfPi.lo = toF KI.negHalfPi.lo by rw [← negHalfPi_toI.1, lo_toI']), negHalfPi_toI.2.1⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show negHalfPi.lo = toF KI.negHalfPi.lo by rw [← negHalfPi_toI.1, lo_toI']), negHalfPi_toI.2.1⟩

theorem asinHi_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    asinHi (toF x) = toF (KI.asinHi x) ∧ KI.asinHi x < 2 ^ 64 := by
  unfold asinHi KI.asinHi
  simp only [negOne_toF]
  simp only [← toF_one]
  rw [lt_toF hx negOneBits_lt, lt_toF oneBits_lt hx]
  cases lt x KI.negOneBits <;> cases lt KI.oneBits x
  · rw [Bool.cond_false, Bool.cond_false, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_false _ _ (eq_false Bool.false_ne_true)]
    refine ⟨?_, UInt64.toNat_lt _⟩
    simp only [Directed.asinUp, Directed.asinUpSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]
  · rw [Bool.cond_false, Bool.cond_true, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show halfPi.hi = toF KI.halfPi.hi by rw [← halfPi_toI.1, hi_toI']), halfPi_toI.2.2⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show negHalfPi.hi = toF KI.negHalfPi.hi by rw [← negHalfPi_toI.1, hi_toI']), negHalfPi_toI.2.2⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show negHalfPi.hi = toF KI.negHalfPi.hi by rw [← negHalfPi_toI.1, hi_toI']), negHalfPi_toI.2.2⟩

theorem acosLo_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    acosLo (toF x) = toF (KI.acosLo x) ∧ KI.acosLo x < 2 ^ 64 := by
  unfold acosLo KI.acosLo
  simp only [negOne_toF]
  simp only [← toF_one]
  rw [lt_toF hx negOneBits_lt, lt_toF oneBits_lt hx]
  cases lt x KI.negOneBits <;> cases lt KI.oneBits x
  · rw [Bool.cond_false, Bool.cond_false, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_false _ _ (eq_false Bool.false_ne_true)]
    refine ⟨?_, UInt64.toNat_lt _⟩
    simp only [Directed.acosDown, Directed.acosDownSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]
  · rw [Bool.cond_false, Bool.cond_true, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show (0 : Float) = toF 0 from toF_zero.symm), zero_lt⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show pi.lo = toF KI.pi.lo by rw [← pi_toI.1, lo_toI']), pi_toI.2.1⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show pi.lo = toF KI.pi.lo by rw [← pi_toI.1, lo_toI']), pi_toI.2.1⟩

theorem acosHi_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    acosHi (toF x) = toF (KI.acosHi x) ∧ KI.acosHi x < 2 ^ 64 := by
  unfold acosHi KI.acosHi
  simp only [negOne_toF]
  simp only [← toF_one]
  rw [lt_toF hx negOneBits_lt, lt_toF oneBits_lt hx]
  cases lt x KI.negOneBits <;> cases lt KI.oneBits x
  · rw [Bool.cond_false, Bool.cond_false, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_false _ _ (eq_false Bool.false_ne_true)]
    refine ⟨?_, UInt64.toNat_lt _⟩
    simp only [Directed.acosUp, Directed.acosUpSpec, toBits_toF_of_not_nan hx hn, toF_ofBits]
  · rw [Bool.cond_false, Bool.cond_true, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true), ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show (0 : Float) = toF 0 from toF_zero.symm), zero_lt⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show pi.hi = toF KI.pi.hi by rw [← pi_toI.1, hi_toI']), pi_toI.2.2⟩
  · rw [Bool.cond_true, ite_cond_eq_true _ _ (eq_true rfl)]
    exact ⟨(show pi.hi = toF KI.pi.hi by rw [← pi_toI.1, hi_toI']), pi_toI.2.2⟩

theorem asin_toI {a : KI} (ha : WF a) : toI (KI.asin a) = Interval64.asin (toI a) ∧ WF (KI.asin a) := by
  unfold Interval64.asin KI.asin
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    have l := asinLo_toF ha.1 h.1
    have u := asinHi_toF ha.2 h.2
    exact ⟨by rw [l.1, u.1], l.2, u.2⟩
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem acos_toI {a : KI} (ha : WF a) : toI (KI.acos a) = Interval64.acos (toI a) ∧ WF (KI.acos a) := by
  unfold Interval64.acos KI.acos
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    have l := acosLo_toF ha.2 h.2
    have u := acosHi_toF ha.1 h.1
    exact ⟨by rw [l.1, u.1], l.2, u.2⟩
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩


theorem logBK_toI (ten : Bool) {X : KI} (h : WF X) :
    toI (logBK ten X) = logBI ten (toI X) ∧ WF (logBK ten X) := by
  unfold logBK logBI
  have e : decide (0 < (toI X).lo) = lt 0 X.lo := by
    show decide (0 < toF X.lo) = _; rw [← toF_zero, lt_toF zero_lt h.1]
  rw [e]
  cases lt 0 X.lo
  · exact ⟨toI_whole, wf_whole⟩
  · exact logB_toI ten h

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

theorem toNat_toBits_lt (f : Float) : f.toBits.toNat < 2 ^ 64 := f.toBits.toNat_lt

theorem isNaN_toBits (f : Float) : isNaN f.toBits.toNat = f.isNaN := by
  have hx := toNat_toBits_lt f
  rw [← isNaN_toF hx]
  show (Spec.unpackBits (toF _).toBits).isNaN = (Spec.unpackBits f.toBits).isNaN
  rw [unpack_toF hx, ← unpackBits_ofNat hx, UInt64.ofNat_toNat]

theorem toBits_toF_toBits {f : Float} (h : f.isNaN = false) :
    (toF f.toBits.toNat).toBits = f.toBits := by
  rw [toBits_toF_of_not_nan (toNat_toBits_lt f) (by rw [isNaN_toBits]; exact h),
    UInt64.ofNat_toNat]

theorem ofI_wf (X : Interval64) : WF (ofI X) := ⟨toNat_toBits_lt _, toNat_toBits_lt _⟩

theorem toIv_eq (X : KI) : toIv X = toI X := rfl

theorem extK_toI [ExtTbl] (k : Nat) {Y : KI} (hY : WF Y) :
    toI (extK k Y) = extI k (toI Y) ∧ WF (extK k Y) := by
  have hs : ∀ Z : KI, WF (sanitizeK Z) := by
    intro Z; unfold sanitizeK
    cases h1 : Nat.blt Z.lo (2 ^ 64) <;> cases h2 : Nat.blt Z.hi (2 ^ 64) <;>
      simp only [Bool.and_true, Bool.and_false, Bool.cond_true, Bool.cond_false]
    all_goals first | exact wf_whole | exact ⟨Nat.blt_eq ▸ h1, Nat.blt_eq ▸ h2⟩
  unfold extK extI
  simp only [toI, isNaN_toF hY.1, isNaN_toF hY.2]
  cases hl : isNaN Y.lo <;> cases hh : isNaN Y.hi <;>
    simp only [Bool.or_true, Bool.or_false, Bool.cond_true, Bool.cond_false, ite_true,
      Bool.false_eq_true, ite_false]
  · have e : ofI ⟨toF Y.lo, toF Y.hi⟩ = Y := by
      cases Y with
      | mk lo hi =>
        simp only [ofI, toBits_toF_of_not_nan hY.1 hl, toBits_toF_of_not_nan hY.2 hh,
          UInt64.toNat_ofNat_of_lt' hY.1, UInt64.toNat_ofNat_of_lt' hY.2]
    rw [e]; exact ⟨rfl, hs _⟩
  all_goals exact ⟨toI_whole, wf_whole⟩

section
variable [ExtTbl]

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
  | sinh a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(sinh_toI iha.2).1, iha.1], (sinh_toI iha.2).2⟩
  | cosh a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(cosh_toI iha.2).1, iha.1], (cosh_toI iha.2).2⟩
  | tanh a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(tanh_toI iha.2).1, iha.1], (tanh_toI iha.2).2⟩
  | log2 a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(logBK_toI false iha.2).1, iha.1],
      (logBK_toI false iha.2).2⟩
  | log10 a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(logBK_toI true iha.2).1, iha.1],
      (logBK_toI true iha.2).2⟩
  | tan a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(tan_toI iha.2).1, iha.1], (tan_toI iha.2).2⟩
  | asin a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(asin_toI iha.2).1, iha.1], (asin_toI iha.2).2⟩
  | acos a iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(acos_toI iha.2).1, iha.1], (acos_toI iha.2).2⟩
  | ext k _ a _ iha =>
    exact ⟨by simp only [evalK, evalI]; rw [(extK_toI k iha.2).1, iha.1], (extK_toI k iha.2).2⟩

end

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
