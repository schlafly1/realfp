/-
Soundness of the reflective interval checker (`Interval64.KF.checkK`) over `ℝ`.

* `IExpr.denote xs e : ℝ` — real value of an expression (`xs` = values of the variables).
* `eval_sound` — `denote xs e ∈ evalI env e` whenever each `xs[i] ∈ env[i]`.
* `checkK_sound` — a bisection certificate accepted by `checkK` proves a goal predicate for every
  point of the box.
* `prove_le` / `prove_lt` / `prove_ge` / `prove_gt` — the statements the `interval` tactic uses.
-/
import RealFPMathlib.Conv
import RealFPMathlib.Ops
import RealFPMathlib.Mem
import RealFPMathlib.Tight
import RealFPMathlib.Unbounded
import RealFPMathlib.Transc
import RealFPMathlib.Trig
import RealFPMathlib.InvTrig
import Interval64Proofs.KernelReflect

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits
open RealFP.Transc RealFP.Trig RealFP.InvTrig

noncomputable section

namespace RealFP

/-- Real value of an expression; `xs` gives the variables (missing ones are `0`). -/
def _root_.Interval64.KF.IExpr.denote (xs : List ℝ) : IExpr → ℝ
  | .var i => xs.getD i 0
  | .rat q => (q : ℝ)
  | .add a b => a.denote xs + b.denote xs
  | .sub a b => a.denote xs - b.denote xs
  | .mul a b => a.denote xs * b.denote xs
  | .div a b => a.denote xs / b.denote xs
  | .neg a => -a.denote xs
  | .inv a => (a.denote xs)⁻¹
  | .sqrt a => Real.sqrt (a.denote xs)
  | .abs a => |a.denote xs|
  | .pow a n => a.denote xs ^ n
  | .exp a => Real.exp (a.denote xs)
  | .log a => Real.log (a.denote xs)
  | .sin a => Real.sin (a.denote xs)
  | .cos a => Real.cos (a.denote xs)
  | .pi => Real.pi
  | .atan a => Real.arctan (a.denote xs)
  | .atan2 a b => Complex.arg (((b.denote xs : ℝ) : ℂ) + ((a.denote xs : ℝ) : ℂ) * Complex.I)

theorem zero_mem_zeroI : (0 : ℝ) ∈ zeroI.toSet := by
  have h := mem_toSet_ofRat 0
  have e1 : KI.ofRat 0 = zeroK := by
    have h1 : (KI.ofRat 0).lo = 0 := by decide +kernel
    have h2 : (KI.ofRat 0).hi = 0 := by decide +kernel
    cases hk : KI.ofRat 0; simp_all [zeroK]
  have e : ofRat 0 = zeroI := by rw [← (ofRat_toI 0).1, e1, toI_zeroK]
  rw [e] at h; simpa using h

theorem getD_mem {xs : List ℝ} {env : List Interval64}
    (h : List.Forall₂ (fun x X => x ∈ X.toSet) xs env) (i : Nat) :
    xs.getD i 0 ∈ (env.getD i zeroI).toSet := by
  induction h generalizing i with
  | nil => simpa using zero_mem_zeroI
  | cons hxX _ ih =>
    cases i with
    | zero => simpa using hxX
    | succ n => simpa using ih n

theorem sqrtI_mem {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) : Real.sqrt x ∈ (sqrtI X).toSet := by
  unfold sqrtI
  by_cases h0 : 0 ≤ x
  · have hs := mem_toSet_sqrt hx h0
    split_ifs
    · exact mem_hull_right hs
    · exact hs
  · push Not at h0
    rw [Real.sqrt_eq_zero'.2 h0.le]
    obtain ⟨⟨hl, hl'⟩, -⟩ := mem_toSet_iff_toE.1 hx
    split_ifs with hlt
    · exact mem_hull_left zero_mem_zeroI
    · exfalso
      have hz : (0 : Float).isNaN = false := by decide +kernel
      have : ¬ X.lo < 0 := by simpa using hlt
      rw [float_lt_iff_toE hl hz] at this
      have e0 : (0 : Float).toE = ((0 : ℝ) : EReal) := by simp
      rw [e0, not_lt] at this
      have := le_trans this hl'
      exact absurd (EReal.coe_le_coe_iff.1 this) (not_le.2 h0)

theorem logI_mem {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) : Real.log x ∈ (logI X).toSet := by
  unfold logI
  split_ifs with hlt
  · obtain ⟨⟨hl, hl'⟩, -⟩ := mem_toSet_iff_toE.1 hx
    have hz : (0 : Float).isNaN = false := by decide +kernel
    have h1 : (0 : Float) < X.lo := by simpa using hlt
    rw [float_lt_iff_toE hz hl] at h1
    have e0 : (0 : Float).toE = ((0 : ℝ) : EReal) := by simp
    rw [e0] at h1
    have := lt_of_lt_of_le h1 hl'
    exact log_mem_toSet hx (EReal.coe_lt_coe_iff.1 this)
  · exact mem_toSet_whole _

theorem atan2I_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) ∈ (atan2I Y X).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan Y X = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  unfold atan2I
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : 0 < X.lo
  · simp only [h1, decide_true, ↓reduceIte]
    have h0 : (0 : EReal) < X.lo.toE := (zero_lt_iff_toE hXl).1 h1
    have hxp : 0 < x := EReal.coe_pos.1 (lt_of_lt_of_le h0 hXl')
    rw [arg_right hxp, div_eq_mul_inv]
    exact atan_mem_toSet (mem_toSet_mul hy (mem_inv hx))
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : 0 < Y.lo
    · simp only [h2, decide_true, ↓reduceIte]
      have h0 : (0 : EReal) < Y.lo.toE := (zero_lt_iff_toE hYl).1 h2
      have hyp : 0 < y := EReal.coe_pos.1 (lt_of_lt_of_le h0 hYl')
      rw [arg_upper hyp, div_eq_mul_inv]
      exact sub_mem_toSet halfPi_mem_toSet (atan_mem_toSet (mem_toSet_mul hx (mem_inv hy)))
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : Y.hi < 0
      · simp only [h3, decide_true, ↓reduceIte]
        have h0 : Y.hi.toE < (0 : EReal) := (lt_zero_iff_toE hYh).1 h3
        have hyn : y < 0 := EReal.coe_neg'.1 (lt_of_le_of_lt hYh' h0)
        rw [arg_lower hyn, div_eq_mul_inv]
        exact sub_mem_toSet negHalfPi_mem_toSet (atan_mem_toSet (mem_toSet_mul hx (mem_inv hy)))
      · simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact arg_mem_argHull _

theorem eval_sound {xs : List ℝ} {env : List Interval64}
    (h : List.Forall₂ (fun x X => x ∈ X.toSet) xs env) :
    ∀ e : IExpr, e.denote xs ∈ (evalI env e).toSet := by
  intro e
  induction e with
  | var i => exact getD_mem h i
  | rat q => exact mem_toSet_ofRat q
  | add a b iha ihb => exact add_mem_toSet iha ihb
  | sub a b iha ihb => exact sub_mem_toSet iha ihb
  | mul a b iha ihb => exact mem_toSet_mul iha ihb
  | div a b iha ihb =>
    show a.denote xs / b.denote xs ∈ _
    rw [div_eq_mul_inv]; exact mem_toSet_mul iha (mem_inv ihb)
  | neg a iha => exact mem_neg iha
  | inv a iha => exact mem_inv iha
  | sqrt a iha => exact sqrtI_mem iha
  | abs a iha => exact mem_abs iha
  | pow a n iha => exact mem_pown iha n
  | exp a iha => exact exp_mem_toSet iha
  | log a iha => exact logI_mem iha
  | sin a iha => exact sin_mem_toSet iha
  | cos a iha => exact cos_mem_toSet iha
  | pi => exact pi_mem_toSet
  | atan a iha => exact atan_mem_toSet iha
  | atan2 a b iha ihb => exact atan2I_mem ihb iha

/-! ### Bisection -/

theorem split_mem {lo hi m : Nat} {y : ℝ} (hm : m < 2 ^ 64) (hn : isNaN m = false)
    (hy : y ∈ (toI ⟨lo, hi⟩).toSet) :
    y ∈ (toI ⟨lo, m⟩).toSet ∨ y ∈ (toI ⟨m, hi⟩).toSet := by
  obtain ⟨⟨hl, hl'⟩, ⟨hh, hh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hmn : (toF m).isNaN = false := by rw [isNaN_toF hm]; exact hn
  rcases le_total (y : EReal) (toF m).toE with h | h
  · exact Or.inl (mem_toSet_of_toE hl hmn hl' h)
  · exact Or.inr (mem_toSet_of_toE hmn hh h hh')

theorem forall2_set {xs : List ℝ} {env : List KI}
    (h : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) (i : Nat) {Y : KI}
    (hY : xs.getD i 0 ∈ (toI Y).toSet) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX _ ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using hY) (by assumption)
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using hY))

theorem getD_mem_toI {xs : List ℝ} {env : List KI}
    (h : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) (i : Nat) :
    xs.getD i 0 ∈ (toI (env.getD i zeroK)).toSet := by
  induction h generalizing i with
  | nil => simpa [toI_zeroK] using zero_mem_zeroI
  | cons hxX _ ih =>
    cases i with
    | zero => simpa using hxX
    | succ n => simpa using ih n

theorem forall2_map {xs : List ℝ} {env : List KI}
    (h : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) :
    List.Forall₂ (fun x X => x ∈ X.toSet) xs (env.map toI) := by
  induction h with
  | nil => simp
  | cons hxX _ ih => exact List.Forall₂.cons hxX ih

theorem checkK_sound (e : IExpr) (g : KI → Bool) (P : ℝ → Prop)
    (hg : ∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y) :
    ∀ (c : Cert) (env : List KI) (xs : List ℝ), (∀ X ∈ env, WF X) →
      List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env →
      checkK e g c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro env xs hwf hxs hc
    have := evalK_toI hwf e
    refine hg _ this.2 hc _ ?_
    rw [this.1]; exact eval_sound (forall2_map hxs) e
  | split i m l r ihl ihr =>
    intro env xs hwf hxs hc
    simp only [checkK, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hn, hm⟩, hcl⟩, hcr⟩ := hc
    have hm' : m < 2 ^ 64 := Nat.blt_eq ▸ hm
    have hwi := getD_wf hwf i
    have hx := getD_mem_toI hxs i
    generalize env.getD i zeroK = X at hx hwi hcl hcr
    rcases split_mem (lo := X.lo) (hi := X.hi) hm' hn hx with h1 | h1
    · exact ihl (env.set i ⟨X.lo, m⟩) xs (set_wf hwf i (Y := ⟨X.lo, m⟩) ⟨hwi.1, hm'⟩)
        (forall2_set hxs i (Y := ⟨X.lo, m⟩) h1) hcl
    · exact ihr (env.set i ⟨m, X.hi⟩) xs (set_wf hwf i (Y := ⟨m, X.hi⟩) ⟨hm', hwi.2⟩)
        (forall2_set hxs i (Y := ⟨m, X.hi⟩) h1) hcr

/-! ### Goal predicates -/

theorem toE_ofRatDown_le (c : ℚ) : (toF (KI.ofRat c).lo).toE ≤ ((c : ℝ) : EReal) ∧
    (toF (KI.ofRat c).lo).isNaN = false := by
  have h := loR_ofBits (ofRatDown_loR (c := c) (y := (c : ℝ)) le_rfl)
  rw [loR_iff_toE] at h
  show (toF (ofRatDown c).toNat).toE ≤ _ ∧ (toF (ofRatDown c).toNat).isNaN = false
  rw [toF_toNat]; exact ⟨h.2, h.1⟩

theorem le_toE_ofRatUp (c : ℚ) : ((c : ℝ) : EReal) ≤ (toF (KI.ofRat c).hi).toE ∧
    (toF (KI.ofRat c).hi).isNaN = false := by
  have h := hiR_ofBits (ofRatUp_hiR (c := c) (y := (c : ℝ)) le_rfl)
  rw [hiR_iff_toE] at h
  show _ ≤ (toF (ofRatUp c).toNat).toE ∧ (toF (ofRatUp c).toNat).isNaN = false
  rw [toF_toNat]; exact ⟨h.2, h.1⟩

theorem gLe_sound (c : ℚ) : ∀ F, WF F → gLe (KI.ofRat c).lo F = true →
    ∀ y ∈ (toI F).toSet, y ≤ (c : ℝ) := by
  intro F hF hg y hy
  have hc := toE_ofRatDown_le c
  have hcw : (KI.ofRat c).lo < 2 ^ 64 := (ofRat_toI c).2.1
  simp only [gLe, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨-, hh⟩, -⟩, hle⟩ := hg
  obtain ⟨-, ⟨-, hy2⟩⟩ := mem_toSet_iff_toE.1 hy
  have hhn : (toF F.hi).isNaN = false := by rw [isNaN_toF hF.2]; exact hh
  have h1 : toF F.hi ≤ toF (KI.ofRat c).lo := by
    have := le_toF hF.2 hcw; rw [hle] at this; exact of_decide_eq_true this
  rw [float_le_iff_toE hhn hc.2] at h1
  exact EReal.coe_le_coe_iff.1 (le_trans hy2 (le_trans h1 hc.1))

theorem gLt_sound (c : ℚ) : ∀ F, WF F → gLt (KI.ofRat c).lo F = true →
    ∀ y ∈ (toI F).toSet, y < (c : ℝ) := by
  intro F hF hg y hy
  have hc := toE_ofRatDown_le c
  have hcw : (KI.ofRat c).lo < 2 ^ 64 := (ofRat_toI c).2.1
  simp only [gLt, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨-, hh⟩, -⟩, hlt⟩ := hg
  obtain ⟨-, ⟨-, hy2⟩⟩ := mem_toSet_iff_toE.1 hy
  have hhn : (toF F.hi).isNaN = false := by rw [isNaN_toF hF.2]; exact hh
  have h1 : toF F.hi < toF (KI.ofRat c).lo := by
    have := lt_toF hF.2 hcw; rw [hlt] at this; exact of_decide_eq_true this
  rw [float_lt_iff_toE hhn hc.2] at h1
  exact EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt hy2 (lt_of_lt_of_le h1 hc.1))

theorem gGe_sound (c : ℚ) : ∀ F, WF F → gGe (KI.ofRat c).hi F = true →
    ∀ y ∈ (toI F).toSet, (c : ℝ) ≤ y := by
  intro F hF hg y hy
  have hc := le_toE_ofRatUp c
  have hcw : (KI.ofRat c).hi < 2 ^ 64 := (ofRat_toI c).2.2
  simp only [gGe, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨hl, -⟩, -⟩, hle⟩ := hg
  obtain ⟨⟨-, hy1⟩, -⟩ := mem_toSet_iff_toE.1 hy
  have hln : (toF F.lo).isNaN = false := by rw [isNaN_toF hF.1]; exact hl
  have h1 : toF (KI.ofRat c).hi ≤ toF F.lo := by
    have := le_toF hcw hF.1; rw [hle] at this; exact of_decide_eq_true this
  rw [float_le_iff_toE hc.2 hln] at h1
  exact EReal.coe_le_coe_iff.1 (le_trans hc.1 (le_trans h1 hy1))

theorem gGt_sound (c : ℚ) : ∀ F, WF F → gGt (KI.ofRat c).hi F = true →
    ∀ y ∈ (toI F).toSet, (c : ℝ) < y := by
  intro F hF hg y hy
  have hc := le_toE_ofRatUp c
  have hcw : (KI.ofRat c).hi < 2 ^ 64 := (ofRat_toI c).2.2
  simp only [gGt, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨hl, -⟩, -⟩, hlt⟩ := hg
  obtain ⟨⟨-, hy1⟩, -⟩ := mem_toSet_iff_toE.1 hy
  have hln : (toF F.lo).isNaN = false := by rw [isNaN_toF hF.1]; exact hl
  have h1 : toF (KI.ofRat c).hi < toF F.lo := by
    have := lt_toF hcw hF.1; rw [hlt] at this; exact of_decide_eq_true this
  rw [float_lt_iff_toE hc.2 hln] at h1
  exact EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt hc.1 (lt_of_lt_of_le h1 hy1))

/-! ### Entry points for the tactic -/

/-- Variables in their rational boxes. -/
def InBoxes : List ℝ → List (ℚ × ℚ) → Prop :=
  List.Forall₂ (fun x b => (b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ))

theorem boxes_mem {xs : List ℝ} {bs : List (ℚ × ℚ)} (h : InBoxes xs bs) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs (boxes bs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih =>
    refine List.Forall₂.cons ?_ ih
    rw [(ofRatInterval_toI _ _).1]; exact mem_toSet_ofRatInterval hx.1 hx.2

theorem prove_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkK e (gLe (KI.ofRat c).lo) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkK_sound e _ _ (gLe_sound c) cert _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem prove_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkK e (gLt (KI.ofRat c).lo) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkK_sound e _ _ (gLt_sound c) cert _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem prove_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkK e (gGe (KI.ofRat c).hi) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkK_sound e _ _ (gGe_sound c) cert _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem prove_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkK e (gGt (KI.ofRat c).hi) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkK_sound e _ _ (gGt_sound c) cert _ xs (boxes_wf bs) (boxes_mem hxs) h

end RealFP
