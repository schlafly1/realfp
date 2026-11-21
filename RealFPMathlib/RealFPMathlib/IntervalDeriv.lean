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


/-! ### Enclosures -/

theorem memK {xs : List ℝ} {env : List KI} (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) (e : IExpr) :
    e.denote xs ∈ (toI (evalK env e)).toSet ∧ WF (evalK env e) := by
  have h := evalK_toI hw e
  exact ⟨by rw [h.1]; exact eval_sound (forall2_map hxs) e, h.2⟩

theorem toE_toF_zero : (toF 0).toE = ((0 : ℝ) : EReal) := by rw [toF_zero]; simp

theorem isNaN_toF_zero : (toF 0).isNaN = false := by rw [toF_zero]; decide +kernel

theorem pos_of_posK {X : KI} (hX : WF X) (h : posK X = true) {x : ℝ}
    (hx : x ∈ (toI X).toSet) : 0 < x := by
  simp only [posK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hl, -⟩, hlt⟩ := h
  obtain ⟨⟨-, hx1⟩, -⟩ := mem_toSet_iff_toE.1 hx
  have hln : (toF X.lo).isNaN = false := by rw [isNaN_toF hX.1]; exact hl
  have h1 : toF 0 < toF X.lo := by
    have := lt_toF zero_lt hX.1; rw [hlt] at this; exact of_decide_eq_true this
  rw [float_lt_iff_toE isNaN_toF_zero hln, toE_toF_zero] at h1
  exact EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le h1 hx1)

theorem ne_of_nzK {X : KI} (hX : WF X) (h : nzK X = true) {x : ℝ}
    (hx : x ∈ (toI X).toSet) : x ≠ 0 := by
  simp only [nzK, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨hl, hh⟩, hlt | hlt⟩ := h
  · exact (pos_of_posK hX (by simp [posK, hl, hh, hlt]) hx).ne'
  · obtain ⟨-, ⟨-, hx2⟩⟩ := mem_toSet_iff_toE.1 hx
    have hhn : (toF X.hi).isNaN = false := by rw [isNaN_toF hX.2]; exact hh
    have h1 : toF X.hi < toF 0 := by
      have := lt_toF hX.2 zero_lt; rw [hlt] at this; exact of_decide_eq_true this
    rw [float_lt_iff_toE hhn isNaN_toF_zero, toE_toF_zero] at h1
    exact (EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt hx2 h1)).ne

theorem domOK_sound {xs : List ℝ} {env : List KI} (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) :
    ∀ e : IExpr, domOK env e = true → Dom xs e := by
  intro e
  induction e with
  | var j => intro _; trivial
  | rat q => intro _; trivial
  | add a b iha ihb =>
    intro h; simp only [domOK, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | sub a b iha ihb =>
    intro h; simp only [domOK, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    intro h; simp only [domOK, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | div a b iha ihb =>
    intro h; simp only [domOK, Bool.and_eq_true] at h
    have m := memK hw hxs b
    exact ⟨iha h.1.1, ihb h.1.2, ne_of_nzK m.2 h.2 m.1⟩
  | neg a iha => intro h; exact iha h
  | inv a iha =>
    intro h; simp only [domOK, Bool.and_eq_true] at h
    have m := memK hw hxs a
    exact ⟨iha h.1, ne_of_nzK m.2 h.2 m.1⟩
  | sqrt a iha =>
    intro h; simp only [domOK, Bool.and_eq_true] at h
    have m := memK hw hxs a
    exact ⟨iha h.1, pos_of_posK m.2 h.2 m.1⟩
  | abs a _ => intro h; simp [domOK] at h
  | pow a n iha => intro h; exact iha h
  | exp a iha => intro h; exact iha h
  | log a iha =>
    intro h; simp only [domOK, Bool.and_eq_true] at h
    have m := memK hw hxs a
    exact ⟨iha h.1, pos_of_posK m.2 h.2 m.1⟩
  | sin a iha => intro h; exact iha h
  | cos a iha => intro h; exact iha h

/-! ### Points, segments, intersection -/

theorem finK_point {p : Nat} (h : finK p = true) :
    ∃ r : ℝ, (toF p).toE = r ∧ r ∈ (toI ⟨p, p⟩).toSet ∧ WF ⟨p, p⟩ := by
  simp only [finK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, hb⟩ := h
  have hp : p < 2 ^ 64 := Nat.blt_eq ▸ hb
  have hfn : (toF p).isNaN = false := by rw [isNaN_toF hp]; exact hn
  have hfi : (toF p).isInf = false := by rw [isInf_toF' hp]; exact hi
  have ht : (toF p).toE ≠ ⊤ := fun h' => by
    have := isInf_iff_toE.2 ⟨Or.inl h', hfn⟩; rw [hfi] at this; exact Bool.false_ne_true this
  have hbot : (toF p).toE ≠ ⊥ := fun h' => by
    have := isInf_iff_toE.2 ⟨Or.inr h', hfn⟩; rw [hfi] at this; exact Bool.false_ne_true this
  obtain ⟨q, -, hq⟩ := exists_rat_of_toE hfn hbot ht
  exact ⟨q, hq, mem_toSet_of_toE hfn hfn (le_of_eq hq) (ge_of_eq hq), hp, hp⟩

theorem seg_mem {I : Interval64} {x r t : ℝ} (hx : x ∈ I.toSet) (hr : r ∈ I.toSet)
    (ht : t ∈ Set.uIcc x r) : t ∈ I.toSet := by
  obtain ⟨⟨hl, hx1⟩, ⟨hh, hx2⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨-, hr1⟩, ⟨-, hr2⟩⟩ := mem_toSet_iff_toE.1 hr
  rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_toSet_of_toE hl hh (le_trans hx1 (EReal.coe_le_coe_iff.2 h1))
      (le_trans (EReal.coe_le_coe_iff.2 h2) hr2)
  · exact mem_toSet_of_toE hl hh (le_trans hr1 (EReal.coe_le_coe_iff.2 h1))
      (le_trans (EReal.coe_le_coe_iff.2 h2) hx2)

theorem meet_mem {A B : KI} (hA : WF A) (hB : WF B) {y : ℝ} (hya : y ∈ (toI A).toSet)
    (hyb : y ∈ (toI B).toSet) : y ∈ (toI (KI.meet A B)).toSet ∧ WF (KI.meet A B) := by
  obtain ⟨⟨hal, ha1⟩, ⟨hah, ha2⟩⟩ := mem_toSet_iff_toE.1 hya
  obtain ⟨⟨hbl, hb1⟩, ⟨hbh, hb2⟩⟩ := mem_toSet_iff_toE.1 hyb
  simp only [toI] at hal ha1 hah ha2 hbl hb1 hbh hb2
  have e1 : toF (KI.fmax A.lo B.lo) = fmax (toF A.lo) (toF B.lo) := (fmax_toF hA.1 hB.1).symm
  have e2 : toF (KI.fmin A.hi B.hi) = fmin (toF A.hi) (toF B.hi) := (fmin_toF hA.2 hB.2).symm
  refine ⟨?_, fmax_lt hA.1 hB.1, fmin_lt hA.2 hB.2⟩
  show y ∈ (Interval64.mk (toF (KI.fmax A.lo B.lo)) (toF (KI.fmin A.hi B.hi))).toSet
  rw [e1, e2]
  refine mem_toSet_of_toE (fmax_isNaN hal hbl) (fmin_isNaN hah hbh) ?_ ?_
  · show (fmax (toF A.lo) (toF B.lo)).toE ≤ _
    rw [toE_fmax hal hbl]; exact max_le ha1 hb1
  · show _ ≤ (fmin (toF A.hi) (toF B.hi)).toE
    rw [toE_fmin hah hbh]; exact le_min ha2 hb2

/-! ### Mean value theorem on a segment -/

theorem mvt_lt {φ : ℝ → ℝ} {S : ℝ → Prop} {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Set.uIcc a b, ∃ d, S d ∧ HasDerivAt φ d t) :
    ∃ d, S d ∧ φ b - φ a = d * (b - a) := by
  have hI : ∀ t ∈ Set.Icc a b, t ∈ Set.uIcc a b := fun t ht => by
    rw [Set.uIcc_of_le hab.le]; exact ht
  have hd : ∀ t ∈ Set.Icc a b, HasDerivAt φ (deriv φ t) t := fun t ht => by
    obtain ⟨d, -, hd⟩ := h t (hI t ht); rw [hd.deriv]; exact hd
  have hc : ContinuousOn φ (Set.Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope φ (deriv φ) hab hc
    (fun t ht => hd t (Set.Ioo_subset_Icc_self ht))
  obtain ⟨d, hS, hdc⟩ := h c (hI c (Set.Ioo_subset_Icc_self hc1))
  refine ⟨d, hS, ?_⟩
  rw [hdc.deriv] at hc2
  rw [hc2]; field_simp [sub_ne_zero.2 hab.ne']

theorem mvt_uIcc {φ : ℝ → ℝ} {S : ℝ → Prop} {a b : ℝ}
    (h : ∀ t ∈ Set.uIcc a b, ∃ d, S d ∧ HasDerivAt φ d t) :
    ∃ d, S d ∧ φ b - φ a = d * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact mvt_lt hab h
  · obtain ⟨d, hS, -⟩ := h a (by simp)
    exact ⟨d, hS, by ring⟩
  · obtain ⟨d, hS, hd⟩ := mvt_lt hab (fun t ht => h t (Set.uIcc_comm a b ▸ ht))
    exact ⟨d, hS, by linarith⟩

/-! ### Lists of boxes -/

theorem forall2_setx {xs : List ℝ} {env : List KI}
    (h : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) (i : Nat) {t : ℝ}
    (ht : t ∈ (toI (env.getD i zeroK)).toSet) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) (xs.set i t) env := by
  induction h generalizing i with
  | nil => simp
  | cons hxX hr ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using ht) hr
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using ht))

theorem forall2_set2 {xs : List ℝ} {env : List KI}
    (h : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) (i : Nat) {t : ℝ} {Y : KI}
    (ht : t ∈ (toI Y).toSet) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) (xs.set i t) (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX hr ih =>
    cases i with
    | zero => exact List.Forall₂.cons ht hr
    | succ n => exact List.Forall₂.cons hxX (ih n)

theorem getD_set_same {xs : List ℝ} {i : Nat} (hi : i < xs.length) (t : ℝ) :
    (xs.set i t).getD i 0 = t := by rw [getD_set_eq hi]; simp

/-- Derivative of `t ↦ e(xs[i := t])` at every point of the box's `i`-th interval. -/
theorem hasDerivAt_box {xs : List ℝ} {env : List KI} (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) {i : Nat} (hi : i < xs.length)
    {e : IExpr} (hd : domOK env e = true) {t : ℝ} (ht : t ∈ (toI (env.getD i zeroK)).toSet) :
    HasDerivAt (fun s => e.denote (xs.set i s)) ((e.diff i).denote (xs.set i t)) t := by
  have hz := forall2_setx hxs i ht
  have hi' : i < (xs.set i t).length := by simpa using hi
  have := hasDerivAt_denote hi' e (domOK_sound hw hz e hd)
  simp only [List.set_set, getD_set_same hi] at this
  exact this

theorem mono_step (upper inc : Bool) {φx φr d x r : ℝ} (hd : if inc then 0 ≤ d else d ≤ 0)
    (hmv : φr - φx = d * (r - x)) (hxr : if (inc == upper) then x ≤ r else r ≤ x) :
    if upper then φx ≤ φr else φr ≤ φx := by
  cases inc <;> cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
    Bool.true_beq, Bool.false_beq, Bool.not_true] at hd hxr ⊢ <;> nlinarith

/-! ### Soundness of `checkD` -/

theorem checkD_sound : ∀ (c : DCert) (e : IExpr) (g : KI → Bool) (upper : Bool) (P : ℝ → Prop),
    (∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y) →
    (∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z) →
    ∀ (env : List KI) (xs : List ℝ), (∀ X ∈ env, WF X) →
      List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env →
      checkD e g upper c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro e g upper P hg _ env xs hw hxs hc
    have m := memK hw hxs e
    exact hg _ m.2 hc _ m.1
  | split i m l r ihl ihr =>
    intro e g upper P hg hP env xs hw hxs hc
    simp only [checkD, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hn, hm⟩, hcl⟩, hcr⟩ := hc
    have hm' : m < 2 ^ 64 := Nat.blt_eq ▸ hm
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    generalize env.getD i zeroK = X at hx hwi hcl hcr
    rcases split_mem (lo := X.lo) (hi := X.hi) hm' hn hx with h1 | h1
    · exact ihl e g upper P hg hP (env.set i ⟨X.lo, m⟩) xs
        (set_wf hw i (Y := ⟨X.lo, m⟩) ⟨hwi.1, hm'⟩) (forall2_set hxs i (Y := ⟨X.lo, m⟩) h1) hcl
    · exact ihr e g upper P hg hP (env.set i ⟨m, X.hi⟩) xs
        (set_wf hw i (Y := ⟨m, X.hi⟩) ⟨hm', hwi.2⟩) (forall2_set hxs i (Y := ⟨m, X.hi⟩) h1) hcr
  | mono i inc dc c ihdc ihc =>
    intro e g upper P hg hP env xs hw hxs hc
    simp only [checkD, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hil, hdom⟩, hsg⟩, hfin⟩, hcc⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    -- sign of the derivative on the box
    have hsign : ∀ zs, List.Forall₂ (fun x X => x ∈ (toI X).toSet) zs env →
        (if inc then 0 ≤ (e.diff i).denote zs else (e.diff i).denote zs ≤ 0) := by
      intro zs hzs
      cases inc
      · simp only [Bool.cond_false] at hsg
        have := ihdc (e.diff i) _ true (fun y => y ≤ ((0 : ℚ) : ℝ)) (gLe_sound 0)
          (fun y z h hy => by simp only [↓reduceIte] at h; linarith) env zs hw hzs hsg
        simpa using this
      · simp only [Bool.cond_true] at hsg
        have := ihdc (e.diff i) _ false (fun y => ((0 : ℚ) : ℝ) ≤ y) (gGe_sound 0)
          (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith)
          env zs hw hzs hsg
        simpa using this
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    have hself := set_getD_self hi
    generalize hX : env.getD i zeroK = X at hx hwi hcc hfin
    -- endpoint
    have key : ∀ p : Nat, finK p = true → (∀ r : ℝ, (toF p).toE = r → r ∈ (toI X).toSet ∧
          (if (inc == upper) then xs.getD i 0 ≤ r else r ≤ xs.getD i 0)) →
        checkD e g upper c (env.set i ⟨p, p⟩) = true → P (e.denote xs) := by
      intro p hp hr hcp
      obtain ⟨r, hre, hrm, hwp⟩ := finK_point hp
      obtain ⟨hrX, hxr⟩ := hr r hre
      have hPr := ihc e g upper P hg hP (env.set i ⟨p, p⟩) (xs.set i r) (set_wf hw i hwp)
        (forall2_set2 hxs i hrm) hcp
      obtain ⟨d, hd, hmv⟩ := mvt_uIcc (S := fun d => if inc then 0 ≤ d else d ≤ 0)
        (φ := fun s => e.denote (xs.set i s)) (a := xs.getD i 0) (b := r) (fun t ht => by
          have htX := seg_mem hx hrX ht
          rw [← hX] at htX
          exact ⟨_, hsign _ (forall2_setx hxs i htX), hasDerivAt_box hw hxs hi hdom htX⟩)
      have hmono := mono_step upper inc hd hmv hxr
      simp only [hself] at hmono
      exact hP _ _ hmono hPr
    cases hb : (inc == upper)
    · simp only [hb, Bool.cond_false] at hfin hcc
      refine key X.lo hfin (fun r hr => ⟨?_, ?_⟩) hcc
      · obtain ⟨⟨hl, -⟩, ⟨hh, hx2⟩⟩ := mem_toSet_iff_toE.1 hx
        obtain ⟨⟨-, hx1⟩, -⟩ := mem_toSet_iff_toE.1 hx
        exact mem_toSet_of_toE hl hh (le_of_eq hr) (le_trans (hr ▸ hx1) hx2)
      · obtain ⟨⟨-, hx1⟩, -⟩ := mem_toSet_iff_toE.1 hx
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact EReal.coe_le_coe_iff.1 (hr ▸ hx1)
    · simp only [hb, Bool.cond_true] at hfin hcc
      refine key X.hi hfin (fun r hr => ⟨?_, ?_⟩) hcc
      · obtain ⟨⟨hl, hx1⟩, ⟨hh, hx2⟩⟩ := mem_toSet_iff_toE.1 hx
        exact mem_toSet_of_toE hl hh (le_trans hx1 (hr ▸ hx2)) (ge_of_eq hr)
      · obtain ⟨-, ⟨-, hx2⟩⟩ := mem_toSet_iff_toE.1 hx
        simp only [hb, ↓reduceIte]
        exact EReal.coe_le_coe_iff.1 (hr ▸ hx2)
  | center i m =>
    intro e g upper P hg _ env xs hw hxs hc
    simp only [checkD, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hil, hdom⟩, hfin⟩, hln⟩, hhn⟩, hlm⟩, hmh⟩, hgc⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    have hself := set_getD_self hi
    obtain ⟨r, hre, hrm, hwp⟩ := finK_point hfin
    have hmw : m < 2 ^ 64 := hwp.1
    -- r lies in the box
    have hrX : r ∈ (toI (env.getD i zeroK)).toSet := by
      have hl' : (toF (env.getD i zeroK).lo).isNaN = false := by rw [isNaN_toF hwi.1]; exact hln
      have hh' : (toF (env.getD i zeroK).hi).isNaN = false := by rw [isNaN_toF hwi.2]; exact hhn
      have hmn : (toF m).isNaN = false := (mem_toSet_iff_toE.1 hrm).1.1
      have h1 : toF (env.getD i zeroK).lo ≤ toF m := by
        have := le_toF hwi.1 hmw; rw [hlm] at this; exact of_decide_eq_true this
      have h2 : toF m ≤ toF (env.getD i zeroK).hi := by
        have := le_toF hmw hwi.2; rw [hmh] at this; exact of_decide_eq_true this
      rw [float_le_iff_toE hl' hmn, hre] at h1
      rw [float_le_iff_toE hmn hh', hre] at h2
      exact mem_toSet_of_toE hl' hh' h1 h2
    obtain ⟨d, hd, hmv⟩ := mvt_uIcc (S := fun d => d ∈ (toI (evalK env (e.diff i))).toSet)
      (φ := fun s => e.denote (xs.set i s)) (a := r) (b := xs.getD i 0) (fun t ht => by
        have htX := seg_mem hrX hx ht
        exact ⟨_, (memK hw (forall2_setx hxs i htX) (e.diff i)).1, hasDerivAt_box hw hxs hi hdom htX⟩)
    simp only [hself] at hmv
    -- the pieces
    have hfr := memK (set_wf hw i hwp) (forall2_set2 hxs i hrm) e
    have hdm := memK hw hxs (e.diff i)
    have hsub : xs.getD i 0 - r ∈ (toI (KI.sub (env.getD i zeroK) ⟨m, m⟩)).toSet := by
      rw [sub_toI hwi hwp]; exact sub_mem_toSet hx hrm
    have hmul := mem_toSet_mul hd hsub
    rw [← mul_toI hdm.2 (sub_wf hwi hwp)] at hmul
    have hadd := add_mem_toSet hfr.1 hmul
    rw [← add_toI hfr.2 (mul_wf hdm.2 (sub_wf hwi hwp))] at hadd
    have heq : e.denote xs = e.denote (xs.set i r) + d * (xs.getD i 0 - r) := by linarith
    rw [← heq] at hadd
    have hn := memK hw hxs e
    have hmt := meet_mem hn.2 (add_wf hfr.2 (mul_wf hdm.2 (sub_wf hwi hwp))) hn.1 hadd
    exact hg _ hmt.2 hgc _ hmt.1

end RealFP
