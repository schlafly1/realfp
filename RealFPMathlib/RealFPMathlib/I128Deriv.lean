/-
Soundness of the 128-bit derivative certificates (`Interval128.Dy.checkDQ`): monotonicity and
the mean-value (centred) form, reusing `RealFP.Dom` / `RealFP.hasDerivAt_denote`
(`IntervalDeriv.lean`) and the dyadic enclosures (`I128Dyadic.lean`).
-/
import RealFPMathlib.I128Dyadic
import RealFPMathlib.IntervalDeriv

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)

noncomputable section

namespace RealFP.I128Q

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-! ### Domain checks -/

omit [ExtTbl] [ExtSem] in
theorem pos_of_posQ {X : DI} (h : Interval128.Dy.posQ X = true) {x : ℝ} (hx : mem x X) : 0 < x := by
  unfold Interval128.Dy.posQ at h
  split at h
  · rename_i a ha
    exact lt_of_lt_of_le ((val_pos_iff a).2 (of_decide_eq_true h)) (hx.1 a ha)
  · simp at h

omit [ExtTbl] [ExtSem] in
theorem ne_of_nzQ {X : DI} (h : Interval128.Dy.nzQ X = true) {x : ℝ} (hx : mem x X) : x ≠ 0 := by
  unfold Interval128.Dy.nzQ at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact (pos_of_posQ h hx).ne'
  · split at h
    · rename_i b hb
      exact (lt_of_le_of_lt (hx.2 b hb) ((val_neg_iff b).2 (of_decide_eq_true h))).ne
    · simp at h

theorem domOKQ_sound {xs : List ℝ} {env : List DI} (hxs : List.Forall₂ mem xs env) :
    ∀ e : IExpr, Interval128.Dy.domOKQ env e = true → Dom xs e := by
  intro e
  induction e with
  | var j => intro _; trivial
  | rat q => intro _; trivial
  | add a b iha ihb =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | sub a b iha ihb =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | div a b iha ihb =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1.1, ihb h.1.2, ne_of_nzQ h.2 (evalQ_sound hxs b)⟩
  | neg a iha => intro h; exact iha h
  | inv a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, ne_of_nzQ h.2 (evalQ_sound hxs a)⟩
  | sqrt a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs a)⟩
  | abs a _ => intro h; simp [Interval128.Dy.domOKQ] at h
  | pow a n iha => intro h; exact iha h
  | exp a iha => intro h; exact iha h
  | log a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs a)⟩
  | sin a iha => intro h; exact iha h
  | cos a iha => intro h; exact iha h
  | pi => intro _; trivial
  | atan a iha => intro h; exact iha h
  | atan2 a b _ _ => intro h; simp [Interval128.Dy.domOKQ] at h
  | sinh a iha => intro h; exact iha h
  | cosh a iha => intro h; exact iha h
  | tanh a iha => intro h; exact iha h
  | log2 a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs a)⟩
  | log10 a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs a)⟩
  | tan a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, ne_of_nzQ h.2 (evalQ_sound hxs (.cos a))⟩
  | asin a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs (.sub (.rat 1) (.pow a 2)))⟩
  | acos a iha =>
    intro h; simp only [Interval128.Dy.domOKQ, Bool.and_eq_true] at h
    exact ⟨iha h.1, pos_of_posQ h.2 (evalQ_sound hxs (.sub (.rat 1) (.pow a 2)))⟩
  | ext k d a _ => intro h; simp [Interval128.Dy.domOKQ] at h

/-! ### Intervals -/

omit [ExtTbl] [ExtSem] in
theorem mem_meet {A B : DI} {x : ℝ} (ha : mem x A) (hb : mem x B) : mem x (DI.meet A B) := by
  constructor
  · intro l hl
    simp only [DI.meet] at hl
    split at hl
    · rename_i a b h1 h2
      simp only [Option.some.injEq] at hl; subst hl
      rcases val_max_cases a b with h | h <;> rw [h]
      · exact ha.1 a h1
      · exact hb.1 b h2
    · rename_i a h1 _; simp only [Option.some.injEq] at hl; subst hl; exact ha.1 _ h1
    · rename_i b h1; exact hb.1 _ hl
  · intro u hu
    simp only [DI.meet] at hu
    split at hu
    · rename_i a b h1 h2
      simp only [Option.some.injEq] at hu; subst hu
      rcases val_min_cases a b with h | h <;> rw [h]
      · exact ha.2 a h1
      · exact hb.2 b h2
    · rename_i a h1 _; simp only [Option.some.injEq] at hu; subst hu; exact ha.2 _ h1
    · rename_i b h1; exact hb.2 _ hu

omit [ExtTbl] [ExtSem] in
theorem seg_memQ {X : DI} {x r t : ℝ} (hx : mem x X) (hr : mem r X) (ht : t ∈ Set.uIcc x r) :
    mem t X := by
  rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun l hl => le_trans (hx.1 l hl) h1, fun u hu => le_trans h2 (hr.2 u hu)⟩
  · exact ⟨fun l hl => le_trans (hr.1 l hl) h1, fun u hu => le_trans h2 (hx.2 u hu)⟩

omit [ExtTbl] [ExtSem] in
theorem forall2_setxQ {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : Nat)
    {t : ℝ} (ht : mem t (env.getD i DI.zero)) : List.Forall₂ mem (xs.set i t) env := by
  induction h generalizing i with
  | nil => simp
  | cons hxX hr ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using ht) hr
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using ht))

omit [ExtTbl] [ExtSem] in
theorem forall2_set2Q {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : Nat)
    {t : ℝ} {Y : DI} (ht : mem t Y) : List.Forall₂ mem (xs.set i t) (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX hr ih =>
    cases i with
    | zero => exact List.Forall₂.cons ht hr
    | succ n => exact List.Forall₂.cons hxX (ih n)

theorem hasDerivAt_boxQ {xs : List ℝ} {env : List DI} (hxs : List.Forall₂ mem xs env) {i : Nat}
    (hi : i < xs.length) {e : IExpr} (hd : Interval128.Dy.domOKQ env e = true) {t : ℝ}
    (ht : mem t (env.getD i DI.zero)) :
    HasDerivAt (fun s => e.denote (xs.set i s)) ((e.deriv i).denote (xs.set i t)) t := by
  have hz := forall2_setxQ hxs i ht
  have hi' : i < (xs.set i t).length := by simpa using hi
  have := hasDerivAt_denote hi' e (domOKQ_sound hz e hd)
  simp only [List.set_set, getD_set_same hi] at this
  rw [denote_deriv]; exact this

/-! ### Soundness of `checkDQ` -/

theorem checkDQ_sound : ∀ (c : Interval128.Dy.DCert) (e : IExpr) (g : DI → Bool) (upper : Bool)
    (P : ℝ → Prop), (∀ F, g F = true → ∀ y, mem y F → P y) →
    (∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z) →
    ∀ (env : List DI) (xs : List ℝ), List.Forall₂ mem xs env →
      Interval128.Dy.checkDQ e g upper c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro e g upper P hg _ env xs hxs hc
    exact hg _ hc _ (evalQ_sound hxs e)
  | split i q l r ihl ihr =>
    intro e g upper P hg hP env xs hxs hc
    simp only [Interval128.Dy.checkDQ, Bool.and_eq_true] at hc
    rcases split_mem q (getD_mem hxs i) with h1 | h1
    · exact ihl e g upper P hg hP _ xs (forall2_set hxs i h1) hc.1
    · exact ihr e g upper P hg hP _ xs (forall2_set hxs i h1) hc.2
  | mono i inc dc c ihdc ihc =>
    intro e g upper P hg hP env xs hxs hc
    simp only [Interval128.Dy.checkDQ, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hil, hdom⟩, hsg⟩, hcc⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    have hsign : ∀ zs, List.Forall₂ mem zs env →
        (if inc then 0 ≤ (e.deriv i).denote zs else (e.deriv i).denote zs ≤ 0) := by
      intro zs hzs
      cases inc
      · simp only [Bool.cond_false] at hsg
        have := ihdc (e.deriv i) _ true (fun y => y ≤ ((0 : ℚ) : ℝ)) (gLe_sound 0)
          (fun y z h hy => by simp only [↓reduceIte] at h; linarith) env zs hzs hsg
        simpa using this
      · simp only [Bool.cond_true] at hsg
        have := ihdc (e.deriv i) _ false (fun y => ((0 : ℚ) : ℝ) ≤ y) (gGe_sound 0)
          (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith)
          env zs hzs hsg
        simpa using this
    have hx := getD_mem hxs i
    have hself := set_getD_self hi
    have key : ∀ p : Dy, mem (val p) (env.getD i DI.zero) →
        (if (inc == upper) then xs.getD i 0 ≤ val p else val p ≤ xs.getD i 0) →
        Interval128.Dy.checkDQ e g upper c (env.set i (DI.pt p)) = true → P (e.denote xs) := by
      intro p hrX hxr hcp
      have hPr := ihc e g upper P hg hP (env.set i (DI.pt p)) (xs.set i (val p))
        (forall2_set2Q hxs i (mem_pt p)) hcp
      obtain ⟨d, hd, hmv⟩ := mvt_uIcc (S := fun d => if inc then 0 ≤ d else d ≤ 0)
        (φ := fun s => e.denote (xs.set i s)) (a := xs.getD i 0) (b := val p) (fun t ht => by
          have htX := seg_memQ hx hrX ht
          exact ⟨_, hsign _ (forall2_setxQ hxs i htX), hasDerivAt_boxQ hxs hi hdom htX⟩)
      have hmono := mono_step upper inc hd hmv hxr
      simp only [hself] at hmono
      exact hP _ _ hmono hPr
    cases hb : (inc == upper)
    · simp only [hb, Bool.cond_false] at hcc
      split at hcc
      · rename_i p hp
        refine key p ⟨fun l hl => ?_, fun u hu => ?_⟩ ?_ hcc
        · rw [hp] at hl; cases hl; exact le_rfl
        · exact le_trans (hx.1 p hp) (hx.2 u hu)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact hx.1 p hp
      · simp at hcc
    · simp only [hb, Bool.cond_true] at hcc
      split at hcc
      · rename_i p hp
        refine key p ⟨fun l hl => ?_, fun u hu => ?_⟩ ?_ hcc
        · exact le_trans (hx.1 l hl) (hx.2 p hp)
        · rw [hp] at hu; cases hu; exact le_rfl
        · simp only [hb, ↓reduceIte]; exact hx.2 p hp
      · simp at hcc
  | center i m =>
    intro e g upper P hg _ env xs hxs hc
    simp only [Interval128.Dy.checkDQ, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hil, hdom⟩, hin⟩, hgc⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    have hx := getD_mem hxs i
    have hself := set_getD_self hi
    have hrX : mem (val m) (env.getD i DI.zero) := by
      unfold Interval128.Dy.inside at hin
      split at hin
      · rename_i a b ha hb
        have h' := of_decide_eq_true hin
        have h1 := (Rat.cast_le (K := ℝ)).2 h'.1
        have h2 := (Rat.cast_le (K := ℝ)).2 h'.2
        rw [toRat_val, toRat_val] at h1 h2
        exact ⟨fun l hl => by rw [ha] at hl; cases hl; exact h1,
          fun u hu => by rw [hb] at hu; cases hu; exact h2⟩
      · simp at hin
    obtain ⟨d, hd, hmv⟩ := mvt_uIcc (S := fun d => mem d (Interval128.Dy.evalQ env (e.deriv i)))
      (φ := fun s => e.denote (xs.set i s)) (a := val m) (b := xs.getD i 0) (fun t ht => by
        have htX := seg_memQ hrX hx ht
        exact ⟨_, evalQ_sound (forall2_setxQ hxs i htX) (e.deriv i), hasDerivAt_boxQ hxs hi hdom htX⟩)
    simp only [hself] at hmv
    have hfr := evalQ_sound (forall2_set2Q hxs i (mem_pt m)) e
    have hmul := mem_mul hd (mem_sub hx (mem_pt m))
    have hadd := mem_add hfr hmul
    have heq : e.denote xs = e.denote (xs.set i (val m)) + d * (xs.getD i 0 - val m) := by linarith
    rw [← heq] at hadd
    exact hg _ hgc _ (mem_meet (evalQ_sound hxs e) hadd)

/-! ### Entry points for the tactic -/

theorem proveD_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.DCert)
    (h : Interval128.Dy.checkDQ e (Interval128.Dy.gLe c) true cert (Interval128.Dy.boxes bs) = true)
    (xs : List ℝ) (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkDQ_sound cert e _ true (fun y => y ≤ (c : ℝ)) (gLe_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_mem hxs) h

theorem proveD_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.DCert)
    (h : Interval128.Dy.checkDQ e (Interval128.Dy.gLt c) true cert (Interval128.Dy.boxes bs) = true)
    (xs : List ℝ) (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkDQ_sound cert e _ true (fun y => y < (c : ℝ)) (gLt_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_mem hxs) h

theorem proveD_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.DCert)
    (h : Interval128.Dy.checkDQ e (Interval128.Dy.gGe c) false cert (Interval128.Dy.boxes bs) = true)
    (xs : List ℝ) (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkDQ_sound cert e _ false (fun y => (c : ℝ) ≤ y) (gGe_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_mem hxs) h

theorem proveD_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.DCert)
    (h : Interval128.Dy.checkDQ e (Interval128.Dy.gGt c) false cert (Interval128.Dy.boxes bs) = true)
    (xs : List ℝ) (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkDQ_sound cert e _ false (fun y => (c : ℝ) < y) (gGt_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_mem hxs) h

omit [ExtSem] in
theorem checkDQ_split_of (e : IExpr) (g : DI → Bool) (upper : Bool) (i : ℕ) (q : Dy)
    (l r : Interval128.Dy.DCert) (env : List DI)
    (hl : Interval128.Dy.checkDQ e g upper l
      (env.set i (Interval128.Dy.leftAt (env.getD i DI.zero) q)) = true)
    (hr : Interval128.Dy.checkDQ e g upper r
      (env.set i (Interval128.Dy.rightAt (env.getD i DI.zero) q)) = true) :
    Interval128.Dy.checkDQ e g upper (.split i q l r) env = true := by
  simp only [Interval128.Dy.checkDQ, hl, hr, Bool.and_self]

end RealFP.I128Q
