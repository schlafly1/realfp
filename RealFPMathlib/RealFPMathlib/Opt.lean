/-
Multivariate centred-form certificates for tight global bounds (branch-and-bound backend of
`interval`, `realfp` and the optimisation forms).

* `ECert` describes a *nested* centred form: centre variable `i` at the float `m`, then
  enclose the remaining function (with `xᵢ := m`) by the next centring, and so on:
  `f(X) ⊆ f(X[i:=m]) + ∂ᵢf(X)·(Xᵢ - m)`. `encK` computes this enclosure; invalid steps fall back to the natural enclosure, so `encK` is always sound.
* `MCert` is a bisection tree whose leaves are nested centred forms (`enc`), derivative
  certificates of `interval` (`d`, monotonicity etc.), or monotonicity steps continuing with an
  `MCert` on a face (`mono`).

Soundness: `RealFP.encK_mem`, `RealFP.checkM_sound`, entry points `RealFP.proveM_le/lt/ge/gt`.
-/
import RealFPMathlib.IntervalDeriv

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits

namespace Interval64.KF

variable [ExtTbl]

/-- Nested centred form: `nat` is the natural enclosure; `cen i m k` centres variable `i` at
the float with bits `m` and encloses `e` at `xᵢ = m` by `k`. -/
inductive ECert where
  | nat
  | cen (i : Nat) (m : Nat) (k : ECert)
  deriving Repr, Inhabited

/-- Conditions for a centring step in variable `i` at `m`. -/
def cenOK (env : List KI) (e : IExpr) (i m : Nat) : Bool :=
  Nat.blt i env.length && domOK env e && finK m &&
    !isNaN (env.getD i zeroK).lo && !isNaN (env.getD i zeroK).hi &&
    le (env.getD i zeroK).lo m && le m (env.getD i zeroK).hi

/-- Enclosure of `e` on `env` by the nested centred form `k`. -/
def encK (e : IExpr) : ECert → List KI → KI
  | .nat, env => evalK env e
  | .cen i m k, env =>
    bif cenOK env e i m then
      KI.add (encK e k (env.set i ⟨m, m⟩))
        (KI.mul (evalK env (e.deriv i)) (KI.sub (env.getD i zeroK) ⟨m, m⟩))
    else evalK env e

/-- Bisection tree with centred-form, derivative-certificate and monotonicity leaves. -/
inductive MCert where
  | enc (k : ECert)
  | d (c : DCert)
  | split (i : Nat) (m : Nat) (l r : MCert)
  | mono (i : Nat) (inc : Bool) (dc : DCert) (c : MCert)
  deriving Repr, Inhabited

def checkM (e : IExpr) (g : KI → Bool) (upper : Bool) : MCert → List KI → Bool
  | .enc k, env => g (encK e k env)
  | .d c, env => checkD e g upper c env
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkM e g upper l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkM e g upper r (env.set i ⟨m, (env.getD i zeroK).hi⟩)
  | .mono i inc dc c, env =>
    Nat.blt i env.length && domOK env e &&
      (bif inc then checkD (e.deriv i) (gGe zeroHi) false dc env
       else checkD (e.deriv i) (gLe zeroLo) true dc env) &&
      finK (bif inc == upper then (env.getD i zeroK).hi else (env.getD i zeroK).lo) &&
      checkM e g upper c
        (env.set i (bif inc == upper then ⟨(env.getD i zeroK).hi, (env.getD i zeroK).hi⟩
          else ⟨(env.getD i zeroK).lo, (env.getD i zeroK).lo⟩))

end Interval64.KF

noncomputable section

namespace RealFP

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-- The nested centred form encloses `e`. -/
theorem encK_mem (e : IExpr) : ∀ (k : ECert) (env : List KI) (xs : List ℝ),
    (∀ X ∈ env, WF X) → List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env →
    e.denote xs ∈ (toI (encK e k env)).toSet ∧ WF (encK e k env) := by
  intro k
  induction k with
  | nat => intro env xs hw hxs; exact memK hw hxs e
  | cen i m k ih =>
    intro env xs hw hxs
    cases hc : cenOK env e i m
    · simp only [encK, hc, Bool.cond_false]; exact memK hw hxs e
    simp only [encK, hc, Bool.cond_true]
    simp only [cenOK, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨hil, hdom⟩, hfin⟩, hln⟩, hhn⟩, hlm⟩, hmh⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    have hself := set_getD_self hi
    obtain ⟨r, hre, hrm, hwp⟩ := finK_point hfin
    have hmw : m < 2 ^ 64 := hwp.1
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
    obtain ⟨d, hd, hmv⟩ := mvt_uIcc (S := fun d => d ∈ (toI (evalK env (e.deriv i))).toSet)
      (φ := fun s => e.denote (xs.set i s)) (a := r) (b := xs.getD i 0) (fun t ht => by
        have htX := seg_mem hrX hx ht
        exact ⟨_, (memK hw (forall2_setx hxs i htX) (e.deriv i)).1,
          hasDerivAt_box hw hxs hi hdom htX⟩)
    simp only [hself] at hmv
    have hfr := ih (env.set i ⟨m, m⟩) (xs.set i r) (set_wf hw i hwp) (forall2_set2 hxs i hrm)
    have hdm := memK hw hxs (e.deriv i)
    have hsub : xs.getD i 0 - r ∈ (toI (KI.sub (env.getD i zeroK) ⟨m, m⟩)).toSet := by
      rw [sub_toI hwi hwp]; exact sub_mem_toSet hx hrm
    have hmul := mem_toSet_mul hd hsub
    rw [← mul_toI hdm.2 (sub_wf hwi hwp)] at hmul
    have hadd := add_mem_toSet hfr.1 hmul
    rw [← add_toI hfr.2 (mul_wf hdm.2 (sub_wf hwi hwp))] at hadd
    have heq : e.denote xs = e.denote (xs.set i r) + d * (xs.getD i 0 - r) := by linarith
    rw [← heq] at hadd
    exact ⟨hadd, add_wf hfr.2 (mul_wf hdm.2 (sub_wf hwi hwp))⟩

theorem checkM_sound : ∀ (c : MCert) (e : IExpr) (g : KI → Bool) (upper : Bool) (P : ℝ → Prop),
    (∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y) →
    (∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z) →
    ∀ (env : List KI) (xs : List ℝ), (∀ X ∈ env, WF X) →
      List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env →
      checkM e g upper c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | enc k =>
    intro e g upper P hg _ env xs hw hxs hc
    have m := encK_mem e k env xs hw hxs
    exact hg _ m.2 hc _ m.1
  | d c =>
    intro e g upper P hg hP env xs hw hxs hc
    exact checkD_sound c e g upper P hg hP env xs hw hxs hc
  | split i m l r ihl ihr =>
    intro e g upper P hg hP env xs hw hxs hc
    simp only [checkM, Bool.and_eq_true, Bool.not_eq_true'] at hc
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
  | mono i inc dc c ihc =>
    intro e g upper P hg hP env xs hw hxs hc
    simp only [checkM, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hil, hdom⟩, hsg⟩, hfin⟩, hcc⟩ := hc
    have hlen := hxs.length_eq
    have hi : i < xs.length := by rw [hlen]; exact Nat.blt_eq ▸ hil
    have hsign : ∀ zs, List.Forall₂ (fun x X => x ∈ (toI X).toSet) zs env →
        (if inc then 0 ≤ (e.deriv i).denote zs else (e.deriv i).denote zs ≤ 0) := by
      intro zs hzs
      cases inc
      · simp only [Bool.cond_false] at hsg
        have := checkD_sound dc (e.deriv i) _ true (fun y => y ≤ ((0 : ℚ) : ℝ)) (gLe_sound 0)
          (fun y z h hy => by simp only [↓reduceIte] at h; linarith) env zs hw hzs hsg
        simpa using this
      · simp only [Bool.cond_true] at hsg
        have := checkD_sound dc (e.deriv i) _ false (fun y => ((0 : ℚ) : ℝ) ≤ y) (gGe_sound 0)
          (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith)
          env zs hw hzs hsg
        simpa using this
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    have hself := set_getD_self hi
    generalize hX : env.getD i zeroK = X at hx hwi hcc hfin
    have key : ∀ p : Nat, finK p = true → (∀ r : ℝ, (toF p).toE = r → r ∈ (toI X).toSet ∧
          (if (inc == upper) then xs.getD i 0 ≤ r else r ≤ xs.getD i 0)) →
        checkM e g upper c (env.set i ⟨p, p⟩) = true → P (e.denote xs) := by
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

/-! ### Entry points -/

theorem proveM_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : MCert)
    (h : checkM e (gLe (KI.ofRat c).lo) true cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkM_sound cert e _ true (fun y => y ≤ (c : ℝ)) (gLe_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem proveM_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : MCert)
    (h : checkM e (gLt (KI.ofRat c).lo) true cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkM_sound cert e _ true (fun y => y < (c : ℝ)) (gLt_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem proveM_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : MCert)
    (h : checkM e (gGe (KI.ofRat c).hi) false cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkM_sound cert e _ false (fun y => (c : ℝ) ≤ y) (gGe_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_wf bs) (boxes_mem hxs) h

theorem proveM_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : MCert)
    (h : checkM e (gGt (KI.ofRat c).hi) false cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkM_sound cert e _ false (fun y => (c : ℝ) < y) (gGt_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_wf bs) (boxes_mem hxs) h

omit [ExtSem] in
theorem checkM_split_of {e : IExpr} {g : KI → Bool} {upper : Bool} {i m : Nat} {l r : MCert}
    {env : List KI} (hm : (!isNaN m && Nat.blt m (2 ^ 64)) = true)
    (hl : checkM e g upper l (env.set i ⟨(env.getD i zeroK).lo, m⟩) = true)
    (hr : checkM e g upper r (env.set i ⟨m, (env.getD i zeroK).hi⟩) = true) :
    checkM e g upper (.split i m l r) env = true := by
  simp only [checkM, hl, hr, Bool.and_true]; exact hm

end RealFP
