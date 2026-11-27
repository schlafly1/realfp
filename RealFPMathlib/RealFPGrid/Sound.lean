import RealFPMathlib.IntervalTactic
import RealFPGridNative

/-! # RealFP.Grid: soundness

`checkC_sound`: the natively compiled checker `checkC` (leaves evaluated with realfp's hardware
interval evaluator `evalI`) implies realfp's kernel checker `checkK`; then realfp's
`RealFP.prove_le` / `prove_ge` give the real-number theorem. Everything else is definitional
(`checkGrid_eq`, `checkC3_map`, `checkC2_compile`) or proved (`Top.soundP`, `TopC.sound`).

Theorems for the user (all on `e.denote xs` for `xs ∈ bs`, `bs` rational boxes):

* `prove_le` / `prove_ge`: one certificate, one `native_decide`;
* `proveTop_le` / `proveTop_ge`: a split certificate (`Top`), the sub-checks as `AllP` (one
  `native_decide` each, possibly in other files);
* `proveTopC_le` / `proveTopC_ge`: a two-level split (`TopC`) for very many sub-files. -/

open Interval64 Interval64.KF RealFP.IntervalTactic

namespace RealFP.Grid

/-- The goal predicates only look at non-NaN endpoints, where `canon` is the identity. -/
def CanonOK (g : KI → Bool) : Prop := ∀ a b, g ⟨canon a, canon b⟩ = true → g ⟨a, b⟩ = true

theorem isNaN_qNaN : isNaN qNaN = true := by decide

theorem gLe_canon (c : Nat) : CanonOK (gLe c) := by
  intro a b h
  unfold gLe KF.canon at *
  cases ha : isNaN a <;> cases hb : isNaN b <;> simp_all [isNaN_qNaN]

theorem gGe_canon (c : Nat) : CanonOK (gGe c) := by
  intro a b h
  unfold gGe KF.canon at *
  cases ha : isNaN a <;> cases hb : isNaN b <;> simp_all [isNaN_qNaN]

theorem evalC_eq {env : List KI} (h : ∀ X ∈ env, WF X) (e : IExpr) :
    evalC env e = ⟨canon (evalK env e).lo, canon (evalK env e).hi⟩ := by
  have hK := evalK_toI h e
  have hm : (env.map fun X => (⟨toFlC X.lo, toFlC X.hi⟩ : Interval64)) = env.map toI := rfl
  have h1 : evalI (env.map fun X => (⟨toFlC X.lo, toFlC X.hi⟩ : Interval64)) e =
      toI (evalK env e) := by
    rw [hm, hK.1]
  unfold evalC
  simp only [h1]
  show KI.mk (toF (evalK env e).lo).toBits.toNat (toF (evalK env e).hi).toBits.toNat = _
  rw [toNat_toBits_toF hK.2.1, toNat_toBits_toF hK.2.2]

theorem checkC_sound (e : IExpr) (g : KI → Bool) (hg : CanonOK g) :
    ∀ (c : Cert) (env : List KI), (∀ X ∈ env, WF X) → checkC e g c env = true →
      checkK e g c env = true := by
  intro c
  induction c with
  | leaf =>
    intro env hwf h
    simp only [checkC, checkK] at *
    rw [evalC_eq hwf] at h
    exact hg _ _ h
  | split i m l r ihl ihr =>
    intro env hwf h
    simp only [checkC, checkK, Bool.and_eq_true] at *
    obtain ⟨⟨⟨hn, hm⟩, hl⟩, hr⟩ := h
    have hm' : m < 2 ^ 64 := Nat.blt_eq ▸ hm
    have hwi := getD_wf hwf i
    refine ⟨⟨⟨hn, hm⟩, ihl _ (set_wf hwf i ⟨hwi.1, hm'⟩) hl⟩, ihr _ (set_wf hwf i ⟨hm', hwi.2⟩) hr⟩

theorem proveC2_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkC2 (compile e) (gLe (KI.ofRat c).lo) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) := by
  rw [checkC2_compile] at h
  exact RealFP.prove_le e bs c cert (checkC_sound e _ (gLe_canon _) cert _ (boxes_wf bs) h) xs hxs

theorem proveC2_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Cert)
    (h : checkC2 (compile e) (gGe (KI.ofRat c).hi) cert (boxes bs) = true) (xs : List ℝ)
    (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs := by
  rw [checkC2_compile] at h
  exact RealFP.prove_ge e bs c cert (checkC_sound e _ (gGe_canon _) cert _ (boxes_wf bs) h) xs hxs

/-- `e ≤ c` on the boxes `bs` from one certificate `hex` (`d` = number of variables), checked by
`native_decide` (the C checker). -/
theorem prove_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (d : Nat) (hex : String)
    (h : checkGrid (compile e) true (KI.ofRat c).lo d 0 hex ((boxes bs).map toIC) = true)
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) := by
  simp only [checkGrid_eq, ↓reduceIte, checkC3_map] at h
  exact proveC2_le e bs c _ h xs hxs

/-- `c ≤ e` on the boxes `bs` from one certificate `hex`. -/
theorem prove_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (d : Nat) (hex : String)
    (h : checkGrid (compile e) false (KI.ofRat c).hi d 0 hex ((boxes bs).map toIC) = true)
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs := by
  simp only [checkGrid_eq, Bool.false_eq_true, ↓reduceIte, checkC3_map] at h
  exact proveC2_ge e bs c _ h xs hxs

/-- Split certificate: `midsOK` (kernel) and every sub-check (`native_decide`, anywhere). -/
theorem proveTop_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (d : Nat) (t : Top)
    (hm : t.midsOK = true)
    (hj : AllP (fun j => Job.check (compile e) true (KI.ofRat c).lo d j = true) (t.jobs (boxes bs)))
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) := by
  have h := Top.soundP (compile e) true (KI.ofRat c).lo d t (boxes bs) hm hj
  simp only [↓reduceIte] at h
  exact proveC2_le e bs c _ h xs hxs

theorem proveTop_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (d : Nat) (t : Top)
    (hm : t.midsOK = true)
    (hj : AllP (fun j => Job.check (compile e) false (KI.ofRat c).hi d j = true) (t.jobs (boxes bs)))
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs := by
  have h := Top.soundP (compile e) false (KI.ofRat c).hi d t (boxes bs) hm hj
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact proveC2_ge e bs c _ h xs hxs

/-- Two-level split: the leaves of `t` are certificates proved by `checkC2` (e.g. from
`Top.sound` in other files). -/
theorem proveTopC_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (t : TopC) (hm : t.midsOK = true)
    (hl : AllP (fun p => checkC2 (compile e) (gLe (KI.ofRat c).lo) p.1 p.2 = true) (t.leaves (boxes bs)))
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  proveC2_le e bs c _ (TopC.sound _ _ t _ hm hl) xs hxs

theorem proveTopC_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (t : TopC) (hm : t.midsOK = true)
    (hl : AllP (fun p => checkC2 (compile e) (gGe (KI.ofRat c).hi) p.1 p.2 = true) (t.leaves (boxes bs)))
    (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  proveC2_ge e bs c _ (TopC.sound _ _ t _ hm hl) xs hxs

/-- Transport a stored bound (e.g. `bound` from `grid/gen_lean.py`) to the reified goal
(`interval_grid (use := thm)`; the equalities are proved by `decide +kernel`). -/
theorem use_le {e e' : IExpr} {bs bs' : List (ℚ × ℚ)} {c c' : ℚ}
    (h : ∀ xs, RealFP.InBoxes xs bs' → e'.denote xs ≤ (c' : ℝ)) (he : e = e') (hb : bs = bs')
    (hc : c = c') (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : e.denote xs ≤ (c : ℝ) := by
  subst he hb hc; exact h xs hxs

theorem use_ge {e e' : IExpr} {bs bs' : List (ℚ × ℚ)} {c c' : ℚ}
    (h : ∀ xs, RealFP.InBoxes xs bs' → (c' : ℝ) ≤ e'.denote xs) (he : e = e') (hb : bs = bs')
    (hc : c = c') (xs : List ℝ) (hxs : RealFP.InBoxes xs bs) : (c : ℝ) ≤ e.denote xs := by
  subst he hb hc; exact h xs hxs

end RealFP.Grid
