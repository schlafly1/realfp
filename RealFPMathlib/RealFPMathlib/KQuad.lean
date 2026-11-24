/-
Soundness of the kernel Taylor quadrature `Interval64.KF.KQ.quadK` (core `Interval64/Kernel/Quad.lean`).

* `integral_mem_quadK` : `quadK e K a b cs = some R` gives `∫_A^B e.denote [x] ∈ toI R`
  (`A`, `B` the real values of the bit patterns `a`, `b`).
* `integral_bounds_of_quadBound` : `quadBound e K a b cs qa qb ql qh = true` gives
  `ql ≤ ∫_qa^qb e.denote [x] ≤ qh` (checked by `decide +kernel`).
-/
import RealFPMathlib.TaylorBound
import RealFPMathlib.IntervalDeriv
import Interval64.Kernel.Quad

open Interval64 Interval64.KF Interval64.KF.KQ Set intervalIntegral MeasureTheory Finset
open Interval64Proofs.FloatBits Interval64.Spec

noncomputable section

namespace RealFP.KQ

open RealFP RealFP.Taylor

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-- The `j`-th derivative expression (in variable `0`). -/
def dN (e : IExpr) (j : ℕ) : IExpr := (fun d => d.deriv 0)^[j] e

omit [ExtTbl] [ExtSem] in
theorem dN_succ (e : IExpr) (j : ℕ) : dN e (j + 1) = dN (e.deriv 0) j :=
  Function.iterate_succ_apply _ _ _

omit [ExtTbl] [ExtSem] in
theorem dN_succ' (e : IExpr) (j : ℕ) : dN e (j + 1) = (dN e j).deriv 0 :=
  Function.iterate_succ_apply' _ _ _

omit [ExtTbl] [ExtSem] in
theorem derivs_ne_nil (e : IExpr) : ∀ k, derivs e k ≠ []
  | 0 => by simp [derivs]
  | _ + 1 => by simp [derivs]

omit [ExtTbl] [ExtSem] in
theorem getLastD_derivs : ∀ (k : ℕ) (e d : IExpr), (derivs e k).getLastD d = dN e k
  | 0, _, _ => rfl
  | k + 1, e, d => by
    show (e :: derivs (e.deriv 0) k).getLastD d = _
    rw [List.getLastD_cons, getLastD_derivs k, dN_succ]

omit [ExtTbl] [ExtSem] in
theorem mem_dropLast_derivs : ∀ (k : ℕ) (e : IExpr) (j : ℕ), j < k → dN e j ∈ (derivs e k).dropLast
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, e, j, h => by
    show dN e j ∈ (e :: derivs (e.deriv 0) k).dropLast
    obtain ⟨x, l, hl⟩ := List.exists_cons_of_ne_nil (derivs_ne_nil (e.deriv 0) k)
    rw [hl, List.dropLast_cons_cons, ← hl]
    cases j with
    | zero => exact List.mem_cons_self ..
    | succ j => rw [dN_succ]; exact List.mem_cons_of_mem _ (mem_dropLast_derivs k _ j (by omega))

omit [ExtTbl] [ExtSem] in
theorem fact_eq : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by simp [fact, fact_eq n, Nat.factorial_succ]

/-! ### Points -/

omit [ExtTbl] [ExtSem] in
theorem finK_spec {p : Nat} (h : finK p = true) : p < 2 ^ 64 ∧ (toF p).isNaN = false := by
  simp only [finK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, -⟩, hb⟩ := h
  have hp : p < 2 ^ 64 := Nat.blt_eq ▸ hb
  exact ⟨hp, (isNaN_toF hp).trans hn⟩

omit [ExtTbl] [ExtSem] in
theorem finK_real {p : Nat} (h : finK p = true) :
    ∃ r : ℝ, (toF p).toE = r ∧ r ∈ (toI ⟨p, p⟩).toSet ∧ WF ⟨p, p⟩ := finK_point h

omit [ExtTbl] [ExtSem] in
theorem le_real {p q : Nat} (hp : finK p = true) (hq : finK q = true) (h : le p q = true)
    {P Q : ℝ} (hP : (toF p).toE = P) (hQ : (toF q).toE = Q) : P ≤ Q := by
  obtain ⟨hp1, hp2⟩ := finK_spec hp
  obtain ⟨hq1, hq2⟩ := finK_spec hq
  have h1 : toF p ≤ toF q := by
    have := le_toF hp1 hq1; rw [h] at this; exact of_decide_eq_true this
  have := (float_le_iff_toE hp2 hq2).1 h1
  rw [hP, hQ] at this; exact EReal.coe_le_coe_iff.1 this

omit [ExtTbl] [ExtSem] in
theorem mem_seg {lo hi : Nat} (hl : finK lo = true) (hh : finK hi = true) {L H t : ℝ}
    (hL : (toF lo).toE = L) (hH : (toF hi).toE = H) (ht : t ∈ Icc L H) :
    t ∈ (toI ⟨lo, hi⟩).toSet ∧ WF ⟨lo, hi⟩ := by
  obtain ⟨hl1, hl2⟩ := finK_spec hl
  obtain ⟨hh1, hh2⟩ := finK_spec hh
  refine ⟨mem_toSet_of_toE (I := toI ⟨lo, hi⟩) hl2 hh2 ?_ ?_, hl1, hh1⟩
  · show (toF lo).toE ≤ _; rw [hL]; exact EReal.coe_le_coe_iff.2 ht.1
  · show _ ≤ (toF hi).toE; rw [hH]; exact EReal.coe_le_coe_iff.2 ht.2

/-! ### Moments and the Taylor part -/

omit [ExtTbl] [ExtSem] in
theorem mom_mem {lo m hi : Nat} {L M H : ℝ} (hL : L ∈ (toI (pt lo)).toSet) (wL : WF (pt lo))
    (hM : M ∈ (toI (pt m)).toSet) (wM : WF (pt m)) (hH : H ∈ (toI (pt hi)).toSet)
    (wH : WF (pt hi)) (j : ℕ) :
    mom L M H j ∈ (toI (momK lo m hi j)).toSet ∧ WF (momK lo m hi j) := by
  unfold momK mom
  have w1 := sub_wf wH wM
  have p1 := pown_toI w1 (j + 1)
  have w2 := sub_wf wL wM
  have p2 := pown_toI w2 (j + 1)
  have w3 := sub_wf p1.2 p2.2
  have r := ofRat_toI (1 / (fact (j + 1) : ℚ))
  refine ⟨?_, mul_wf w3 r.2⟩
  rw [mul_toI w3 r.2, sub_toI p1.2 p2.2, p1.1, p2.1, sub_toI wH wM, sub_toI wL wM, r.1]
  have hq := mem_toSet_ofRat (1 / (fact (j + 1) : ℚ))
  have e : ((1 / (fact (j + 1) : ℚ) : ℚ) : ℝ) = 1 / ((j + 1).factorial : ℝ) := by
    rw [fact_eq]; push_cast; ring
  rw [e] at hq
  exact Iv.mem_mul (Iv.sub_mem (mem_pown (Iv.sub_mem hH hM) _) (mem_pown (Iv.sub_mem hL hM) _)) hq

omit [ExtSem] in
theorem taylorK_cons {lo m hi j : Nat} {d : IExpr} {ds : List IExpr} (h : ds ≠ []) :
    taylorK lo m hi j (d :: ds) =
      KI.add (KI.mul (evalK [pt m] d) (momK lo m hi j)) (taylorK lo m hi (j + 1) ds) := by
  cases ds with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem taylor_mem {lo m hi : Nat} {L M H : ℝ} (hL : L ∈ (toI (pt lo)).toSet) (wL : WF (pt lo))
    (hM : M ∈ (toI (pt m)).toSet) (wM : WF (pt m)) (hH : H ∈ (toI (pt hi)).toSet)
    (wH : WF (pt hi)) :
    ∀ (k : ℕ) (e : IExpr) (j : ℕ),
      (∑ i ∈ range k, (dN e i).denote [M] * mom L M H (j + i)) ∈
        (toI (taylorK lo m hi j (derivs e k))).toSet ∧ WF (taylorK lo m hi j (derivs e k))
  | 0, e, j => by
    show (∑ i ∈ range 0, _) ∈ (toI zeroK).toSet ∧ WF zeroK
    rw [Finset.sum_range_zero, toI_zeroK]; exact ⟨zero_mem_zeroI, wf_zeroK⟩
  | k + 1, e, j => by
    show _ ∈ (toI (taylorK lo m hi j (e :: derivs (e.deriv 0) k))).toSet ∧
      WF (taylorK lo m hi j (e :: derivs (e.deriv 0) k))
    rw [taylorK_cons (derivs_ne_nil _ k), Finset.sum_range_succ']
    have ih := taylor_mem hL wL hM wM hH wH k (e.deriv 0) (j + 1)
    have hw : ∀ X ∈ [pt m], WF X := by simpa using wM
    have me := memK (xs := [M]) hw (List.Forall₂.cons hM List.Forall₂.nil) e
    have mo := mom_mem hL wL hM wM hH wH j
    have w1 := mul_wf me.2 mo.2
    have e1 : (∑ i ∈ range k, (dN e (i + 1)).denote [M] * mom L M H (j + (i + 1))) =
        ∑ i ∈ range k, (dN (e.deriv 0) i).denote [M] * mom L M H (j + 1 + i) :=
      sum_congr rfl fun i _ => by rw [dN_succ, show j + (i + 1) = j + 1 + i by omega]
    refine ⟨?_, add_wf w1 ih.2⟩
    rw [e1, add_comm (∑ i ∈ range k, (dN (e.deriv 0) i).denote [M] * mom L M H (j + 1 + i)),
      add_toI w1 ih.2, mul_toI me.2 mo.2]
    exact Iv.add_mem (Iv.mem_mul me.1 mo.1) ih.1

/-! ### One cell -/

omit [ExtSem] in
theorem cellOK_fin {ds : List IExpr} {c : Nat × Nat × Nat} (h : cellOK ds c = true) :
    finK c.1 = true ∧ finK c.2.2 = true := by
  simp only [cellOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.2⟩

theorem cell_mem {e : IExpr} {K : ℕ} (hK : Even K) (hK0 : 0 < K) {c : Nat × Nat × Nat}
    (hc : cellOK (derivs e K) c = true) {L H : ℝ} (hL : (toF c.1).toE = L)
    (hH : (toF c.2.2).toE = H) :
    L ≤ H ∧ IntervalIntegrable (fun x => e.denote [x]) volume L H ∧
      (∫ x in L..H, e.denote [x]) ∈ (toI (cellK (derivs e K) K (dN e K) c)).toSet ∧
      WF (cellK (derivs e K) K (dN e K) c) := by
  obtain ⟨lo, m, hi⟩ := c
  simp only [cellOK, Bool.and_eq_true, List.all_eq_true] at hc hL hH
  obtain ⟨⟨⟨⟨⟨fl, fm⟩, fh⟩, hlm⟩, hmh⟩, hdom⟩ := hc
  obtain ⟨M, hMe, hM, wM⟩ := finK_real fm
  obtain ⟨L', hL', hLm, wL⟩ := finK_real fl
  obtain ⟨H', hH', hHm, wH⟩ := finK_real fh
  obtain rfl : L' = L := EReal.coe_injective (hL'.symm.trans hL)
  obtain rfl : H' = H := EReal.coe_injective (hH'.symm.trans hH)
  have hLM := le_real fl fm hlm hL hMe
  have hMH := le_real fm fh hmh hMe hH
  set F : ℕ → ℝ → ℝ := fun j t => (dN e j).denote [t] with hF
  have hseg := fun t (ht : t ∈ Icc L' H') => mem_seg fl fh hL hH ht
  have hd : ∀ j < K, ∀ t ∈ Icc L' H', HasDerivAt (F j) (F (j + 1) t) t := by
    intro j hj t ht
    have ms := hseg t ht
    have hw : ∀ X ∈ [(⟨lo, hi⟩ : KI)], WF X := by simpa using ms.2
    have hdm := domOK_sound (xs := [t]) hw (List.Forall₂.cons ms.1 List.Forall₂.nil) _
      (hdom _ (mem_dropLast_derivs K e j hj))
    have := hasDerivAt_denote (xs := [t]) (i := 0) (by simp) _ hdm
    simp only [hF]; rw [dN_succ', denote_deriv]; simpa using this
  have hw0 : ∀ X ∈ [(⟨lo, hi⟩ : KI)], WF X := by
    intro X hX; simp only [List.mem_singleton] at hX; subst hX; exact ⟨wL.1, wH.1⟩
  have hD : ∀ t ∈ Icc L' H', F K t ∈ toI (evalK [⟨lo, hi⟩] (dN e K)) := fun t ht =>
    (memK hw0 (List.Forall₂.cons (hseg t ht).1 List.Forall₂.nil) _).1
  have wD := (evalK_toI hw0 (dN e K)).2
  have mo := mom_mem hLm wL hM wM hHm wH K
  obtain ⟨r, hr, hint⟩ := integral_mem_taylorCell hK hK0 hLM hMH hd hD mo.1
  have hc0 : ContinuousOn (F 0) (Icc L' H') :=
    fun t ht => (hd 0 hK0 t ht).continuousAt.continuousWithinAt
  have tm := taylor_mem hLm wL hM wM hHm wH K e 0
  simp only [zero_add] at tm
  refine ⟨hLM.trans hMH, hc0.intervalIntegrable_of_Icc (hLM.trans hMH), ?_,
    add_wf tm.2 (mul_wf wD mo.2)⟩
  show _ ∈ (toI (KI.add (taylorK lo m hi 0 (derivs e K))
    (KI.mul (evalK [⟨lo, hi⟩] (dN e K)) (momK lo m hi K)))).toSet
  rw [add_toI tm.2 (mul_wf wD mo.2), mul_toI wD mo.2,
    show (∫ x in L'..H', e.denote [x]) = ∫ x in L'..H', F 0 x from rfl, hint]
  exact Iv.add_mem tm.1 hr

/-! ### Chains of cells -/

theorem chain_mem {e : IExpr} {K : ℕ} (hK : Even K) (hK0 : 0 < K) {b : Nat} {B : ℝ}
    (hB : (toF b).toE = B) :
    ∀ (cs : List (Nat × Nat × Nat)) (a : Nat) {A : ℝ}, (toF a).toE = A →
      chainOK a b cs = true → cs.all (cellOK (derivs e K)) = true →
      IntervalIntegrable (fun x => e.denote [x]) volume A B ∧
        (∫ x in A..B, e.denote [x]) ∈ (toI (sumCells (derivs e K) K (dN e K) cs)).toSet ∧
        WF (sumCells (derivs e K) K (dN e K) cs)
  | [], a, A, hA, hch, _ => by
    have hab : a = b := Nat.eq_of_beq_eq_true hch
    subst hab
    obtain rfl : A = B := EReal.coe_injective (hA.symm.trans hB)
    refine ⟨IntervalIntegrable.refl, ?_, wf_zeroK⟩
    show _ ∈ (toI zeroK).toSet
    rw [integral_same, toI_zeroK]; exact zero_mem_zeroI
  | c :: cs, a, A, hA, hch, hall => by
    simp only [chainOK, Bool.and_eq_true] at hch
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have ha : a = c.1 := Nat.eq_of_beq_eq_true hch.1
    subst ha
    obtain ⟨H, hH, -, -⟩ := finK_real (cellOK_fin hall.1).2
    have cell := cell_mem hK hK0 hall.1 hA hH
    have rest := chain_mem hK hK0 hB cs c.2.2 hH hch.2 hall.2
    refine ⟨cell.2.1.trans rest.1, ?_, add_wf cell.2.2.2 rest.2.2⟩
    rw [← integral_add_adjacent_intervals cell.2.1 rest.1]
    show _ ∈ (toI (KI.add (cellK (derivs e K) K (dN e K) c)
      (sumCells (derivs e K) K (dN e K) cs))).toSet
    rw [add_toI cell.2.2.2 rest.2.2]
    exact Iv.add_mem cell.2.2.1 rest.2.1

/-- **Soundness of the kernel Taylor quadrature.** -/
theorem integral_mem_quadK {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)} {R : KI}
    (h : quadK e K a b cs = some R) {A B : ℝ} (hA : (toF a).toE = A) (hB : (toF b).toE = B) :
    (∫ x in A..B, e.denote [x]) ∈ (toI R).toSet ∧ WF R := by
  unfold quadK at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨h2, h0⟩, hch⟩, hall⟩ := hc
    cases Option.some.inj h
    have hK : Even K := Nat.even_iff.2 (Nat.eq_of_beq_eq_true h2)
    have hK0 : 0 < K := by simpa [Nat.blt_eq] using h0
    rw [getLastD_derivs]
    exact (chain_mem hK hK0 hB cs a hA hch hall).2
  · exact absurd h (by simp)

omit [ExtTbl] [ExtSem] in
theorem ratOf_sound {p : Nat} {q : ℚ} (h : ratOf p = some q) :
    p < 2 ^ 64 ∧ (toF p).isNaN = false ∧ (toF p).toE = ((q : ℝ) : EReal) := by
  unfold ratOf at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hc
    have hb : bitsToRat? (toF p).toBits = some q := by
      rw [toBits_toF_of_not_nan hc.1 hc.2]; exact h
    exact ⟨hc.1, (isNaN_toF hc.1).trans hc.2, toE_of_bitsToRat? hb⟩
  · exact absurd h (by simp)

/-- **Rigorous integral bounds** from a kernel-checked `quadBound` certificate. -/
theorem integral_bounds_of_quadBound {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)}
    {qa qb ql qh : ℚ} (h : quadBound e K a b cs qa qb ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧
      (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  unfold quadBound at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hb⟩, h⟩ := h
  split at h
  · rename_i R hR
    obtain ⟨hm, -⟩ := integral_mem_quadK hR (ratOf_sound ha).2.2 (ratOf_sound hb).2.2
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 hm
    split at h
    · rename_i l u hl hu
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h1' := (ratOf_sound hl).2.2
      have h2' := (ratOf_sound hu).2.2
      simp only [toI] at h1 h2
      rw [h1'] at h1; rw [h2'] at h2
      refine ⟨le_trans (by exact_mod_cast h.1) (EReal.coe_le_coe_iff.1 h1),
        le_trans (EReal.coe_le_coe_iff.1 h2) (by exact_mod_cast h.2)⟩
    · simp at h
  · simp at h

end RealFP.KQ
