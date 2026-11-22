/-
Soundness of the kernel 2D Taylor rule `KF.KQ.taylor2K` / `taylor2Bound`.

Under `toI`, `t2SumK` is exactly `Quad.t2Sum` on the `Float` cells (`t2SumK_toI`), so soundness
follows from `RealFP.Taylor2.integral2_mem_taylor2_smooth`.

* `integral2_mem_taylor2K` : `∫∫ ∈ toI R` when `taylor2K … = some R`.
* `integral2_bounds_of_taylor2Bound` : `ql ≤ ∫_{qa}^{qb} ∫_{qc}^{qd} e ≤ qh` from a
  kernel-checked certificate, no side conditions.
-/
import RealFPMathlib.KQuad
import RealFPMathlib.Taylor2
import Interval64.Kernel.Quad2

open Interval64 Interval64.Quad Interval64.KF Interval64.KF.KQ Set intervalIntegral MeasureTheory

noncomputable section

namespace RealFP.KTaylor2

open RealFP RealFP.KQ RealFP.Taylor2

def fl3 (c : Nat × Nat × Nat) : Float × Float × Float := (toF c.1, toF c.2.1, toF c.2.2)

theorem wf_pt {p : Nat} (h : finK p = true) : WF (pt p) := ⟨(finK_spec h).1, (finK_spec h).1⟩

theorem wf_box {p q : Nat} (hp : finK p = true) (hq : finK q = true) : WF ⟨p, q⟩ :=
  ⟨(finK_spec hp).1, (finK_spec hq).1⟩

theorem momK_toI {lo m hi : Nat} (hl : finK lo = true) (hm : finK m = true) (hh : finK hi = true)
    (j : Nat) : toI (momK lo m hi j) = momF (toF lo) (toF m) (toF hi) j ∧ WF (momK lo m hi j) := by
  have w1 := sub_wf (wf_pt hh) (wf_pt hm)
  have p1 := pown_toI w1 (j + 1)
  have w2 := sub_wf (wf_pt hl) (wf_pt hm)
  have p2 := pown_toI w2 (j + 1)
  have w3 := sub_wf p1.2 p2.2
  have r := ofRat_toI (1 / (fact (j + 1) : Rat))
  refine ⟨?_, mul_wf w3 r.2⟩
  unfold momK momF
  rw [mul_toI w3 r.2, sub_toI p1.2 p2.2, p1.1, p2.1, sub_toI (wf_pt hh) (wf_pt hm),
    sub_toI (wf_pt hl) (wf_pt hm), r.1]
  rfl

theorem sumK_toI {f : Nat → KI} {F : Nat → Interval64} :
    ∀ n, (∀ j < n, toI (f j) = F j ∧ WF (f j)) → toI (sumK f n) = sumI F n ∧ WF (sumK f n)
  | 0, _ => ⟨toI_zeroK, wf_zeroK⟩
  | n + 1, h => by
    have ih := sumK_toI n fun j hj => h j (by omega)
    have hn := h n (by omega)
    refine ⟨?_, add_wf ih.2 hn.2⟩
    show toI (KI.add _ _) = sumI F n + F n
    rw [add_toI ih.2 hn.2, ih.1, hn.1]

theorem evalK2_toI {A B : KI} (hA : WF A) (hB : WF B) (d : IExpr) :
    toI (evalK [A, B] d) = evalI [toI A, toI B] d ∧ WF (evalK [A, B] d) :=
  evalK_toI (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro X (rfl | rfl) <;> assumption) d

theorem cellOKK_fin {c : Nat × Nat × Nat} (h : cellOKK c = true) :
    finK c.1 = true ∧ finK c.2.1 = true ∧ finK c.2.2 = true ∧ le c.1 c.2.1 = true ∧
      le c.2.1 c.2.2 = true := by
  simp only [cellOKK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem t2CellK_toI (e : IExpr) (K : Nat) {cx cy : Nat × Nat × Nat} (hx : cellOKK cx = true)
    (hy : cellOKK cy = true) :
    toI (t2CellK e K cx cy) = t2Cell e K (fl3 cx) (fl3 cy) ∧ WF (t2CellK e K cx cy) := by
  obtain ⟨x1, x2, x3, -, -⟩ := cellOKK_fin hx
  obtain ⟨y1, y2, y3, -, -⟩ := cellOKK_fin hy
  have inner : ∀ i, toI (t2InnerK e K i cx cy.2.1) = t2Inner e K i (fl3 cx) (toF cy.2.1) ∧
      WF (t2InnerK e K i cx cy.2.1) := by
    intro i
    have hs := sumK_toI (f := fun j => KI.mul (evalK [pt cx.2.1, pt cy.2.1] (dxy e i j))
        (momK cx.1 cx.2.1 cx.2.2 j))
      (F := fun j => evalI [ptF (toF cx.2.1), ptF (toF cy.2.1)] (dxy e i j) *
        momF (toF cx.1) (toF cx.2.1) (toF cx.2.2) j) K fun j _ => by
      have ev := evalK2_toI (wf_pt x2) (wf_pt y2) (dxy e i j)
      have mo := momK_toI x1 x2 x3 j
      exact ⟨by rw [mul_toI ev.2 mo.2, ev.1, mo.1]; rfl, mul_wf ev.2 mo.2⟩
    have ev := evalK2_toI (wf_box x1 x3) (wf_pt y2) (dxy e i K)
    have mo := momK_toI x1 x2 x3 K
    refine ⟨?_, add_wf hs.2 (mul_wf ev.2 mo.2)⟩
    unfold t2InnerK
    rw [add_toI hs.2 (mul_wf ev.2 mo.2), hs.1, mul_toI ev.2 mo.2, ev.1, mo.1]
    rfl
  have hs := sumK_toI (f := fun i => KI.mul (momK cy.1 cy.2.1 cy.2.2 i) (t2InnerK e K i cx cy.2.1))
    (F := fun i => momF (toF cy.1) (toF cy.2.1) (toF cy.2.2) i * t2Inner e K i (fl3 cx) (toF cy.2.1))
    K fun i _ => by
      have mo := momK_toI y1 y2 y3 i
      exact ⟨by rw [mul_toI mo.2 (inner i).2, mo.1, (inner i).1], mul_wf mo.2 (inner i).2⟩
  have ev := evalK2_toI (wf_box x1 x3) (wf_box y1 y3) (dxy e K 0)
  have mo := momK_toI y1 y2 y3 K
  have w1 := mul_wf ev.2 mo.2
  have w2 := sub_wf (wf_pt x3) (wf_pt x1)
  refine ⟨?_, add_wf hs.2 (mul_wf w1 w2)⟩
  unfold t2CellK
  rw [add_toI hs.2 (mul_wf w1 w2), hs.1, mul_toI w1 w2, mul_toI ev.2 mo.2, ev.1, mo.1,
    sub_toI (wf_pt x3) (wf_pt x1)]
  rfl

theorem t2SumK_toI (e : IExpr) (K : Nat) {ys : List (Nat × Nat × Nat)} (hy : ys.all cellOKK = true) :
    ∀ xs : List (Nat × Nat × Nat), xs.all cellOKK = true →
      toI (t2SumK e K xs ys) = t2Sum e K (xs.map fl3) (ys.map fl3) ∧ WF (t2SumK e K xs ys) := by
  have row : ∀ cx, cellOKK cx = true → ∀ zs : List (Nat × Nat × Nat), zs.all cellOKK = true →
      toI (zs.foldr (fun cy acc' => KI.add (t2CellK e K cx cy) acc') zeroK) =
        (zs.map fl3).foldr (fun cy acc' => t2Cell e K (fl3 cx) cy + acc') zeroI ∧
      WF (zs.foldr (fun cy acc' => KI.add (t2CellK e K cx cy) acc') zeroK) := by
    intro cx hcx zs
    induction zs with
    | nil => intro _; exact ⟨toI_zeroK, wf_zeroK⟩
    | cons cy zs ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      have c := t2CellK_toI e K hcx h.1
      have r := ih h.2
      refine ⟨?_, add_wf c.2 r.2⟩
      simp only [List.foldr_cons, List.map_cons]
      rw [add_toI c.2 r.2, c.1, r.1]
  intro xs
  induction xs with
  | nil => intro _; exact ⟨toI_zeroK, wf_zeroK⟩
  | cons cx xs ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true] at h
    have r := row cx h.1 ys hy
    have t := ih h.2
    refine ⟨?_, add_wf r.2 t.2⟩
    show toI (KI.add _ (t2SumK e K xs ys)) = _ + t2Sum e K (xs.map fl3) (ys.map fl3)
    rw [add_toI r.2 t.2, r.1, t.1]

theorem cellOKF_fl3 {c : Nat × Nat × Nat} (h : cellOKK c = true) : cellOKF (fl3 c) = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cellOKK_fin h
  have fin : ∀ {p : Nat}, finK p = true → finite (toF p) = true := by
    intro p hp
    simp only [finK, Bool.and_eq_true, Bool.not_eq_true'] at hp
    have hb : p < 2 ^ 64 := Nat.blt_eq ▸ hp.2
    simp only [finite, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(isNaN_toF hb).trans hp.1.1, (isInf_toF' hb).trans hp.1.2⟩
  simp only [cellOKF, fl3, Bool.and_eq_true]
  refine ⟨⟨⟨⟨fin h1, fin h2⟩, fin h3⟩, ?_⟩, ?_⟩
  · exact decide_eq_true (of_decide_eq_true ((le_toF (finK_spec h1).1 (finK_spec h2).1).trans h4))
  · exact decide_eq_true (of_decide_eq_true ((le_toF (finK_spec h2).1 (finK_spec h3).1).trans h5))

theorem chainF_fl3 {b : Nat} :
    ∀ (cs : List (Nat × Nat × Nat)) (a : Nat), chainOK a b cs = true →
      chainF (toF a) (toF b) (cs.map fl3) = true
  | [], a, h => by
    have : a = b := Nat.eq_of_beq_eq_true h
    subst this; simp [chainF]
  | c :: cs, a, h => by
    simp only [chainOK, Bool.and_eq_true] at h
    have : a = c.1 := Nat.eq_of_beq_eq_true h.1
    subst this
    simp only [List.map_cons, chainF, Bool.and_eq_true]
    exact ⟨by simp [fl3], chainF_fl3 cs c.2.2 h.2⟩

/-- **Soundness of `taylor2K`.** -/
theorem integral2_mem_taylor2K {e : IExpr} {K a b c d : Nat} {xs ys : List (Nat × Nat × Nat)}
    {R : KI} (h : taylor2K e K a b c d xs ys = some R) :
    (∫ x in (toF a).toReal..(toF b).toReal, ∫ y in (toF c).toReal..(toF d).toReal, e.denote [x, y]) ∈
      (toI R).toSet ∧ WF R := by
  unfold taylor2K at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨h2, h0⟩, hchx⟩, hchy⟩, hallx⟩, hally⟩, hsm⟩ := hc
    cases Option.some.inj h
    have hok : t2OK K (toF a) (toF b) (toF c) (toF d) (xs.map fl3) (ys.map fl3) = true := by
      simp only [t2OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_map]
      refine ⟨⟨⟨⟨⟨Nat.eq_of_beq_eq_true h2, by simpa [Nat.blt_eq] using h0⟩, chainF_fl3 xs a hchx⟩,
        chainF_fl3 ys c hchy⟩, ?_⟩, ?_⟩
      · exact List.all_eq_true.2 fun cx hcx => cellOKF_fl3 (List.all_eq_true.1 hallx cx hcx)
      · exact List.all_eq_true.2 fun cy hcy => cellOKF_fl3 (List.all_eq_true.1 hally cy hcy)
    have hm := integral2_mem_taylor2_smooth e K (a := toF a) (b := toF b) (c := toF c) (d := toF d)
      (xs.map fl3) (ys.map fl3) hsm
    simp only [taylor2, hok, ↓reduceIte] at hm
    have t := t2SumK_toI e K hally xs hallx
    rw [t.1]
    exact ⟨hm, t.2⟩
  · exact absurd h (by simp)

theorem toReal_of_ratOf {p : Nat} {q : ℚ} (h : ratOf p = some q) : (toF p).toReal = q := by
  obtain ⟨-, hn, he⟩ := ratOf_sound h
  have hi : (toF p).isInf = false := by
    cases hc : (toF p).isInf
    · rfl
    · have := (isInf_iff_toE.1 hc).1; rw [he] at this; simp at this
  have := RealFP.Poly.toE_eq_toReal hn hi
  rw [he] at this
  exact (EReal.coe_injective this).symm

/-- **Rigorous 2D integral bounds** from a kernel-checked `taylor2Bound` certificate. -/
theorem integral2_bounds_of_taylor2Bound {e : IExpr} {K a b c d : Nat}
    {xs ys : List (Nat × Nat × Nat)} {qa qb qc qd ql qh : ℚ}
    (h : taylor2Bound e K a b c d xs ys qa qb qc qd ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, ∫ y in (qc : ℝ)..qd, e.denote [x, y]) ∧
      (∫ x in (qa : ℝ)..qb, ∫ y in (qc : ℝ)..qd, e.denote [x, y]) ≤ qh := by
  unfold taylor2Bound at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, h⟩ := h
  split at h
  · rename_i R hR
    obtain ⟨hm, -⟩ := integral2_mem_taylor2K hR
    rw [toReal_of_ratOf ha, toReal_of_ratOf hb, toReal_of_ratOf hc, toReal_of_ratOf hd] at hm
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 hm
    split at h
    · rename_i l u hl hu
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h1' := (ratOf_sound hl).2.2
      have h2' := (ratOf_sound hu).2.2
      simp only [toI] at h1 h2
      rw [h1'] at h1; rw [h2'] at h2
      exact ⟨le_trans (by exact_mod_cast h.1) (EReal.coe_le_coe_iff.1 h1),
        le_trans (EReal.coe_le_coe_iff.1 h2) (by exact_mod_cast h.2)⟩
    · simp at h
  · simp at h

end RealFP.KTaylor2
