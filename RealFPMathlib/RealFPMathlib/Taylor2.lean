/-
Soundness of the higher-order 2D rule `Interval64.Quad.taylor2` (tensor Taylor cells).

On a cell `[xl, xh] × [yl, yh]` with midpoints `(mx, my)`, for even `K > 0`:
`∫∫ f = Σ_{i<K} mom_y i · ∫_x ∂ᵧⁱ f (x, my) dx + ∫_x r(x) dx` (Taylor in `y`, Lagrange remainder
`r(x) ∈ [∂ᵧᴷ f](X, Y) · mom_y K`), and each `∫_x ∂ᵧⁱ f (x, my)` is again a Taylor cell in `x`.
Cells are chained with `integral_add_adjacent_intervals` in both variables.

* `integral2_mem_t2Cell` : one cell.
* `integral2_mem_taylor2` : the grid rule, against the Mathlib iterated integral.
* `integral_rect_mem_taylor2` : the same for the Bochner integral over the rectangle (Fubini).
-/
import RealFPMathlib.KQuad
import RealFPMathlib.Quad2

open Interval64 Interval64.Quad Interval64.KF Set intervalIntegral MeasureTheory Finset

noncomputable section

namespace RealFP.Taylor2

open RealFP RealFP.Quad RealFP.Taylor

theorem fle_real {a b : Float} (ha : finite a = true) (hb : finite b = true) (h : a ≤ b) :
    a.toReal ≤ b.toReal := by
  obtain ⟨ha1, ha2⟩ := finite_spec ha
  obtain ⟨hb1, hb2⟩ := finite_spec hb
  have := (float_le_iff_toE ha1 hb1).1 h
  rw [RealFP.Poly.toE_eq_toReal ha1 ha2, RealFP.Poly.toE_eq_toReal hb1 hb2] at this
  exact EReal.coe_le_coe_iff.1 this

theorem cellOKF_spec {c : Float × Float × Float} (h : cellOKF c = true) :
    finite c.1 = true ∧ finite c.2.1 = true ∧ finite c.2.2 = true ∧
      c.1.toReal ≤ c.2.1.toReal ∧ c.2.1.toReal ≤ c.2.2.toReal := by
  simp only [cellOKF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fle_real h1 h2 h4, fle_real h2 h3 h5⟩

theorem toReal_of_bits {a b : Float} (h : (a.toBits == b.toBits) = true) : a.toReal = b.toReal := by
  have : a.toBits = b.toBits := by simpa using h
  unfold Float.toReal; rw [this]

theorem ptF_mem {x : Float} (h : finite x = true) : x.toReal ∈ KQ.ptF x := toReal_mem h

theorem mom_mem_momF {lo m hi : Float} (hl : finite lo = true) (hm : finite m = true)
    (hh : finite hi = true) (j : ℕ) :
    mom lo.toReal m.toReal hi.toReal j ∈ KQ.momF lo m hi j := by
  unfold mom KQ.momF
  have hq := mem_toSet_ofRat (1 / (KQ.fact (j + 1) : ℚ))
  have e : ((1 / (KQ.fact (j + 1) : ℚ) : ℚ) : ℝ) = 1 / ((j + 1).factorial : ℝ) := by
    rw [RealFP.KQ.fact_eq]; push_cast; ring
  rw [e] at hq
  exact Iv.mem_mul (Iv.sub_mem (mem_pown (Iv.sub_mem (ptF_mem hh) (ptF_mem hm)) _)
    (mem_pown (Iv.sub_mem (ptF_mem hl) (ptF_mem hm)) _)) hq

theorem sum_mem_sumI {a : ℕ → ℝ} {A : ℕ → Interval64} :
    ∀ n, (∀ j < n, a j ∈ A j) → ∑ j ∈ range n, a j ∈ sumI A n
  | 0, _ => by simp only [range_zero, sum_empty]; exact zero_mem_zeroI
  | n + 1, h => by
    rw [sum_range_succ]
    exact Iv.add_mem (sum_mem_sumI n fun j hj => h j (by omega)) (h n (by omega))

/-! ### Derivative chains -/

theorem hasDerivAt_y {e : IExpr} {j : ℕ} {x t : ℝ} (hD : Dom [x, t] (dIt 1 j e)) :
    HasDerivAt (fun y => (dIt 1 j e).denote [x, y]) ((dIt 1 (j + 1) e).denote [x, t]) t := by
  have := hasDerivAt_denote (xs := [x, t]) (i := 1) (by simp) (dIt 1 j e) hD
  show HasDerivAt _ (((dIt 1 j e).deriv 1).denote [x, t]) t
  rw [denote_deriv]; simpa using this

theorem hasDerivAt_x {e : IExpr} {i j : ℕ} {t y : ℝ} (hD : Dom [t, y] (dxy e i j)) :
    HasDerivAt (fun x => (dxy e i j).denote [x, y]) ((dxy e i (j + 1)).denote [t, y]) t := by
  have := hasDerivAt_denote (xs := [t, y]) (i := 0) (by simp) (dxy e i j) hD
  show HasDerivAt _ (((dxy e i j).deriv 0).denote [t, y]) t
  rw [denote_deriv]; simpa using this

theorem env2 {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    List.Forall₂ (fun (r : ℝ) (I : Interval64) => r ∈ I.toSet) [x, y] [X, Y] :=
  List.Forall₂.cons hx (List.Forall₂.cons hy List.Forall₂.nil)

/-! ### One cell -/

theorem integral2_mem_t2Cell (e : IExpr) {K : ℕ} (hK : Even K) (hK0 : 0 < K)
    {cx cy : Float × Float × Float} (hx : cellOKF cx = true) (hy : cellOKF cy = true)
    (hdom : ∀ i ≤ K, ∀ j ≤ K, ∀ x ∈ Icc cx.1.toReal cx.2.2.toReal,
      ∀ y ∈ Icc cy.1.toReal cy.2.2.toReal, Dom [x, y] (dxy e i j))
    (hc : ContinuousOn (fun p : ℝ × ℝ => e.denote [p.1, p.2])
      (Icc cx.1.toReal cx.2.2.toReal ×ˢ Icc cy.1.toReal cy.2.2.toReal)) :
    (∫ x in cx.1.toReal..cx.2.2.toReal, ∫ y in cy.1.toReal..cy.2.2.toReal, e.denote [x, y]) ∈
      t2Cell e K cx cy := by
  obtain ⟨fxl, fxm, fxh, ox1, ox2⟩ := cellOKF_spec hx
  obtain ⟨fyl, fym, fyh, oy1, oy2⟩ := cellOKF_spec hy
  set XL := cx.1.toReal; set XM := cx.2.1.toReal; set XH := cx.2.2.toReal
  set YL := cy.1.toReal; set YM := cy.2.1.toReal; set YH := cy.2.2.toReal
  have hxle : XL ≤ XH := ox1.trans ox2
  have hyle : YL ≤ YH := oy1.trans oy2
  have hYM : YM ∈ Icc YL YH := ⟨oy1, oy2⟩
  have hXM : XM ∈ Icc XL XH := ⟨ox1, ox2⟩
  set DC := evalI [⟨cx.1, cx.2.2⟩, ⟨cy.1, cy.2.2⟩] (dxy e K 0)
  set Qy := KQ.momF cy.1 cy.2.1 cy.2.2
  -- Taylor in `y` for each `x`
  set S : ℝ → ℝ := fun x => ∑ i ∈ range K, mom YL YM YH i * (dIt 1 i e).denote [x, YM]
  set r : ℝ → ℝ := fun x => (∫ y in YL..YH, e.denote [x, y]) - S x
  have hr : ∀ x ∈ Icc XL XH, r x ∈ DC * Qy K := by
    intro x hxI
    obtain ⟨r0, hr0, heq⟩ := integral_mem_taylorCell (F := fun i y => (dIt 1 i e).denote [x, y])
      hK hK0 oy1 oy2 (fun j hj t ht => hasDerivAt_y (hdom j hj.le 0 (Nat.zero_le _) x hxI t ht))
      (D := DC) (fun t ht => eval_sound (env2 (mem_box fxl fxh hxI) (mem_box fyl fyh ht)) _)
      (mom_mem_momF fyl fym fyh K)
    have : r x = r0 := by
      simp only [r, S]
      change (∫ y in YL..YH, (dIt 1 0 e).denote [x, y]) - _ = r0
      rw [heq]
      have : ∑ i ∈ range K, mom YL YM YH i * (dIt 1 i e).denote [x, YM] =
          ∑ j ∈ range K, (dIt 1 j e).denote [x, YM] * mom YL YM YH j :=
        sum_congr rfl fun _ _ => mul_comm _ _
      rw [this]; ring
    rw [this]; exact hr0
  -- continuity
  have hcS1 : ∀ i < K + 1, ContinuousOn (fun x => (dIt 1 i e).denote [x, YM]) (Icc XL XH) :=
    fun i hi x hxI => (hasDerivAt_x (i := i) (j := 0)
      (hdom i (by omega) 0 (Nat.zero_le _) x hxI YM hYM)).continuousAt.continuousWithinAt
  have hcS : ContinuousOn S (Icc XL XH) :=
    continuousOn_finsetSum _ fun i hi =>
      continuousOn_const.mul (hcS1 i (by simp at hi; omega))
  have hcI : ContinuousOn (fun x => ∫ y in YL..YH, e.denote [x, y]) (Icc XL XH) := by
    have := RealFP.Quad2.continuousOn_inner (f := fun x y => e.denote [x, y]) (a := XL) (b := XH) (c := YL)
      (d := YH) (by rw [uIcc_of_le hxle, uIcc_of_le hyle]; exact hc)
    rwa [uIcc_of_le hxle] at this
  have hcr : ContinuousOn r (Icc XL XH) := hcI.sub hcS
  -- split
  have hsplit : (∫ x in XL..XH, ∫ y in YL..YH, e.denote [x, y]) =
      (∫ x in XL..XH, S x) + ∫ x in XL..XH, r x := by
    rw [← intervalIntegral.integral_add (hcS.intervalIntegrable_of_Icc hxle)
      (hcr.intervalIntegrable_of_Icc hxle)]
    congr 1; funext x; simp only [r]; ring
  have hS : (∫ x in XL..XH, S x) =
      ∑ i ∈ range K, mom YL YM YH i * ∫ x in XL..XH, (dIt 1 i e).denote [x, YM] := by
    have h := intervalIntegral.integral_finsetSum (μ := volume) (a := XL) (b := XH) (s := range K)
      (f := fun i x => mom YL YM YH i * (dIt 1 i e).denote [x, YM]) fun i hi =>
      (continuousOn_const.mul (hcS1 i (by simp at hi; omega))).intervalIntegrable_of_Icc hxle
    simp only [S]; rw [h]
    exact sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  rw [hsplit, hS]
  refine Iv.add_mem (sum_mem_sumI K fun i hi => Iv.mem_mul (mom_mem_momF fyl fym fyh i) ?_) ?_
  · -- Taylor in `x`
    obtain ⟨r1, hr1, heq⟩ := integral_mem_taylorCell (F := fun j x => (dxy e i j).denote [x, YM])
      hK hK0 ox1 ox2 (fun j hj t ht => hasDerivAt_x (hdom i hi.le j hj.le t ht YM hYM))
      (D := evalI [⟨cx.1, cx.2.2⟩, KQ.ptF cy.2.1] (dxy e i K))
      (fun t ht => eval_sound (env2 (mem_box fxl fxh ht) (ptF_mem fym)) _)
      (mom_mem_momF fxl fxm fxh K)
    change (∫ x in XL..XH, (dxy e i 0).denote [x, YM]) ∈ _
    rw [heq]
    exact Iv.add_mem (sum_mem_sumI K fun j hj => Iv.mem_mul
      (eval_sound (env2 (ptF_mem fxm) (ptF_mem fym)) _) (mom_mem_momF fxl fxm fxh j)) hr1
  · have := RealFP.Quad2.integral_mem_cell0' (f := r) (F := fun _ => DC * Qy K) hr fxl fxh hxle hcr
    exact this

/-! ### Chains of cells -/

/-- Splitting `∫_a^b` along a chain of cells (equality). -/
theorem chain_eq {φ : ℝ → ℝ} {A0 : ℝ} {b : Float} :
    ∀ (cs : List (Float × Float × Float)) (a : Float), A0 ≤ a.toReal → chainF a b cs = true →
      cs.all cellOKF = true →
      (∀ c ∈ cs, A0 ≤ c.1.toReal → c.2.2.toReal ≤ b.toReal →
        IntervalIntegrable φ volume c.1.toReal c.2.2.toReal) →
      IntervalIntegrable φ volume a.toReal b.toReal ∧ a.toReal ≤ b.toReal ∧
        (∫ x in a.toReal..b.toReal, φ x) =
          (cs.map fun c => ∫ x in c.1.toReal..c.2.2.toReal, φ x).sum
  | [], a, _, hch, _, _ => by
    have h := toReal_of_bits (by simpa [chainF] using hch)
    rw [h]; exact ⟨IntervalIntegrable.refl, le_rfl, by simp⟩
  | c :: cs, a, hA, hch, hall, hint => by
    simp only [chainF, Bool.and_eq_true] at hch
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have ha := toReal_of_bits hch.1
    obtain ⟨-, -, -, o1, o2⟩ := cellOKF_spec hall.1
    have rest := chain_eq cs c.2.2 (by linarith) hch.2 hall.2
      fun c' hc' => hint c' (List.mem_cons_of_mem _ hc')
    have hi := hint c List.mem_cons_self (by linarith) rest.2.1
    rw [ha]
    refine ⟨hi.trans rest.1, o1.trans (o2.trans rest.2.1), ?_⟩
    rw [← integral_add_adjacent_intervals hi rest.1, rest.2.2]
    simp

theorem chain_bounds {A0 : ℝ} {b : Float} :
    ∀ (cs : List (Float × Float × Float)) (a : Float), A0 ≤ a.toReal → chainF a b cs = true →
      cs.all cellOKF = true → ∀ c ∈ cs, A0 ≤ c.1.toReal ∧ c.2.2.toReal ≤ b.toReal
  | [], _, _, _, _ => by simp
  | c :: cs, a, hA, hch, hall => by
    simp only [chainF, Bool.and_eq_true] at hch
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have ha := toReal_of_bits hch.1
    obtain ⟨-, -, -, o1, o2⟩ := cellOKF_spec hall.1
    have rest := chain_bounds (A0 := A0) cs c.2.2 (by linarith) hch.2 hall.2
    have hle := (chain_eq (φ := fun _ => (0 : ℝ)) cs c.2.2 (A0 := c.2.2.toReal) le_rfl hch.2 hall.2
      fun _ _ _ _ => intervalIntegrable_const).2.1
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | h
    · exact ⟨by linarith, hle⟩
    · exact rest c' h

theorem sum_mem_foldr {α : Type} {g : α → ℝ} {I : α → Interval64} :
    ∀ L : List α, (∀ c ∈ L, g c ∈ I c) → (L.map g).sum ∈ L.foldr (fun c acc => I c + acc) zeroI
  | [], _ => by simpa using zero_mem_zeroI
  | c :: L, h => by
    simp only [List.map_cons, List.sum_cons, List.foldr_cons]
    exact Iv.add_mem (h c List.mem_cons_self)
      (sum_mem_foldr L fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem integral_list_sum {α : Type} {f : α → ℝ → ℝ} {lo hi : ℝ} :
    ∀ L : List α, (∀ c ∈ L, IntervalIntegrable (f c) volume lo hi) →
      IntervalIntegrable (fun x => (L.map fun c => f c x).sum) volume lo hi ∧
        (∫ x in lo..hi, (L.map fun c => f c x).sum) = (L.map fun c => ∫ x in lo..hi, f c x).sum
  | [], _ => by simp
  | c :: L, h => by
    have ih := integral_list_sum L fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have hc := h c List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hc.add ih.1, by rw [intervalIntegral.integral_add hc ih.1, ih.2]⟩

/-! ### The grid rule -/

/-- **Soundness of `taylor2`** (iterated integral). `Dom` of all `∂ₓʲ ∂ᵧⁱ e` (`i, j ≤ K`) and
    continuity of `e` on the rectangle. -/
theorem integral2_mem_taylor2 (e : IExpr) (K : ℕ) {a b c d : Float}
    (xs ys : List (Float × Float × Float))
    (hdom : ∀ i ≤ K, ∀ j ≤ K, ∀ x ∈ Icc a.toReal b.toReal, ∀ y ∈ Icc c.toReal d.toReal,
      Dom [x, y] (dxy e i j))
    (hc : ContinuousOn (fun p : ℝ × ℝ => e.denote [p.1, p.2])
      (Icc a.toReal b.toReal ×ˢ Icc c.toReal d.toReal)) :
    (∫ x in a.toReal..b.toReal, ∫ y in c.toReal..d.toReal, e.denote [x, y]) ∈
      taylor2 e K a b c d xs ys := by
  unfold taylor2
  split
  case isFalse => exact mem_toSet_whole _
  rename_i hok
  simp only [t2OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hK2, hK0⟩, hchx⟩, hchy⟩, hallx⟩, hally⟩ := hok
  have hK : Even K := Nat.even_iff.2 hK2
  set A := a.toReal; set B := b.toReal; set C := c.toReal; set D := d.toReal
  -- `y`-integrability on sub-intervals, for each `x ∈ [A, B]`
  have hcy : ∀ x ∈ Icc A B, ContinuousOn (fun y => e.denote [x, y]) (Icc C D) := fun x hx =>
    hc.comp (continuousOn_const.prodMk continuousOn_id) fun y hy => ⟨hx, hy⟩
  have chy : ∀ x ∈ Icc A B, _ := fun x hx => chain_eq (φ := fun y => e.denote [x, y]) (A0 := C)
    ys c le_rfl hchy hally fun cy _ h1 h2 => by
      obtain ⟨-, -, -, o1, o2⟩ := cellOKF_spec (List.all_eq_true.1 hally cy ‹_›)
      exact ((hcy x hx).mono (Icc_subset_Icc h1 h2)).intervalIntegrable_of_Icc (o1.trans o2)
  have hAB : A ≤ B := (chain_eq (φ := fun _ => (0 : ℝ)) (A0 := A) xs a le_rfl hchx hallx
    fun _ _ _ _ => intervalIntegrable_const).2.1
  have hinner : ∀ lo hi lo' hi' : ℝ, A ≤ lo → hi ≤ B → lo ≤ hi → C ≤ lo' → hi' ≤ D → lo' ≤ hi' →
      ContinuousOn (fun x => ∫ y in lo'..hi', e.denote [x, y]) (Icc lo hi) := by
    intro lo hi lo' hi' h1 h2 h3 h4 h5 h6
    have := RealFP.Quad2.continuousOn_inner (f := fun x y => e.denote [x, y]) (a := lo) (b := hi)
      (c := lo') (d := hi') (by
        rw [uIcc_of_le h3, uIcc_of_le h6]
        exact hc.mono (prod_mono (Icc_subset_Icc h1 h2) (Icc_subset_Icc h4 h5)))
    rwa [uIcc_of_le h3] at this
  have hCD : C ≤ D := (chain_eq (φ := fun _ => (0 : ℝ)) (A0 := C) ys c le_rfl hchy hally
    fun _ _ _ _ => intervalIntegrable_const).2.1
  have chx := chain_eq (φ := fun x => ∫ y in C..D, e.denote [x, y]) (A0 := A) xs a le_rfl hchx hallx
    fun cx hcx h1 h2 => by
      obtain ⟨-, -, -, o1, o2⟩ := cellOKF_spec (List.all_eq_true.1 hallx cx hcx)
      exact (hinner _ _ _ _ h1 h2 (o1.trans o2) le_rfl le_rfl hCD).intervalIntegrable_of_Icc
        (o1.trans o2)
  rw [chx.2.2]
  refine sum_mem_foldr (I := fun cx => ys.foldr (fun cy acc' => t2Cell e K cx cy + acc') zeroI)
    xs fun cx hcx => ?_
  obtain ⟨bx1, bx2⟩ := chain_bounds xs a le_rfl hchx hallx cx hcx
  have okx := List.all_eq_true.1 hallx cx hcx
  obtain ⟨-, -, -, ox1, ox2⟩ := cellOKF_spec okx
  have e1 : (∫ x in cx.1.toReal..cx.2.2.toReal, ∫ y in C..D, e.denote [x, y]) =
      ∫ x in cx.1.toReal..cx.2.2.toReal,
        (ys.map fun cy => ∫ y in cy.1.toReal..cy.2.2.toReal, e.denote [x, y]).sum := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (ox1.trans ox2)] at hx
    exact (chy x ⟨bx1.trans hx.1, hx.2.trans bx2⟩).2.2
  have e2 := integral_list_sum (f := fun cy x => ∫ y in cy.1.toReal..cy.2.2.toReal, e.denote [x, y])
    (lo := cx.1.toReal) (hi := cx.2.2.toReal) ys fun cy hcy => by
      obtain ⟨by1, by2⟩ := chain_bounds ys c le_rfl hchy hally cy hcy
      obtain ⟨-, -, -, oy1, oy2⟩ := cellOKF_spec (List.all_eq_true.1 hally cy hcy)
      exact (hinner _ _ _ _ bx1 bx2 (ox1.trans ox2) by1 by2 (oy1.trans oy2)).intervalIntegrable_of_Icc
        (ox1.trans ox2)
  rw [e1, e2.2]
  refine sum_mem_foldr ys fun cy hcy => ?_
  obtain ⟨by1, by2⟩ := chain_bounds ys c le_rfl hchy hally cy hcy
  have oky := List.all_eq_true.1 hally cy hcy
  refine integral2_mem_t2Cell e hK hK0 okx oky
    (fun i hi j hj x hx y hy => hdom i hi j hj x ⟨bx1.trans hx.1, hx.2.trans bx2⟩ y
      ⟨by1.trans hy.1, hy.2.trans by2⟩)
    (hc.mono (prod_mono (Icc_subset_Icc bx1 bx2) (Icc_subset_Icc by1 by2)))

/-- **Fubini form**: the Bochner integral over the rectangle `[a, b] × [c, d]`. -/
theorem integral_rect_mem_taylor2 (e : IExpr) (K : ℕ) {a b c d : Float}
    (xs ys : List (Float × Float × Float)) (hab : a.toReal ≤ b.toReal) (hcd : c.toReal ≤ d.toReal)
    (hdom : ∀ i ≤ K, ∀ j ≤ K, ∀ x ∈ Icc a.toReal b.toReal, ∀ y ∈ Icc c.toReal d.toReal,
      Dom [x, y] (dxy e i j))
    (hc : ContinuousOn (fun p : ℝ × ℝ => e.denote [p.1, p.2])
      (Icc a.toReal b.toReal ×ˢ Icc c.toReal d.toReal)) :
    (∫ p in Icc a.toReal b.toReal ×ˢ Icc c.toReal d.toReal, e.denote [p.1, p.2]) ∈
      taylor2 e K a b c d xs ys := by
  rw [RealFP.Quad2.setIntegral_rect_eq (f := fun x y => e.denote [x, y]) hab hcd hc]
  exact integral2_mem_taylor2 e K xs ys hdom hc

/-! ### Structurally smooth integrands -/

theorem dom_of_smoothB {xs : List ℝ} : ∀ e : IExpr, smoothB e = true → Dom xs e := by
  intro e; induction e <;> simp_all [smoothB, Dom]

theorem continuous_of_smoothB :
    ∀ e : IExpr, smoothB e = true → Continuous (fun p : ℝ × ℝ => e.denote [p.1, p.2]) := by
  intro e; induction e with
  | var i =>
    intro _; rcases i with _ | _ | i
    · exact continuous_fst
    · exact continuous_snd
    · simpa [IExpr.denote] using continuous_const
  | rat q => intro _; exact continuous_const
  | add a b iha ihb =>
    intro h; simp only [smoothB, Bool.and_eq_true] at h; exact (iha h.1).add (ihb h.2)
  | sub a b iha ihb =>
    intro h; simp only [smoothB, Bool.and_eq_true] at h; exact (iha h.1).sub (ihb h.2)
  | mul a b iha ihb =>
    intro h; simp only [smoothB, Bool.and_eq_true] at h; exact (iha h.1).mul (ihb h.2)
  | neg a ih => intro h; exact (ih h).neg
  | pow a n ih => intro h; exact (ih h).pow n
  | exp a ih => intro h; exact Real.continuous_exp.comp (ih h)
  | sin a ih => intro h; exact Real.continuous_sin.comp (ih h)
  | cos a ih => intro h; exact Real.continuous_cos.comp (ih h)
  | pi => intro _; exact continuous_const
  | atan a ih => intro h; exact Real.continuous_arctan.comp (ih h)
  | sinh a ih => intro h; exact Real.continuous_sinh.comp (ih h)
  | cosh a ih => intro h; exact Real.continuous_cosh.comp (ih h)
  | _ => intro h; simp [smoothB] at h

theorem allSmooth_spec {e : IExpr} {K : ℕ} (h : allSmooth e K = true) :
    ∀ i ≤ K, ∀ j ≤ K, smoothB (dxy e i j) = true := by
  intro i hi j hj
  simp only [allSmooth, List.all_eq_true, List.mem_range] at h
  exact h i (by omega) j (by omega)

/-- `taylor2` for a structurally smooth integrand: the side conditions reduce to
    `allSmooth e K = true` (by `decide +kernel`). -/
theorem integral2_mem_taylor2_smooth (e : IExpr) (K : ℕ) {a b c d : Float}
    (xs ys : List (Float × Float × Float)) (h : allSmooth e K = true) :
    (∫ x in a.toReal..b.toReal, ∫ y in c.toReal..d.toReal, e.denote [x, y]) ∈
      taylor2 e K a b c d xs ys := by
  have h0 : smoothB e = true := allSmooth_spec h 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  exact integral2_mem_taylor2 e K xs ys
    (fun i hi j hj _ _ _ _ => dom_of_smoothB _ (allSmooth_spec h i hi j hj))
    (continuous_of_smoothB e h0).continuousOn

end RealFP.Taylor2