/-
`Interval64.mul` / `Interval64.div` / `Interval64.sqrt` enclosures with no
finiteness assumption on the endpoints (half-lines and `whole` allowed):

* `mem_toSet_mul : x ∈ X → y ∈ Y → x * y ∈ X * Y`
* `mem_toSet_div : x ∈ X → y ∈ Y → y ≠ 0 → x / y ∈ X / Y`
* `mem_toSet_sqrt : x ∈ X → 0 ≤ x → √x ∈ sqrt X`

They supersede `mul_mem_toSet` / `div_mem_toSet` / `sqrt_mem_toSet` (in `Mem`,
now deprecated), which needed all four endpoints finite.
-/
import RealFPMathlib.Corners
import RealFPMathlib.Tight

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.FloatBits

noncomputable section

namespace RealFP

theorem skip_iff {x y : Float} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    ((x == 0 && y.isInf) || (y == 0 && x.isInf)) = true ↔ SkipMul x.toE y.toE := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_zero_iff_toE hx, beq_zero_iff_toE hy,
    isInf_iff_toE, hx, hy, and_true, SkipMul]

/-- Invariant of the corner accumulator: once a corner is taken, both ends are not NaN. -/
def AccInv (r : Float × Float × Bool) : Prop :=
  r.2.2 = true → r.1.isNaN = false ∧ r.2.1.isNaN = false

theorem acc_step {x y lo hi : Float} {got : Bool} (hinv : AccInv (lo, hi, got))
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    let r := accCorner x y lo hi got
    AccInv r ∧ (got = true → r.2.2 = true) ∧
    (∀ z : EReal, got = true → lo.toE ≤ z → r.1.toE ≤ z) ∧
    (∀ z : EReal, got = true → z ≤ hi.toE → z ≤ r.2.1.toE) ∧
    (¬ SkipMul x.toE y.toE → r.2.2 = true ∧ r.1.toE ≤ x.toE * y.toE ∧
        x.toE * y.toE ≤ r.2.1.toE) ∧
    (SkipMul x.toE y.toE → r = (lo, hi, got)) := by
  intro r
  by_cases hs : SkipMul x.toE y.toE
  · have hr : r = (lo, hi, got) := by
      simp only [r, accCorner, (skip_iff hx hy).2 hs, ↓reduceIte]
    rw [hr]
    exact ⟨hinv, id, fun _ _ h => h, fun _ _ h => h, fun h => absurd hs h, fun _ => rfl⟩
  obtain ⟨⟨hdn, hd⟩, ⟨hun, hu⟩⟩ := corner_mul hx hy hs
  have hsk : ((x == 0 && y.isInf) || (y == 0 && x.isInf)) = false := by
    cases h : ((x == 0 && y.isInf) || (y == 0 && x.isInf))
    · rfl
    · exact absurd ((skip_iff hx hy).1 h) hs
  cases got with
  | false =>
    have hr : r = (Directed.mulDown x y, Directed.mulUp x y, true) := by
      simp only [r, accCorner, hsk, hdn, hun, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false]
    rw [hr]
    refine ⟨fun _ => ⟨hdn, hun⟩, fun h => absurd h (by simp), fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp), fun _ => ⟨rfl, hd, hu⟩, fun h => absurd h hs⟩
  | true =>
    obtain ⟨hln, hhn⟩ := hinv rfl
    have hr : r = (fmin (Directed.mulDown x y) lo, fmax (Directed.mulUp x y) hi, true) := by
      simp only [r, accCorner, hsk, hdn, hun, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        Bool.not_true, fmin, fmax]
    rw [hr]
    have e1 := toE_fmin hdn hln
    have e2 := toE_fmax hun hhn
    refine ⟨fun _ => ⟨fmin_isNaN hdn hln, fmax_isNaN hun hhn⟩, fun _ => rfl, ?_, ?_, ?_,
      fun h => absurd h hs⟩
    · intro z _ h; rw [e1]; exact le_trans (min_le_right _ _) h
    · intro z _ h; rw [e2]; exact le_trans h (le_max_right _ _)
    · intro _
      exact ⟨rfl, by rw [e1]; exact le_trans (min_le_left _ _) hd,
        by rw [e2]; exact le_trans hu (le_max_left _ _)⟩

/-- The whole line contains every real. -/
theorem mem_toSet_whole (x : ℝ) : x ∈ whole.toSet := by
  refine ⟨?_, ?_⟩
  · rw [show bitsToEVal whole.lo.toBits = some .negInf by decide +kernel]; trivial
  · rw [show bitsToEVal whole.hi.toBits = some .posInf by decide +kernel]; trivial

/-- `x * y ∈ X * Y` for every `x ∈ X`, `y ∈ Y`, with no finiteness assumption. -/
theorem mem_toSet_mul {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    x * y ∈ (X * Y).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan X Y = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  change x * y ∈ (Interval64.mul X Y).toSet
  unfold Interval64.mul
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  have inv0 : AccInv ((0 : Float), (0 : Float), false) := fun h => absurd h (by simp)
  obtain ⟨i1, g1, l1, u1, c1, s1⟩ := acc_step inv0 hXl hYl
  generalize hr1 : accCorner X.lo Y.lo 0 0 false = r1 at i1 g1 l1 u1 c1 s1
  obtain ⟨lo1, hi1, got1⟩ := r1
  obtain ⟨i2, g2, l2, u2, c2, s2⟩ := acc_step i1 hXl hYh
  generalize hr2 : accCorner X.lo Y.hi lo1 hi1 got1 = r2 at i2 g2 l2 u2 c2 s2
  obtain ⟨lo2, hi2, got2⟩ := r2
  obtain ⟨i3, g3, l3, u3, c3, s3⟩ := acc_step i2 hXh hYl
  generalize hr3 : accCorner X.hi Y.lo lo2 hi2 got2 = r3 at i3 g3 l3 u3 c3 s3
  obtain ⟨lo3, hi3, got3⟩ := r3
  obtain ⟨i4, g4, l4, u4, c4, s4⟩ := acc_step i3 hXh hYh
  generalize hr4 : accCorner X.hi Y.hi lo3 hi3 got3 = r4 at i4 g4 l4 u4 c4 s4
  obtain ⟨lo4, hi4, got4⟩ := r4
  simp only
  cases hg : got4 with
  | false => exact mem_toSet_whole _
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only at i1 g1 l1 u1 c1 s1 i2 g2 l2 u2 c2 s2 i3 g3 l3 u3 c3 s3 i4 g4 l4 u4 c4 s4
  obtain ⟨hn4l, hn4h⟩ := i4 hg
  have hxy : ((x * y : ℝ) : EReal) = ((x * y : ℝ) : EReal) := rfl
  refine mem_toSet_of_toE hn4l hn4h ?_ ?_
  · rcases mul_corner_lo hXl' hXh' hYl' hYh' with ⟨k1, k2, k3, k4⟩ | ⟨k, kb⟩ | ⟨k, kb⟩ | ⟨k, kb⟩ |
        ⟨k, kb⟩
    · have e1 := s1 k1; have e2 := s2 k2; have e3 := s3 k3; have e4 := s4 k4
      simp only [Prod.mk.injEq] at e1 e2 e3 e4
      rw [e4.2.2, e3.2.2, e2.2.2, e1.2.2] at hg; exact absurd hg (by simp)
    · obtain ⟨t1, b1, -⟩ := c1 k
      exact l4 _ (g3 (g2 t1)) (l3 _ (g2 t1) (l2 _ t1 (le_trans b1 kb)))
    · obtain ⟨t2, b2, -⟩ := c2 k
      exact l4 _ (g3 t2) (l3 _ t2 (le_trans b2 kb))
    · obtain ⟨t3, b3, -⟩ := c3 k
      exact l4 _ t3 (le_trans b3 kb)
    · obtain ⟨-, b4, -⟩ := c4 k
      exact le_trans b4 kb
  · rcases mul_corner_hi hXl' hXh' hYl' hYh' with ⟨k1, k2, k3, k4⟩ | ⟨k, kb⟩ | ⟨k, kb⟩ | ⟨k, kb⟩ |
        ⟨k, kb⟩
    · have e1 := s1 k1; have e2 := s2 k2; have e3 := s3 k3; have e4 := s4 k4
      simp only [Prod.mk.injEq] at e1 e2 e3 e4
      rw [e4.2.2, e3.2.2, e2.2.2, e1.2.2] at hg; exact absurd hg (by simp)
    · obtain ⟨t1, -, b1⟩ := c1 k
      exact u4 _ (g3 (g2 t1)) (u3 _ (g2 t1) (u2 _ t1 (le_trans kb b1)))
    · obtain ⟨t2, -, b2⟩ := c2 k
      exact u4 _ (g3 t2) (u3 _ t2 (le_trans kb b2))
    · obtain ⟨t3, -, b3⟩ := c3 k
      exact u4 _ t3 (le_trans kb b3)
    · obtain ⟨-, -, b4⟩ := c4 k
      exact le_trans kb b4

/-! ### Division -/

theorem containsZero_iff_toE {Y : Interval64} (hl : Y.lo.isNaN = false) (hh : Y.hi.isNaN = false) :
    containsZero Y = true ↔ Y.lo.toE ≤ 0 ∧ 0 ≤ Y.hi.toE := by
  simp only [containsZero, isInvalid, hl, hh, Bool.or_self, Bool.not_false, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq, le_zero_iff_toE hl, zero_le_iff_toE hh]

theorem float_lt_nan_left {a b : Float} (ha : a.isNaN = true) : ¬ a < b := by
  intro h
  rw [Interval64Proofs.IntervalMem.float_lt_iff] at h
  rw [float_isNaN] at ha
  revert h ha
  cases unpackBits a.toBits <;> cases unpackBits b.toBits <;>
    simp [Float.Model.UnpackedFloat.isNaN, Float.Model.UnpackedFloat.lt,
      Float.Model.UnpackedFloat.compare]

theorem float_lt_nan_right {a b : Float} (hb : b.isNaN = true) : ¬ a < b := by
  intro h
  rw [Interval64Proofs.IntervalMem.float_lt_iff] at h
  rw [float_isNaN] at hb
  revert h hb
  cases unpackBits a.toBits <;> cases unpackBits b.toBits <;>
    simp [Float.Model.UnpackedFloat.isNaN, Float.Model.UnpackedFloat.lt,
      Float.Model.UnpackedFloat.compare]

/-- If `fmin a b` is not NaN, then `b` is not NaN. -/
theorem fmin_nan_right {a b : Float} (h : (fmin a b).isNaN = false) : b.isNaN = false := by
  cases hb : b.isNaN
  · rfl
  · unfold fmin at h
    rw [ite_eq_right (by simpa using float_lt_nan_right (a := a) hb)] at h
    rw [hb] at h; exact h

theorem fmax_nan_right {a b : Float} (h : (fmax a b).isNaN = false) : b.isNaN = false := by
  cases hb : b.isNaN
  · rfl
  · unfold fmax at h
    rw [ite_eq_right (by simpa using float_lt_nan_left (b := a) hb)] at h
    rw [hb] at h; exact h

/-- A lower bound `z` carried by either argument survives `fmin` (when it is not NaN). -/
theorem fmin_le_of {a b : Float} {z : EReal} (h : (fmin a b).isNaN = false)
    (hab : (a.isNaN = false ∧ a.toE ≤ z) ∨ (b.isNaN = false ∧ b.toE ≤ z)) :
    (fmin a b).toE ≤ z := by
  have hb := fmin_nan_right h
  cases ha : a.isNaN
  · rw [toE_fmin ha hb]
    rcases hab with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact le_trans (min_le_left _ _) h'
    · exact le_trans (min_le_right _ _) h'
  · have : fmin a b = b := by
      unfold fmin; rw [ite_eq_right (by simpa using float_lt_nan_left (b := b) ha)]
    rw [this]
    rcases hab with ⟨h', -⟩ | ⟨-, h'⟩
    · rw [ha] at h'; exact absurd h' (by simp)
    · exact h'

theorem le_fmax_of {a b : Float} {z : EReal} (h : (fmax a b).isNaN = false)
    (hab : (a.isNaN = false ∧ z ≤ a.toE) ∨ (b.isNaN = false ∧ z ≤ b.toE)) :
    z ≤ (fmax a b).toE := by
  have hb := fmax_nan_right h
  cases ha : a.isNaN
  · rw [toE_fmax ha hb]
    rcases hab with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact le_trans h' (le_max_left _ _)
    · exact le_trans h' (le_max_right _ _)
  · have : fmax a b = b := by
      unfold fmax; rw [ite_eq_right (by simpa using float_lt_nan_right (a := b) ha)]
    rw [this]
    rcases hab with ⟨h', -⟩ | ⟨-, h'⟩
    · rw [ha] at h'; exact absurd h' (by simp)
    · exact h'

theorem fminN_le_of {a b : Float} {z : EReal}
    (hab : (a.isNaN = false ∧ a.toE ≤ z) ∨ (b.isNaN = false ∧ b.toE ≤ z)) :
    (fminN a b).isNaN = false ∧ (fminN a b).toE ≤ z := by
  unfold fminN
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨fmin_isNaN ha hb, fmin_le_of (fmin_isNaN ha hb) hab⟩
  · rcases hab with h | h
    · exact h
    · rw [hb] at h; exact absurd h.1 (by simp)
  · rcases hab with h | h
    · rw [ha] at h; exact absurd h.1 (by simp)
    · exact h
  · rcases hab with h | h
    · rw [ha] at h; exact absurd h.1 (by simp)
    · rw [hb] at h; exact absurd h.1 (by simp)

theorem le_fmaxN_of {a b : Float} {z : EReal}
    (hab : (a.isNaN = false ∧ z ≤ a.toE) ∨ (b.isNaN = false ∧ z ≤ b.toE)) :
    (fmaxN a b).isNaN = false ∧ z ≤ (fmaxN a b).toE := by
  unfold fmaxN
  cases ha : a.isNaN <;> cases hb : b.isNaN <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨fmax_isNaN ha hb, le_fmax_of (fmax_isNaN ha hb) hab⟩
  · rcases hab with h | h
    · exact h
    · rw [hb] at h; exact absurd h.1 (by simp)
  · rcases hab with h | h
    · rw [ha] at h; exact absurd h.1 (by simp)
    · exact h
  · rcases hab with h | h
    · rw [ha] at h; exact absurd h.1 (by simp)
    · rw [hb] at h; exact absurd h.1 (by simp)

/-- Lower bound carried by one of four `fmin`-folded values (if the fold is not NaN). -/
theorem fmin4_le {d0 d1 d2 d3 : Float} {z : EReal}
    (h : (fmin d0 (fmin d1 (fmin d2 d3))).isNaN = false)
    (hk : (d0.isNaN = false ∧ d0.toE ≤ z) ∨ (d1.isNaN = false ∧ d1.toE ≤ z) ∨
      (d2.isNaN = false ∧ d2.toE ≤ z) ∨ (d3.isNaN = false ∧ d3.toE ≤ z)) :
    (fmin d0 (fmin d1 (fmin d2 d3))).toE ≤ z := by
  have h1 := fmin_nan_right h
  have h2 := fmin_nan_right h1
  apply fmin_le_of h
  rcases hk with hk | hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr ⟨h1, fmin_le_of h1 (Or.inl hk)⟩
  · exact Or.inr ⟨h1, fmin_le_of h1 (Or.inr ⟨h2, fmin_le_of h2 (Or.inl hk)⟩)⟩
  · exact Or.inr ⟨h1, fmin_le_of h1 (Or.inr ⟨h2, fmin_le_of h2 (Or.inr hk)⟩)⟩

theorem le_fmax4 {d0 d1 d2 d3 : Float} {z : EReal}
    (h : (fmax d0 (fmax d1 (fmax d2 d3))).isNaN = false)
    (hk : (d0.isNaN = false ∧ z ≤ d0.toE) ∨ (d1.isNaN = false ∧ z ≤ d1.toE) ∨
      (d2.isNaN = false ∧ z ≤ d2.toE) ∨ (d3.isNaN = false ∧ z ≤ d3.toE)) :
    z ≤ (fmax d0 (fmax d1 (fmax d2 d3))).toE := by
  have h1 := fmax_nan_right h
  have h2 := fmax_nan_right h1
  apply le_fmax_of h
  rcases hk with hk | hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr ⟨h1, le_fmax_of h1 (Or.inl hk)⟩
  · exact Or.inr ⟨h1, le_fmax_of h1 (Or.inr ⟨h2, le_fmax_of h2 (Or.inl hk)⟩)⟩
  · exact Or.inr ⟨h1, le_fmax_of h1 (Or.inr ⟨h2, le_fmax_of h2 (Or.inr hk)⟩)⟩

theorem fminN4_le {d0 d1 d2 d3 : Float} {z : EReal}
    (hk : (d0.isNaN = false ∧ d0.toE ≤ z) ∨ (d1.isNaN = false ∧ d1.toE ≤ z) ∨
      (d2.isNaN = false ∧ d2.toE ≤ z) ∨ (d3.isNaN = false ∧ d3.toE ≤ z)) :
    (fminN d0 (fminN d1 (fminN d2 d3))).isNaN = false ∧
      (fminN d0 (fminN d1 (fminN d2 d3))).toE ≤ z := by
  apply fminN_le_of
  rcases hk with hk | hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr (fminN_le_of (Or.inl hk))
  · exact Or.inr (fminN_le_of (Or.inr (fminN_le_of (Or.inl hk))))
  · exact Or.inr (fminN_le_of (Or.inr (fminN_le_of (Or.inr hk))))

theorem le_fmaxN4 {d0 d1 d2 d3 : Float} {z : EReal}
    (hk : (d0.isNaN = false ∧ z ≤ d0.toE) ∨ (d1.isNaN = false ∧ z ≤ d1.toE) ∨
      (d2.isNaN = false ∧ z ≤ d2.toE) ∨ (d3.isNaN = false ∧ z ≤ d3.toE)) :
    (fmaxN d0 (fmaxN d1 (fmaxN d2 d3))).isNaN = false ∧
      z ≤ (fmaxN d0 (fmaxN d1 (fmaxN d2 d3))).toE := by
  apply le_fmaxN_of
  rcases hk with hk | hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr (le_fmaxN_of (Or.inl hk))
  · exact Or.inr (le_fmaxN_of (Or.inr (le_fmaxN_of (Or.inl hk))))
  · exact Or.inr (le_fmaxN_of (Or.inr (le_fmaxN_of (Or.inr hk))))

theorem divDown_good {a b : Float} {p : ℝ} (ha : a.isNaN = false) (hb : b.isNaN = false)
    (h : GoodDLo a.toE b.toE p) :
    (Directed.divDown a b).isNaN = false ∧ (Directed.divDown a b).toE ≤ (p : EReal) := by
  obtain ⟨⟨hn, hd⟩, -⟩ := corner_div ha hb h.2.1 h.1
  exact ⟨hn, le_trans hd h.2.2⟩

theorem divUp_good {a b : Float} {p : ℝ} (ha : a.isNaN = false) (hb : b.isNaN = false)
    (h : GoodDHi a.toE b.toE p) :
    (Directed.divUp a b).isNaN = false ∧ (p : EReal) ≤ (Directed.divUp a b).toE := by
  obtain ⟨-, ⟨hn, hd⟩⟩ := corner_div ha hb h.2.1 h.1
  exact ⟨hn, le_trans h.2.2 hd⟩

/-- `x / y ∈ X / Y` for every `x ∈ X`, `y ∈ Y` with `y ≠ 0`; no finiteness assumption
    (if `0 ∈ Y` the result is `whole`). -/
theorem mem_toSet_div {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet)
    (_hy0 : y ≠ 0) : x / y ∈ (X / Y).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  obtain ⟨⟨hYl, hYl'⟩, ⟨hYh, hYh'⟩⟩ := mem_toSet_iff_toE.1 hy
  have hnan : anyNan X Y = false := by simp [anyNan, hXl, hXh, hYl, hYh]
  change x / y ∈ (Interval64.div X Y).toSet
  unfold Interval64.div
  simp only [hnan, Bool.false_eq_true, ↓reduceIte]
  cases hcz : containsZero Y with
  | true => exact mem_toSet_whole _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsign : 0 < Y.lo.toE ∨ Y.hi.toE < 0 := by
    by_contra hc
    push Not at hc
    rw [(containsZero_iff_toE hYl hYh).2 ⟨hc.1, hc.2⟩] at hcz
    exact absurd hcz (by simp)
  -- good corners
  have hlo : ∀ z : ℝ, (GoodDLo X.lo.toE Y.lo.toE z ∨ GoodDLo X.lo.toE Y.hi.toE z ∨
      GoodDLo X.hi.toE Y.lo.toE z ∨ GoodDLo X.hi.toE Y.hi.toE z) →
      ((Directed.divDown X.lo Y.lo).isNaN = false ∧ (Directed.divDown X.lo Y.lo).toE ≤ z) ∨
      ((Directed.divDown X.lo Y.hi).isNaN = false ∧ (Directed.divDown X.lo Y.hi).toE ≤ z) ∨
      ((Directed.divDown X.hi Y.lo).isNaN = false ∧ (Directed.divDown X.hi Y.lo).toE ≤ z) ∨
      ((Directed.divDown X.hi Y.hi).isNaN = false ∧ (Directed.divDown X.hi Y.hi).toE ≤ z) := by
    intro z h
    rcases h with h | h | h | h
    · exact Or.inl (divDown_good hXl hYl h)
    · exact Or.inr (Or.inl (divDown_good hXl hYh h))
    · exact Or.inr (Or.inr (Or.inl (divDown_good hXh hYl h)))
    · exact Or.inr (Or.inr (Or.inr (divDown_good hXh hYh h)))
  have hhi : ∀ z : ℝ, (GoodDHi X.lo.toE Y.lo.toE z ∨ GoodDHi X.lo.toE Y.hi.toE z ∨
      GoodDHi X.hi.toE Y.lo.toE z ∨ GoodDHi X.hi.toE Y.hi.toE z) →
      ((Directed.divUp X.lo Y.lo).isNaN = false ∧ (z : EReal) ≤ (Directed.divUp X.lo Y.lo).toE) ∨
      ((Directed.divUp X.lo Y.hi).isNaN = false ∧ (z : EReal) ≤ (Directed.divUp X.lo Y.hi).toE) ∨
      ((Directed.divUp X.hi Y.lo).isNaN = false ∧ (z : EReal) ≤ (Directed.divUp X.hi Y.lo).toE) ∨
      ((Directed.divUp X.hi Y.hi).isNaN = false ∧ (z : EReal) ≤ (Directed.divUp X.hi Y.hi).toE) := by
    intro z h
    rcases h with h | h | h | h
    · exact Or.inl (divUp_good hXl hYl h)
    · exact Or.inr (Or.inl (divUp_good hXl hYh h))
    · exact Or.inr (Or.inr (Or.inl (divUp_good hXh hYl h)))
    · exact Or.inr (Or.inr (Or.inr (divUp_good hXh hYh h)))
  have kl : GoodDLo X.lo.toE Y.lo.toE (x / y) ∨ GoodDLo X.lo.toE Y.hi.toE (x / y) ∨
      GoodDLo X.hi.toE Y.lo.toE (x / y) ∨ GoodDLo X.hi.toE Y.hi.toE (x / y) := by
    rcases hsign with hs | hs
    · rcases (div_corner_pos hXl' hXh' hYl' hYh' hs).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases (div_corner_neg hXl' hXh' hYl' hYh' hs).1 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have kh : GoodDHi X.lo.toE Y.lo.toE (x / y) ∨ GoodDHi X.lo.toE Y.hi.toE (x / y) ∨
      GoodDHi X.hi.toE Y.lo.toE (x / y) ∨ GoodDHi X.hi.toE Y.hi.toE (x / y) := by
    rcases hsign with hs | hs
    · rcases (div_corner_pos hXl' hXh' hYl' hYh' hs).2 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases (div_corner_neg hXl' hXh' hYl' hYh' hs).2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have L := hlo _ kl
  have H := hhi _ kh
  split
  · -- slow path
    unfold divNaNCorners
    obtain ⟨n1, b1⟩ := fminN4_le L
    obtain ⟨n2, b2⟩ := le_fmaxN4 H
    simp only [n1, n2, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    exact mem_toSet_of_toE n1 n2 b1 b2
  · rename_i hn
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    exact mem_toSet_of_toE hn.1 hn.2 (fmin4_le hn.1 L) (le_fmax4 hn.2 H)

/-! ### Square root -/

theorem unpack_of_toE_top {f : Float} (h : f.toE = ⊤) :
    unpackBits f.toBits = .infinity .positive := by
  unfold Float.toE at h
  revert h
  cases unpackBits f.toBits with
  | notANumber => simp [uE]
  | infinity s => cases s <;> simp [uE]
  | zero s => simp [uE]
  | finite s m e hm => simp [uE]

theorem toE_sqrtUp_of_top {f : Float} (h : f.toE = ⊤) : (Directed.sqrtUp f).toE = ⊤ := by
  have hu : unpackBits (Directed.sqrtUp f).toBits = .infinity .positive := by
    rw [sqrtUp_toBits]
    simp only [Spec.sqrtUp, Spec.sqrt, unpack_of_toE_top h, Spec.sqrtU]
    rfl
  simp [Float.toE, hu, uE]

theorem isNaN_sqrtUp_of_top {f : Float} (h : f.toE = ⊤) : (Directed.sqrtUp f).isNaN = false := by
  have hu : unpackBits (Directed.sqrtUp f).toBits = .infinity .positive := by
    rw [sqrtUp_toBits]
    simp only [Spec.sqrtUp, Spec.sqrt, unpack_of_toE_top h, Spec.sqrtU]
    rfl
  rw [float_isNaN, hu]; rfl

/-- `√x ∈ sqrt X` for `x ∈ X`, `0 ≤ x`; no finiteness assumption (half-lines work). -/
theorem mem_toSet_sqrt {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 ≤ x) :
    Real.sqrt x ∈ (Interval64.sqrt X).toSet := by
  obtain ⟨⟨hXl, hXl'⟩, ⟨hXh, hXh'⟩⟩ := mem_toSet_iff_toE.1 hx
  have hh0 : ¬ X.hi < 0 := by
    rw [lt_zero_iff_toE hXh]; intro h
    exact absurd (lt_of_le_of_lt hXh' h) (not_lt.2 (by exact_mod_cast hx0))
  unfold Interval64.sqrt
  simp only [hXl, hXh, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hh0, decide_false]
  rw [mem_toSet]
  constructor
  · -- lower endpoint
    have key : ∃ r : ℝ, (if decide (X.lo < 0) = true then (0 : Float) else X.lo).toReal? = some r
        ∧ 0 ≤ r ∧ r ≤ x := by
      by_cases hl : X.lo < 0
      · refine ⟨0, ?_, le_refl _, hx0⟩
        simp only [hl, decide_true, ↓reduceIte]
        exact toReal?_eq_some.2 ⟨0, by rfl, by simp⟩
      · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte]
        have h0 : 0 ≤ X.lo.toE := by
          rw [lt_zero_iff_toE hXl] at hl; exact not_lt.1 hl
        have hb : X.lo.toE ≠ ⊥ := fun h => by rw [h] at h0; exact absurd h0 (by simp)
        have ht : X.lo.toE ≠ ⊤ := fun h => by rw [h] at hXl'; exact absurd hXl' (by simp)
        obtain ⟨q, hq, he⟩ := exists_rat_of_toE hXl hb ht
        refine ⟨q, toReal?_eq_some.2 ⟨q, hq, rfl⟩, ?_, ?_⟩
        · rw [he] at h0; exact_mod_cast h0
        · rw [he] at hXl'; exact_mod_cast hXl'
    obtain ⟨r, hr, hr0, hrx⟩ := key
    exact loR_mono (sqrtDown_isRoundDownR hr hr0).1 (Real.sqrt_le_sqrt hrx)
  · -- upper endpoint
    by_cases ht : X.hi.toE = ⊤
    · exact (hiR_iff_toE _ _).2 ⟨isNaN_sqrtUp_of_top ht, by rw [toE_sqrtUp_of_top ht]; simp⟩
    · have hb : X.hi.toE ≠ ⊥ := fun h => by rw [h] at hXh'; exact absurd hXh' (by simp)
      obtain ⟨q, hq, he⟩ := exists_rat_of_toE hXh hb ht
      have hxq : x ≤ (q : ℝ) := by rw [he] at hXh'; exact_mod_cast hXh'
      exact hiR_mono (sqrtUp_isRoundUpR (toReal?_eq_some.2 ⟨q, hq, rfl⟩)
        (le_trans hx0 hxq)).1 (Real.sqrt_le_sqrt hxq)

end RealFP

end
