/-
Interval128 proofs, part 3: interval enclosure theorems.

Semantics. The lower endpoint `(h, l)` of an `Interval128` admits `x` when
either both words are finite with `h + l ≤ x`, or `l` is a zero and the
(possibly infinite) word `h` satisfies `h ≤ x` in the extended reals. The
upper endpoint is symmetric. A reversed interval is the empty set; NaN words
admit nothing. This is exactly how the runtime produces endpoints: the
double-double kernels give finite pairs, the Interval64 fallback gives
`⟨J.lo, 0⟩` / `⟨J.hi, 0⟩`.
-/
import RealFPMathlib.I128DD
import RealFPMathlib.Unbounded
import RealFPMathlib.Mem

open Interval64 Interval64.Directed
open Interval128 Interval128.DD
open Interval64.Spec Interval64Proofs.FloatBits Interval64Proofs.Value

namespace RealFP.I128

def loIn (h l : Float) (x : ℝ) : Prop :=
  (∃ a b, Fv h a ∧ Fv l b ∧ a + b ≤ x) ∨ (Fv l 0 ∧ h.isNaN = false ∧ h.toE ≤ (x : EReal))

def hiIn (h l : Float) (x : ℝ) : Prop :=
  (∃ a b, Fv h a ∧ Fv l b ∧ x ≤ a + b) ∨ (Fv l 0 ∧ h.isNaN = false ∧ (x : EReal) ≤ h.toE)

/-- The set of reals enclosed by an `Interval128`. -/
def toSet (X : Interval128) : Set ℝ := {x | loIn X.lh X.ll x ∧ hiIn X.uh X.ul x}

theorem mem_toSet_iff {X : Interval128} {x : ℝ} :
    x ∈ toSet X ↔ loIn X.lh X.ll x ∧ hiIn X.uh X.ul x := Iff.rfl

theorem loIn_val {h l : Float} {x a b : ℝ} (hx : loIn h l x) (ha : Fv h a) (hb : Fv l b) :
    a + b ≤ x := by
  rcases hx with ⟨a', b', ha', hb', i⟩ | ⟨hl0, -, hle⟩
  · rw [fv_unique ha ha', fv_unique hb hb']; exact i
  · rw [fv_unique hb hl0, toE_of_fv ha] at *
    have : a ≤ x := by exact_mod_cast hle
    linarith

theorem hiIn_val {h l : Float} {x a b : ℝ} (hx : hiIn h l x) (ha : Fv h a) (hb : Fv l b) :
    x ≤ a + b := by
  rcases hx with ⟨a', b', ha', hb', i⟩ | ⟨hl0, -, hle⟩
  · rw [fv_unique ha ha', fv_unique hb hb']; exact i
  · rw [fv_unique hb hl0, toE_of_fv ha] at *
    have : x ≤ a := by exact_mod_cast hle
    linarith

/-! ### Interval64 embedding and hull -/

theorem mem_ofInterval64 {J : Interval64} {x : ℝ} (hx : x ∈ J.toSet) :
    x ∈ toSet (Interval128.ofInterval64 J) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := mem_toSet_iff_toE.1 hx
  exact ⟨Or.inr ⟨fv_zero, h1, h2⟩, Or.inr ⟨fv_zero, h3, h4⟩⟩

theorem mem_whole (x : ℝ) : x ∈ toSet Interval128.whole :=
  mem_ofInterval64 (mem_toSet_whole x)

theorem unpack_of_fv_zero {l : Float} (h : Fv l 0) : ∃ s, unpackBits l.toBits = .zero s := by
  obtain ⟨q, hq, hq0⟩ := toReal?_eq_some.1 h
  rcases Interval64Proofs.AddBits.bitsToRat?_cases hq with ⟨s, hu, -⟩ | ⟨s, m, e, hm, hu, rfl, -⟩
  · exact ⟨s, hu⟩
  · exfalso
    have : Interval64Proofs.Pow2.signedVal s m e = 0 := by exact_mod_cast hq0
    exact Interval64Proofs.ExactAdd.signedVal_ne_zero_of_pos hm this

theorem addDown_neginf_zero {h l : Float} (hh : unpackBits h.toBits = .infinity .negative)
    (hl : Fv l 0) (x : ℝ) : loR (bitsToEVal (addDown h l).toBits) x := by
  obtain ⟨s, hs⟩ := unpack_of_fv_zero hl
  have e : addDown h l = Float.ofBits (packDirected false
      (addU (unpackBits h.toBits) (unpackBits l.toBits) false)) := rfl
  rw [e, hh, hs]
  show loR (bitsToEVal (Float.ofBits (packBits (.infinity .negative))).toBits) x
  rw [toBits_ofBits, bitsToEVal, Interval64Proofs.Pack.unpackBits_inf]
  trivial

theorem addUp_inf_zero {h l : Float} (hh : unpackBits h.toBits = .infinity .positive)
    (hl : Fv l 0) (x : ℝ) : hiR (bitsToEVal (addUp h l).toBits) x := by
  obtain ⟨s, hs⟩ := unpack_of_fv_zero hl
  have e : addUp h l = Float.ofBits (packDirected true
      (addU (unpackBits h.toBits) (unpackBits l.toBits) true)) := rfl
  rw [e, hh, hs]
  show hiR (bitsToEVal (Float.ofBits (packBits (.infinity .positive))).toBits) x
  rw [toBits_ofBits, bitsToEVal, Interval64Proofs.Pack.unpackBits_inf]
  trivial

theorem hull_lo {h l : Float} {x : ℝ} (hx : loIn h l x) : loR (bitsToEVal (addDown h l).toBits) x := by
  rcases hx with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
  · exact loR_mono (addDown_isRoundDownR ha hb).1 i
  · rcases fin_or_NF h with ⟨a, ha⟩ | hnf
    · have : a ≤ x := by rw [toE_of_fv ha] at hle; exact_mod_cast hle
      exact loR_mono (addDown_isRoundDownR ha hl0).1 (by linarith)
    · rcases hnf with hu | ⟨s, hu⟩
      · rw [float_isNaN, hu] at hn; exact absurd hn (by decide)
      · cases s with
        | negative => exact addDown_neginf_zero hu hl0 x
        | positive =>
          exfalso
          have : h.toE = ⊤ := by unfold Float.toE; rw [hu]; rfl
          rw [this] at hle; exact EReal.coe_ne_top x (top_le_iff.1 hle)

theorem hull_hi {h l : Float} {x : ℝ} (hx : hiIn h l x) : hiR (bitsToEVal (addUp h l).toBits) x := by
  rcases hx with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
  · exact hiR_mono (addUp_isRoundUpR ha hb).1 i
  · rcases fin_or_NF h with ⟨a, ha⟩ | hnf
    · have : x ≤ a := by rw [toE_of_fv ha] at hle; exact_mod_cast hle
      exact hiR_mono (addUp_isRoundUpR ha hl0).1 (by linarith)
    · rcases hnf with hu | ⟨s, hu⟩
      · rw [float_isNaN, hu] at hn; exact absurd hn (by decide)
      · cases s with
        | positive => exact addUp_inf_zero hu hl0 x
        | negative =>
          exfalso
          have : h.toE = ⊥ := by unfold Float.toE; rw [hu]; rfl
          rw [this] at hle; exact EReal.coe_ne_bot x (le_bot_iff.1 hle)

/-- The outward binary64 hull contains the interval. -/
theorem mem_toInterval64 {X : Interval128} {x : ℝ} (hx : x ∈ toSet X) :
    x ∈ (Interval128.toInterval64 X).toSet :=
  mem_toSet.2 ⟨hull_lo hx.1, hull_hi hx.2⟩

/-! ### Per-endpoint choice -/

theorem loIn_of_I64 {J : Interval64} {x : ℝ} (hx : x ∈ J.toSet) : loIn J.lo 0 x :=
  (mem_ofInterval64 hx).1

theorem hiIn_of_I64 {J : Interval64} {x : ℝ} (hx : x ∈ J.toSet) : hiIn J.hi 0 x :=
  (mem_ofInterval64 hx).2

theorem mem_pick {l u : DD} {slow : Unit → Interval64} {z : ℝ}
    (hl : ∀ H L, Fv l.hi H → Fv l.lo L → H + L ≤ z)
    (hu : ∀ H L, Fv u.hi H → Fv u.lo L → z ≤ H + L)
    (hs : z ∈ (slow ()).toSet) : z ∈ toSet (Interval128.pick l u slow) := by
  have lo_ok : l.isFin = true → loIn l.hi l.lo z := fun h => by
    obtain ⟨H, L, hH, hL⟩ := fv_of_isFin h
    exact Or.inl ⟨H, L, hH, hL, hl H L hH hL⟩
  have hi_ok : u.isFin = true → hiIn u.hi u.lo z := fun h => by
    obtain ⟨H, L, hH, hL⟩ := fv_of_isFin h
    exact Or.inl ⟨H, L, hH, hL, hu H L hH hL⟩
  unfold Interval128.pick
  split_ifs with c1 c2 c2
  · exact ⟨lo_ok c1, hi_ok c2⟩
  · exact ⟨lo_ok c1, hiIn_of_I64 hs⟩
  · exact ⟨loIn_of_I64 hs, hi_ok c2⟩
  · exact mem_ofInterval64 hs

/-! ### Addition, subtraction, negation -/

theorem mem_add {X Y : Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
    x + y ∈ toSet (X + Y) := by
  show x + y ∈ toSet (Interval128.addSpec X Y)
  apply mem_pick
  · intro H L hH hL
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addLo_le hH hL
    have := loIn_val hx.1 ha1 ha2; have := loIn_val hy.1 hb1 hb2; linarith
  · intro H L hH hL
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addHi_ge hH hL
    have := hiIn_val hx.2 ha1 ha2; have := hiIn_val hy.2 hb1 hb2; linarith
  · exact add_mem_toSet (mem_toInterval64 hx) (mem_toInterval64 hy)

theorem mem_sub {X Y : Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
    x - y ∈ toSet (X - Y) := by
  show x - y ∈ toSet (Interval128.subSpec X Y)
  apply mem_pick
  · intro H L hH hL
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addLo_le hH hL
    have := loIn_val hx.1 ha1 ha2; have := hiIn_val hy.2 (fv_of_neg hb1) (fv_of_neg hb2)
    linarith
  · intro H L hH hL
    obtain ⟨a1, a2, b1, b2, ha1, ha2, hb1, hb2, i⟩ := addHi_ge hH hL
    have := hiIn_val hx.2 ha1 ha2; have := loIn_val hy.1 (fv_of_neg hb1) (fv_of_neg hb2)
    linarith
  · exact sub_mem_toSet (mem_toInterval64 hx) (mem_toInterval64 hy)

theorem fv_neg_zero {l : Float} (h : Fv l 0) : Fv (-l) 0 := by simpa using fv_neg h

theorem mem_neg {X : Interval128} {x : ℝ} (hx : x ∈ toSet X) :
    -x ∈ toSet (-X) := by
  show -x ∈ toSet (Interval128.neg X)
  constructor
  · rcases hx.2 with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
    · exact Or.inl ⟨-a, -b, fv_neg ha, fv_neg hb, by linarith⟩
    · refine Or.inr ⟨fv_neg_zero hl0, isNaN_neg hn, ?_⟩
      show (-X.uh).toE ≤ _
      rw [toE_neg hn, EReal.coe_neg]; exact EReal.neg_le_neg_iff.2 hle
  · rcases hx.1 with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
    · exact Or.inl ⟨-a, -b, fv_neg ha, fv_neg hb, by linarith⟩
    · refine Or.inr ⟨fv_neg_zero hl0, isNaN_neg hn, ?_⟩
      show _ ≤ (-X.lh).toE
      rw [toE_neg hn, EReal.coe_neg]; exact EReal.neg_le_neg_iff.2 hle

/-! ### Multiplication -/

theorem isFin_vals {X : Interval128} (h : X.isFin = true) :
    ∃ a1 a2 a3 a4, Fv X.lh a1 ∧ Fv X.ll a2 ∧ Fv X.uh a3 ∧ Fv X.ul a4 := by
  simp only [Interval128.isFin, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨a1, f1⟩ := isFinite_fv h1
  obtain ⟨a2, f2⟩ := isFinite_fv h2
  obtain ⟨a3, f3⟩ := isFinite_fv h3
  obtain ⟨a4, f4⟩ := isFinite_fv h4
  exact ⟨a1, a2, a3, a4, f1, f2, f3, f4⟩

theorem bool_decide {b : Bool} {p : Prop} [Decidable p] (h : b = true ↔ p) : b = decide p := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact h

theorem mulLo_le' {ah al bh bl : Float} {a1 a2 b1 b2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hb1 : Fv bh b1) (hb2 : Fv bl b2) (hH : Fv (mulLo ah al bh bl).hi H)
    (hL : Fv (mulLo ah al bh bl).lo L) : H + L ≤ (a1 + a2) * (b1 + b2) := by
  obtain ⟨c1, c2, d1, d2, hc1, hc2, hd1, hd2, i⟩ := mulLo_le hH hL
  rw [fv_unique ha1 hc1, fv_unique ha2 hc2, fv_unique hb1 hd1, fv_unique hb2 hd2]; exact i

theorem mulHi_ge' {ah al bh bl : Float} {a1 a2 b1 b2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hb1 : Fv bh b1) (hb2 : Fv bl b2) (hH : Fv (mulHi ah al bh bl).hi H)
    (hL : Fv (mulHi ah al bh bl).lo L) : (a1 + a2) * (b1 + b2) ≤ H + L := by
  obtain ⟨c1, c2, d1, d2, hc1, hc2, hd1, hd2, i⟩ := mulHi_ge hH hL
  rw [fv_unique ha1 hc1, fv_unique ha2 hc2, fv_unique hb1 hd1, fv_unique hb2 hd2]; exact i

theorem mixed_lo {xl xh yl yh x y : ℝ} (h1 : xl ≤ x) (h2 : x ≤ xh) (h3 : yl ≤ y) (h4 : y ≤ yh)
    (s1 : xl < 0) (s2 : 0 < xh) (s3 : yl < 0) (s4 : 0 < yh) :
    xl * yh ≤ x * y ∨ xh * yl ≤ x * y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · left; nlinarith
  · right; nlinarith
  · left; nlinarith
  · left; nlinarith

theorem mixed_hi {xl xh yl yh x y : ℝ} (h1 : xl ≤ x) (h2 : x ≤ xh) (h3 : yl ≤ y) (h4 : y ≤ yh)
    (s1 : xl < 0) (s2 : 0 < xh) (s3 : yl < 0) (s4 : 0 < yh) :
    x * y ≤ xl * yl ∨ x * y ≤ xh * yh := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · right; nlinarith
  · left; nlinarith
  · right; nlinarith
  · left; nlinarith

section mul
variable {X Y : Interval128} {x y a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
  (fa1 : Fv X.lh a1) (fa2 : Fv X.ll a2) (fa3 : Fv X.uh a3) (fa4 : Fv X.ul a4)
  (fb1 : Fv Y.lh b1) (fb2 : Fv Y.ll b2) (fb3 : Fv Y.uh b3) (fb4 : Fv Y.ul b4)
  (hx1 : a1 + a2 ≤ x) (hx2 : x ≤ a3 + a4) (hy1 : b1 + b2 ≤ y) (hy2 : y ≤ b3 + b4)
include fa1 fa2 fa3 fa4 fb1 fb2 fb3 fb4 hx1 hx2 hy1 hy2

theorem mulLoF_le : ∀ H L, Fv (Interval128.mulLoF X Y).hi H → Fv (Interval128.mulLoF X Y).lo L →
    H + L ≤ x * y := by
  intro H L hH hL
  have e1 := bool_decide (nonneg_iff fb1 fb2)
  have e2 := bool_decide (nonneg_iff fa1 fa2)
  have e3 := bool_decide (nonpos_iff fb3 fb4)
  have e4 := bool_decide (nonpos_iff fa3 fa4)
  simp only [Interval128.mulLoF, e1, e2, e3, e4, decide_eq_true_eq] at hH hL
  split_ifs at hH hL with c1 c2 c3 c4 c5 c6
  · have := mulLo_le' fa1 fa2 fb1 fb2 hH hL; nlinarith
  · have := mulLo_le' fa1 fa2 fb3 fb4 hH hL; nlinarith
  · have := mulLo_le' fa3 fa4 fb3 fb4 hH hL; nlinarith
  · have := mulLo_le' fa3 fa4 fb1 fb2 hH hL; nlinarith
  · have := mulLo_le' fa3 fa4 fb1 fb2 hH hL; nlinarith
  · have := mulLo_le' fa1 fa2 fb3 fb4 hH hL; nlinarith
  · obtain ⟨A, B, ⟨h1, l1, hh1, hl1, rfl⟩, ⟨h2, l2, hh2, hl2, rfl⟩, i1, i2⟩ := minLo_le hH hL
    have j1 := mulLo_le' fa1 fa2 fb3 fb4 hh1 hl1
    have j2 := mulLo_le' fa3 fa4 fb1 fb2 hh2 hl2
    rcases mixed_lo hx1 hx2 hy1 hy2 (by linarith) (by linarith) (by linarith) (by linarith)
      with k | k <;> linarith

theorem mulHiF_ge : ∀ H L, Fv (Interval128.mulHiF X Y).hi H → Fv (Interval128.mulHiF X Y).lo L →
    x * y ≤ H + L := by
  intro H L hH hL
  have e1 := bool_decide (nonneg_iff fb1 fb2)
  have e2 := bool_decide (nonneg_iff fa3 fa4)
  have e3 := bool_decide (nonpos_iff fb3 fb4)
  have e4 := bool_decide (nonneg_iff fa1 fa2)
  have e5 := bool_decide (nonpos_iff fa3 fa4)
  simp only [Interval128.mulHiF, e1, e2, e3, e4, e5, decide_eq_true_eq] at hH hL
  split_ifs at hH hL with c1 c2 c3 c4 c5 c6
  · have := mulHi_ge' fa3 fa4 fb3 fb4 hH hL; nlinarith
  · have := mulHi_ge' fa3 fa4 fb1 fb2 hH hL; nlinarith
  · have := mulHi_ge' fa1 fa2 fb3 fb4 hH hL; nlinarith
  · have := mulHi_ge' fa1 fa2 fb1 fb2 hH hL; nlinarith
  · have := mulHi_ge' fa3 fa4 fb3 fb4 hH hL; nlinarith
  · have := mulHi_ge' fa1 fa2 fb1 fb2 hH hL; nlinarith
  · obtain ⟨A, B, ⟨h1, l1, hh1, hl1, rfl⟩, ⟨h2, l2, hh2, hl2, rfl⟩, i1, i2⟩ := maxHi_ge hH hL
    have j1 := mulHi_ge' fa1 fa2 fb1 fb2 hh1 hl1
    have j2 := mulHi_ge' fa3 fa4 fb3 fb4 hh2 hl2
    rcases mixed_hi hx1 hx2 hy1 hy2 (by linarith) (by linarith) (by linarith) (by linarith)
      with k | k <;> linarith

end mul

theorem mem_mul {X Y : Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
    x * y ∈ toSet (X * Y) := by
  show x * y ∈ toSet (Interval128.mulSpec X Y)
  have hs := mem_toSet_mul (mem_toInterval64 hx) (mem_toInterval64 hy)
  unfold Interval128.mulSpec
  split_ifs with c
  · simp only [Bool.and_eq_true] at c
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c.1
    obtain ⟨b1, b2, b3, b4, fb1, fb2, fb3, fb4⟩ := isFin_vals c.2
    have hx1 := loIn_val hx.1 fa1 fa2
    have hx2 := hiIn_val hx.2 fa3 fa4
    have hy1 := loIn_val hy.1 fb1 fb2
    have hy2 := hiIn_val hy.2 fb3 fb4
    exact mem_pick (mulLoF_le fa1 fa2 fa3 fa4 fb1 fb2 fb3 fb4 hx1 hx2 hy1 hy2)
      (mulHiF_ge fa1 fa2 fa3 fa4 fb1 fb2 fb3 fb4 hx1 hx2 hy1 hy2) hs
  · exact mem_ofInterval64 hs

/-! ### Division -/

theorem divPos_lo {xl x yl yh y : ℝ} (h1 : xl ≤ x) (h3 : yl ≤ y) (h4 : y ≤ yh) (hyl : 0 < yl) :
    (0 ≤ xl → xl / yh ≤ x / y) ∧ (¬ 0 ≤ xl → xl / yl ≤ x / y) := by
  have hy : 0 < y := by linarith
  have hyh : 0 < yh := by linarith
  constructor
  · intro h0
    rw [div_le_div_iff₀ hyh hy]; nlinarith
  · intro h0
    rw [div_le_div_iff₀ hyl hy]; push Not at h0; nlinarith

theorem divPos_hi {xh x yl yh y : ℝ} (h2 : x ≤ xh) (h3 : yl ≤ y) (h4 : y ≤ yh) (hyl : 0 < yl) :
    (0 ≤ xh → x / y ≤ xh / yl) ∧ (¬ 0 ≤ xh → x / y ≤ xh / yh) := by
  have hy : 0 < y := by linarith
  have hyh : 0 < yh := by linarith
  constructor
  · intro h0
    rw [div_le_div_iff₀ hy hyl]; nlinarith
  · intro h0
    rw [div_le_div_iff₀ hy hyh]; push Not at h0; nlinarith

theorem divLo_le' {ah al bh bl : Float} {a1 a2 b1 b2 H L : ℝ} (ha1 : Fv ah a1) (ha2 : Fv al a2)
    (hb1 : Fv bh b1) (hb2 : Fv bl b2) (hB : 0 < b1 + b2) :
    Fv (divLo ah al bh bl).hi H → Fv (divLo ah al bh bl).lo L → H + L ≤ (a1 + a2) / (b1 + b2) :=
  divLo_le ha1 ha2 hb1 hb2 hB

theorem mem_divPos {X Y : Interval128} {x y a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
    (fa1 : Fv X.lh a1) (fa2 : Fv X.ll a2) (fa3 : Fv X.uh a3) (fa4 : Fv X.ul a4)
    (fb1 : Fv Y.lh b1) (fb2 : Fv Y.ll b2) (fb3 : Fv Y.uh b3) (fb4 : Fv Y.ul b4)
    (hx1 : a1 + a2 ≤ x) (hx2 : x ≤ a3 + a4) (hy1 : b1 + b2 ≤ y) (hy2 : y ≤ b3 + b4)
    (hpos : 0 < b1 + b2) (hs : x / y ∈ (Interval128.toInterval64 X / Interval128.toInterval64 Y).toSet) :
    x / y ∈ toSet (Interval128.divPos X Y) := by
  unfold Interval128.divPos
  have hyh : 0 < b3 + b4 := by linarith
  obtain ⟨l1, l2⟩ := divPos_lo hx1 hy1 hy2 hpos
  obtain ⟨u1, u2⟩ := divPos_hi hx2 hy1 hy2 hpos
  refine mem_pick (slow := fun _ => Interval128.toInterval64 X / Interval128.toInterval64 Y)
    ?_ ?_ hs
  · intro H L hH hL
    by_cases c : DD.nonneg X.lh X.ll = true
    · rw [if_pos c] at hH hL
      exact le_trans (divLo_le fa1 fa2 fb3 fb4 hyh hH hL) (l1 ((nonneg_iff fa1 fa2).1 c))
    · rw [if_neg c] at hH hL
      exact le_trans (divLo_le fa1 fa2 fb1 fb2 hpos hH hL)
        (l2 (fun h => c ((nonneg_iff fa1 fa2).2 h)))
  · intro H L hH hL
    by_cases c : DD.nonneg X.uh X.ul = true
    · rw [if_pos c] at hH hL
      exact le_trans (u1 ((nonneg_iff fa3 fa4).1 c)) (divHi_ge fa3 fa4 fb1 fb2 hpos hH hL)
    · rw [if_neg c] at hH hL
      exact le_trans (u2 (fun h => c ((nonneg_iff fa3 fa4).2 h)))
        (divHi_ge fa3 fa4 fb3 fb4 hyh hH hL)

theorem mem_div {X Y : Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y)
    (hy0 : y ≠ 0) : x / y ∈ toSet (X / Y) := by
  show x / y ∈ toSet (Interval128.divSpec X Y)
  have hs := mem_toSet_div (mem_toInterval64 hx) (mem_toInterval64 hy) hy0
  unfold Interval128.divSpec
  split_ifs with c c1 c2
  · simp only [Bool.and_eq_true] at c
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c.1
    obtain ⟨b1, b2, b3, b4, fb1, fb2, fb3, fb4⟩ := isFin_vals c.2
    exact mem_divPos fa1 fa2 fa3 fa4 fb1 fb2 fb3 fb4 (loIn_val hx.1 fa1 fa2) (hiIn_val hx.2 fa3 fa4)
      (loIn_val hy.1 fb1 fb2) (hiIn_val hy.2 fb3 fb4) ((pos_iff fb1 fb2).1 c1) hs
  · simp only [Bool.and_eq_true] at c
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c.1
    obtain ⟨b1, b2, b3, b4, fb1, fb2, fb3, fb4⟩ := isFin_vals c.2
    have hneg := (neg_iff fb3 fb4).1 c2
    have hx' := mem_neg hx
    have hy' := mem_neg hy
    have e : x / y = (-x) / (-y) := (neg_div_neg_eq x y).symm
    rw [e]
    have hs' : -x / -y ∈ (Interval128.toInterval64 (-X) / Interval128.toInterval64 (-Y)).toSet :=
      mem_toSet_div (mem_toInterval64 hx') (mem_toInterval64 hy') (neg_ne_zero.2 hy0)
    exact mem_divPos (fv_neg fa3) (fv_neg fa4) (fv_neg fa1) (fv_neg fa2)
      (fv_neg fb3) (fv_neg fb4) (fv_neg fb1) (fv_neg fb2)
      (loIn_val hx'.1 (fv_neg fa3) (fv_neg fa4)) (hiIn_val hx'.2 (fv_neg fa1) (fv_neg fa2))
      (loIn_val hy'.1 (fv_neg fb3) (fv_neg fb4)) (hiIn_val hy'.2 (fv_neg fb1) (fv_neg fb2))
      (by linarith) hs'
  · exact mem_whole _
  · exact mem_ofInterval64 hs

/-! ### Square root -/

theorem mem_sqrt {X : Interval128} {x : ℝ} (hx : x ∈ toSet X) (hx0 : 0 ≤ x) :
    Real.sqrt x ∈ toSet (Interval128.sqrt X) := by
  show Real.sqrt x ∈ toSet (Interval128.sqrtSpec X)
  have hs := mem_toSet_sqrt (mem_toInterval64 hx) hx0
  unfold Interval128.sqrtSpec
  split_ifs with c c1 c2
  · obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c
    have := (neg_iff fa3 fa4).1 c1
    have := hiIn_val hx.2 fa3 fa4
    exact absurd hx0 (by linarith)
  · obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c
    have hx1 := loIn_val hx.1 fa1 fa2
    have hx2 := hiIn_val hx.2 fa3 fa4
    refine mem_pick (slow := fun _ => Interval64.sqrt (Interval128.toInterval64 X)) ?_ ?_ hs
    · intro H L hH hL
      exact le_trans (sqrtLo_le fa1 fa2 ((nonneg_iff fa1 fa2).1 c2) hH hL) (Real.sqrt_le_sqrt hx1)
    · intro H L hH hL
      exact le_trans (Real.sqrt_le_sqrt hx2) (sqrtHi_ge fa3 fa4 (by linarith) hH hL)
  · obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c
    have hx2 := hiIn_val hx.2 fa3 fa4
    refine mem_pick (slow := fun _ => Interval64.sqrt (Interval128.toInterval64 X)) ?_ ?_ hs
    · intro H L hH hL
      rw [fv_unique hH fv_zero, fv_unique hL fv_zero]; simp [Real.sqrt_nonneg]
    · intro H L hH hL
      exact le_trans (Real.sqrt_le_sqrt hx2) (sqrtHi_ge fa3 fa4 (by linarith) hH hL)
  · exact mem_ofInterval64 hs

/-! ### Conversions -/

theorem mem_point {f : Float} {v : ℝ} (h : Fv f v) : v ∈ toSet (Interval128.point f) :=
  ⟨Or.inl ⟨v, 0, h, fv_zero, by simp⟩, Or.inl ⟨v, 0, h, fv_zero, by simp⟩⟩

theorem fv_of_loR_hiR {f : Float} {a b : ℝ} (hl : loR (bitsToEVal f.toBits) b)
    (hh : hiR (bitsToEVal f.toBits) a) : ∃ v, Fv f v ∧ a ≤ v ∧ v ≤ b := by
  obtain ⟨hn, h1⟩ := (loR_iff_toE f b).1 hl
  obtain ⟨-, h2⟩ := (hiR_iff_toE f a).1 hh
  obtain ⟨q, hq, hqe⟩ := exists_rat_of_toE hn
    (fun h => by rw [h] at h2; exact EReal.coe_ne_bot a (le_bot_iff.1 h2))
    (fun h => by rw [h] at h1; exact EReal.coe_ne_top b (top_le_iff.1 h1))
  rw [hqe] at h1 h2
  exact ⟨q, toReal?_of_bitsToRat? hq, by exact_mod_cast h2, by exact_mod_cast h1⟩

theorem repr_zero : RepresentableR 0 := (representableR_iff_exists_float 0).2 ⟨0, fv_zero⟩

theorem ofRatDown_float_lo (q : ℚ) : IsRoundDownR (q : ℝ) (bitsToEVal (Float.ofRatDown q).toBits) := by
  have h := ofRatDown_isRoundDownR q
  show IsRoundDownR (q : ℝ) (bitsToEVal (Float.ofBits (Interval64.Spec.ofRatDown q)).toBits)
  rw [toBits_ofBits]
  cases hb : bitsToEVal (Interval64.Spec.ofRatDown q) with
  | none => rw [hb] at h; exact absurd h.1 (by simp [loR])
  | some ev => rw [bitsToEVal_pack_unpack_of_some hb, ← hb]; exact h

theorem ofRatUp_float_hi (q : ℚ) : IsRoundUpR (q : ℝ) (bitsToEVal (Float.ofRatUp q).toBits) := by
  have h := ofRatUp_isRoundUpR q
  show IsRoundUpR (q : ℝ) (bitsToEVal (Float.ofBits (Interval64.Spec.ofRatUp q)).toBits)
  rw [toBits_ofBits]
  cases hb : bitsToEVal (Interval64.Spec.ofRatUp q) with
  | none => rw [hb] at h; exact absurd h.1 (by simp [hiR])
  | some ev => rw [bitsToEVal_pack_unpack_of_some hb, ← hb]; exact h

theorem ddOfRatDown_lo (q : ℚ) :
    loIn (Interval128.ddOfRatDown q).hi (Interval128.ddOfRatDown q).lo (q : ℝ) := by
  have hl := (ofRatDown_float_lo q).1
  unfold Interval128.ddOfRatDown
  dsimp only
  split
  · rename_i r hr
    have hfr : Fv (Float.ofRatDown q) r := toReal?_of_bitsToRat? hr
    have hrq : (r : ℝ) ≤ q := le_of_loR hfr hl
    have h2 := ofRatDown_float_lo (q - r)
    have h0 : hiR (bitsToEVal (Float.ofRatDown (q - r)).toBits) 0 :=
      h2.2 0 repr_zero (by push_cast; linarith)
    obtain ⟨v, hv, -, hv2⟩ := fv_of_loR_hiR h2.1 h0
    exact Or.inl ⟨r, v, hfr, hv, by push_cast at hv2; linarith⟩
  · exact Or.inr ⟨fv_zero, ((loR_iff_toE _ _).1 hl).1, ((loR_iff_toE _ _).1 hl).2⟩

theorem ddOfRatUp_hi (q : ℚ) :
    hiIn (Interval128.ddOfRatUp q).hi (Interval128.ddOfRatUp q).lo (q : ℝ) := by
  have hl := (ofRatUp_float_hi q).1
  unfold Interval128.ddOfRatUp
  dsimp only
  split
  · rename_i r hr
    have hfr : Fv (Float.ofRatUp q) r := toReal?_of_bitsToRat? hr
    have hrq : (q : ℝ) ≤ r := ge_of_hiR hfr hl
    have h2 := ofRatUp_float_hi (q - r)
    have h0 : loR (bitsToEVal (Float.ofRatUp (q - r)).toBits) 0 :=
      h2.2 0 repr_zero (by push_cast; linarith)
    obtain ⟨v, hv, hv1, -⟩ := fv_of_loR_hiR h0 h2.1
    exact Or.inl ⟨r, v, hfr, hv, by push_cast at hv1; linarith⟩
  · exact Or.inr ⟨fv_zero, ((hiR_iff_toE _ _).1 hl).1, ((hiR_iff_toE _ _).1 hl).2⟩

theorem mem_ofRat (q : ℚ) : (q : ℝ) ∈ toSet (Interval128.ofRat q) :=
  ⟨ddOfRatDown_lo q, ddOfRatUp_hi q⟩

theorem mem_ofNat (n : ℕ) : (n : ℝ) ∈ toSet (Interval128.ofNat n) := by
  have := mem_ofRat (n : ℚ); push_cast at this; exact this

theorem mem_ofInt (n : ℤ) : (n : ℝ) ∈ toSet (Interval128.ofInt n) := by
  have := mem_ofRat (n : ℚ); push_cast at this; exact this

end RealFP.I128
