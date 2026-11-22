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
def toSet (X : Interval128.Interval128) : Set ℝ := {x | loIn X.lh X.ll x ∧ hiIn X.uh X.ul x}

theorem mem_toSet_iff {X : Interval128.Interval128} {x : ℝ} :
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
theorem mem_toInterval64 {X : Interval128.Interval128} {x : ℝ} (hx : x ∈ toSet X) :
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

theorem mem_add {X Y : Interval128.Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
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

theorem mem_sub {X Y : Interval128.Interval128} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
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

theorem mem_neg {X : Interval128.Interval128} {x : ℝ} (hx : x ∈ toSet X) :
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

end RealFP.I128
