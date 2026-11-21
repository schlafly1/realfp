/-
Four-corner lemmas in the extended reals, allowing infinite endpoints.

`mul_corner_lo` / `mul_corner_hi`: for `x ∈ [A, B]`, `y ∈ [C, D]` (endpoints in
`EReal`), either every corner is a `0 · ∞` pair, or some corner that is not
such a pair bounds `x * y` from below (resp. above). This is exactly what the
`Interval64.mul` corner-skipping rule needs.

`div_corner_lo` / `div_corner_hi`: the same for `x / y` when `0 < C` or
`D < 0`, with corners that are not `±∞ / ±∞`.
-/
import RealFPMathlib.Ext

noncomputable section

namespace RealFP

/-- A corner that is not a `0 · ∞` pair and bounds `p` from below. -/
def GoodLo (a b : EReal) (p : ℝ) : Prop := ¬ SkipMul a b ∧ a * b ≤ (p : EReal)
/-- A corner that is not a `0 · ∞` pair and bounds `p` from above. -/
def GoodHi (a b : EReal) (p : ℝ) : Prop := ¬ SkipMul a b ∧ (p : EReal) ≤ a * b

def AllSkip (A B C D : EReal) : Prop :=
  SkipMul A C ∧ SkipMul A D ∧ SkipMul B C ∧ SkipMul B D

theorem ereal_neg_eq_zero (a : EReal) : -a = 0 ↔ a = 0 := by
  constructor
  · intro h; rw [← neg_neg a, h, neg_zero]
  · intro h; rw [h, neg_zero]

theorem skipMul_neg_left (a b : EReal) : SkipMul (-a) b ↔ SkipMul a b := by
  simp only [SkipMul, ereal_neg_eq_zero, EReal.neg_eq_top_iff, EReal.neg_eq_bot_iff]; tauto

theorem skipMul_neg_right (a b : EReal) : SkipMul a (-b) ↔ SkipMul a b := by
  simp only [SkipMul, ereal_neg_eq_zero, EReal.neg_eq_top_iff, EReal.neg_eq_bot_iff]; tauto

theorem ereal_mul_neg (a b : EReal) : a * -b = -(a * b) := by
  rw [mul_comm, EReal.neg_mul, mul_comm]

theorem not_skip_coe (a b : ℝ) : ¬ SkipMul (a : EReal) (b : EReal) := by
  simp [SkipMul]

theorem coe_mul_le {a b p : ℝ} (h : a * b ≤ p) : (a : EReal) * (b : EReal) ≤ (p : EReal) := by
  rw [← EReal.coe_mul]; exact EReal.coe_le_coe h

theorem coe_le_mul {a b p : ℝ} (h : p ≤ a * b) : (p : EReal) ≤ (a : EReal) * (b : EReal) := by
  rw [← EReal.coe_mul]; exact EReal.coe_le_coe h

theorem mul_corner_lo_nonneg {A B C D : EReal} {x y : ℝ} (hA : A ≤ x) (hB : (x : EReal) ≤ B)
    (hC : C ≤ y) (hD : (y : EReal) ≤ D) (hy : 0 ≤ y) :
    AllSkip A B C D ∨ GoodLo A C (x * y) ∨ GoodLo A D (x * y) ∨ GoodLo B C (x * y) ∨
      GoodLo B D (x * y) := by
  induction A using EReal.rec with
  | top => exact absurd hA (by simp)
  | bot =>
    induction D using EReal.rec with
    | bot => exact absurd hD (by simp)
    | top => right; right; left; exact ⟨by simp [SkipMul], by simp⟩
    | coe d =>
      have hyd : y ≤ d := EReal.coe_le_coe_iff.1 hD
      rcases lt_or_ge 0 d with hd | hd
      · right; right; left
        exact ⟨by simp [SkipMul, hd.ne'], by rw [EReal.bot_mul_coe_of_pos hd]; exact bot_le⟩
      have hy0 : y = 0 := le_antisymm (le_trans hyd hd) hy
      have hd0 : d = 0 := le_antisymm hd (hy0 ▸ hyd)
      subst hy0 hd0
      induction B using EReal.rec with
      | bot => exact absurd hB (by simp)
      | coe b => right; right; right; right; exact ⟨not_skip_coe _ _, coe_mul_le (by simp)⟩
      | top =>
        induction C using EReal.rec with
        | top => exact absurd hC (by simp)
        | bot => right; right; right; left; exact ⟨by simp [SkipMul], by simp⟩
        | coe c =>
          have hc0 : c ≤ 0 := EReal.coe_le_coe_iff.1 hC
          rcases lt_or_eq_of_le hc0 with hc | hc
          · right; right; right; left
            exact ⟨by simp [SkipMul, hc.ne], by rw [EReal.top_mul_coe_of_neg hc]; exact bot_le⟩
          · subst hc; left; simp [AllSkip, SkipMul]
  | coe a =>
    have hax : a ≤ x := EReal.coe_le_coe_iff.1 hA
    rcases le_or_gt 0 a with ha | ha
    · induction C using EReal.rec with
      | top => exact absurd hC (by simp)
      | coe c =>
        have hcy : c ≤ y := EReal.coe_le_coe_iff.1 hC
        right; left
        exact ⟨not_skip_coe _ _, coe_mul_le (by nlinarith)⟩
      | bot =>
        rcases lt_or_eq_of_le ha with ha' | ha'
        · right; left
          exact ⟨by simp [SkipMul, ha'.ne'], by rw [EReal.coe_mul_bot_of_pos ha']; exact bot_le⟩
        subst ha'
        induction D using EReal.rec with
        | bot => exact absurd hD (by simp)
        | coe d => right; right; left; exact ⟨not_skip_coe _ _, coe_mul_le (by nlinarith)⟩
        | top =>
          induction B using EReal.rec with
          | bot => exact absurd hB (by simp)
          | top => right; right; right; left; exact ⟨by simp [SkipMul], by simp⟩
          | coe b =>
            have hxb : x ≤ b := EReal.coe_le_coe_iff.1 hB
            rcases lt_or_ge 0 b with hb | hb
            · right; right; right; left
              exact ⟨by simp [SkipMul, hb.ne'], by rw [EReal.coe_mul_bot_of_pos hb]; exact bot_le⟩
            · have hb0 : b = 0 := le_antisymm hb (le_trans hax hxb)
              subst hb0; left; simp [AllSkip, SkipMul]
    · induction D using EReal.rec with
      | bot => exact absurd hD (by simp)
      | coe d =>
        have hyd : y ≤ d := EReal.coe_le_coe_iff.1 hD
        right; right; left
        exact ⟨not_skip_coe _ _, coe_mul_le (by nlinarith)⟩
      | top =>
        right; right; left
        exact ⟨by simp [SkipMul, ha.ne], by rw [EReal.coe_mul_top_of_neg ha]; exact bot_le⟩

theorem mul_corner_lo {A B C D : EReal} {x y : ℝ} (hA : A ≤ x) (hB : (x : EReal) ≤ B)
    (hC : C ≤ y) (hD : (y : EReal) ≤ D) :
    AllSkip A B C D ∨ GoodLo A C (x * y) ∨ GoodLo A D (x * y) ∨ GoodLo B C (x * y) ∨
      GoodLo B D (x * y) := by
  rcases le_total 0 y with hy | hy
  · exact mul_corner_lo_nonneg hA hB hC hD hy
  have h := mul_corner_lo_nonneg (A := -B) (B := -A) (C := -D) (D := -C) (x := -x) (y := -y)
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hB)
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hA)
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hD)
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hC) (by linarith)
  have e : ∀ a b : EReal, GoodLo (-a) (-b) (-x * -y) ↔ GoodLo a b (x * y) := by
    intro a b
    simp only [GoodLo, skipMul_neg_left, skipMul_neg_right, neg_mul_neg]
  rw [e, e, e, e] at h
  rcases h with ⟨h1, h2, h3, h4⟩ | h | h | h | h
  · left
    rw [skipMul_neg_left, skipMul_neg_right] at h1 h2 h3 h4
    exact ⟨h4, h3, h2, h1⟩
  · right; right; right; right; exact h
  · right; right; right; left; exact h
  · right; right; left; exact h
  · right; left; exact h

theorem mul_corner_hi {A B C D : EReal} {x y : ℝ} (hA : A ≤ x) (hB : (x : EReal) ≤ B)
    (hC : C ≤ y) (hD : (y : EReal) ≤ D) :
    AllSkip A B C D ∨ GoodHi A C (x * y) ∨ GoodHi A D (x * y) ∨ GoodHi B C (x * y) ∨
      GoodHi B D (x * y) := by
  have h := mul_corner_lo (A := A) (B := B) (C := -D) (D := -C) (x := x) (y := -y) hA hB
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hD)
    (by rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hC)
  have e : ∀ a b : EReal, GoodLo a (-b) (x * -y) ↔ GoodHi a b (x * y) := by
    intro a b
    simp only [GoodLo, GoodHi, skipMul_neg_right, mul_neg, EReal.coe_neg, EReal.neg_le_neg_iff]
  rw [e, e, e, e] at h
  rcases h with ⟨h1, h2, h3, h4⟩ | h | h | h | h
  · left
    rw [skipMul_neg_right] at h1 h2 h3 h4
    exact ⟨h2, h1, h4, h3⟩
  · right; right; left; exact h
  · right; left; exact h
  · right; right; right; right; exact h
  · right; right; right; left; exact h

/-! ### Division corners -/

/-- Not `±∞ / ±∞`, nonzero divisor, and bounds `p` from below. -/
def GoodDLo (a b : EReal) (p : ℝ) : Prop :=
  ¬ ((a = ⊤ ∨ a = ⊥) ∧ (b = ⊤ ∨ b = ⊥)) ∧ b ≠ 0 ∧ a / b ≤ (p : EReal)
/-- Not `±∞ / ±∞`, nonzero divisor, and bounds `p` from above. -/
def GoodDHi (a b : EReal) (p : ℝ) : Prop :=
  ¬ ((a = ⊤ ∨ a = ⊥) ∧ (b = ⊤ ∨ b = ⊥)) ∧ b ≠ 0 ∧ (p : EReal) ≤ a / b

theorem rdiv_le_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := (div_le_div_iff₀ hb hd).2 h

theorem rdiv_le_neg {a b c d : ℝ} (hb : b < 0) (hd : d < 0) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [← neg_div_neg_eq a b, ← neg_div_neg_eq c d]
  exact rdiv_le_pos (neg_pos.2 hb) (neg_pos.2 hd) (by nlinarith)

theorem coe_div_le {a b p : ℝ} (h : a / b ≤ p) : (a : EReal) / (b : EReal) ≤ (p : EReal) := by
  rw [← EReal.coe_div]; exact EReal.coe_le_coe h

theorem coe_le_div {a b p : ℝ} (h : p ≤ a / b) : (p : EReal) ≤ (a : EReal) / (b : EReal) := by
  rw [← EReal.coe_div]; exact EReal.coe_le_coe h

theorem div_corner_pos {A B C D : EReal} {x y : ℝ} (hA : A ≤ x) (hB : (x : EReal) ≤ B)
    (hC : C ≤ y) (hD : (y : EReal) ≤ D) (hC0 : 0 < C) :
    (GoodDLo A C (x / y) ∨ GoodDLo A D (x / y)) ∧
    (GoodDHi B C (x / y) ∨ GoodDHi B D (x / y)) := by
  induction C using EReal.rec with
  | bot => exact absurd hC0 (by simp)
  | top => exact absurd hC (by simp)
  | coe c =>
  have hc : 0 < c := EReal.coe_pos.1 hC0
  have hcy : c ≤ y := EReal.coe_le_coe_iff.1 hC
  have hy : 0 < y := lt_of_lt_of_le hc hcy
  have hc0 : (c : EReal) ≠ 0 := by simp [hc.ne']
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hD; exact absurd (EReal.coe_le_coe_iff.1 (by simpa using hD)) (not_le.2 hy)
  have hcfin : ¬ ((c : EReal) = ⊤ ∨ (c : EReal) = ⊥) := by simp
  constructor
  · induction A using EReal.rec with
    | top => exact absurd hA (by simp)
    | bot =>
      left
      exact ⟨fun h => hcfin h.2, hc0, by
        rw [EReal.bot_div_of_pos_ne_top hC0 (EReal.coe_ne_top _)]; exact bot_le⟩
    | coe a =>
      have hax : a ≤ x := EReal.coe_le_coe_iff.1 hA
      have hafin : ¬ ((a : EReal) = ⊤ ∨ (a : EReal) = ⊥) := by simp
      rcases le_or_gt 0 a with ha | ha
      · right
        refine ⟨fun h => hafin h.1, hD0, ?_⟩
        induction D using EReal.rec with
        | bot => exact absurd hD (by simp)
        | top => rw [EReal.div_top]; exact EReal.coe_nonneg.2 (div_nonneg (by linarith) hy.le)
        | coe d =>
          have hyd : y ≤ d := EReal.coe_le_coe_iff.1 hD
          exact coe_div_le (rdiv_le_pos (by linarith) hy (by nlinarith))
      · left
        exact ⟨fun h => hafin h.1, hc0, coe_div_le (rdiv_le_pos hc hy (by nlinarith))⟩
  · induction B using EReal.rec with
    | bot => exact absurd hB (by simp)
    | top =>
      left
      exact ⟨fun h => hcfin h.2, hc0, by
        rw [EReal.top_div_of_pos_ne_top hC0 (EReal.coe_ne_top _)]; exact le_top⟩
    | coe b =>
      have hxb : x ≤ b := EReal.coe_le_coe_iff.1 hB
      have hbfin : ¬ ((b : EReal) = ⊤ ∨ (b : EReal) = ⊥) := by simp
      rcases le_or_gt 0 b with hb | hb
      · left
        exact ⟨fun h => hbfin h.1, hc0, coe_le_div (rdiv_le_pos hy hc (by nlinarith))⟩
      · right
        refine ⟨fun h => hbfin h.1, hD0, ?_⟩
        induction D using EReal.rec with
        | bot => exact absurd hD (by simp)
        | top =>
          rw [EReal.div_top]
          exact EReal.coe_nonpos.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hy.le)
        | coe d =>
          have hyd : y ≤ d := EReal.coe_le_coe_iff.1 hD
          exact coe_le_div (rdiv_le_pos hy (by linarith) (by nlinarith))

theorem div_corner_neg {A B C D : EReal} {x y : ℝ} (hA : A ≤ x) (hB : (x : EReal) ≤ B)
    (hC : C ≤ y) (hD : (y : EReal) ≤ D) (hD0 : D < 0) :
    (GoodDLo B C (x / y) ∨ GoodDLo B D (x / y)) ∧
    (GoodDHi A C (x / y) ∨ GoodDHi A D (x / y)) := by
  induction D using EReal.rec with
  | bot => exact absurd hD (by simp)
  | top => exact absurd hD0 (by simp)
  | coe d =>
  have hd : d < 0 := EReal.coe_neg'.1 hD0
  have hyd : y ≤ d := EReal.coe_le_coe_iff.1 hD
  have hy : y < 0 := lt_of_le_of_lt hyd hd
  have hd0 : (d : EReal) ≠ 0 := by simp [hd.ne]
  have hC0 : C ≠ 0 := by
    intro h; rw [h] at hC; exact absurd (EReal.coe_le_coe_iff.1 (by simpa using hC)) (not_le.2 hy)
  have hdfin : ¬ ((d : EReal) = ⊤ ∨ (d : EReal) = ⊥) := by simp
  constructor
  · induction B using EReal.rec with
    | bot => exact absurd hB (by simp)
    | top =>
      right
      exact ⟨fun h => hdfin h.2, hd0, by
        rw [EReal.top_div_of_neg_ne_bot hD0 (EReal.coe_ne_bot _)]; exact bot_le⟩
    | coe b =>
      have hxb : x ≤ b := EReal.coe_le_coe_iff.1 hB
      have hbfin : ¬ ((b : EReal) = ⊤ ∨ (b : EReal) = ⊥) := by simp
      rcases le_or_gt b 0 with hb | hb
      · left
        refine ⟨fun h => hbfin h.1, hC0, ?_⟩
        induction C using EReal.rec with
        | top => exact absurd hC (by simp)
        | bot =>
          rw [EReal.div_bot]
          exact EReal.coe_nonneg.2 (div_nonneg_of_nonpos (by linarith) hy.le)
        | coe c =>
          have hcy : c ≤ y := EReal.coe_le_coe_iff.1 hC
          exact coe_div_le (rdiv_le_neg (by linarith) hy (by nlinarith))
      · right
        exact ⟨fun h => hbfin h.1, hd0, coe_div_le (rdiv_le_neg hd hy (by nlinarith))⟩
  · induction A using EReal.rec with
    | top => exact absurd hA (by simp)
    | bot =>
      right
      exact ⟨fun h => hdfin h.2, hd0, by
        rw [EReal.bot_div_of_neg_ne_bot hD0 (EReal.coe_ne_bot _)]; exact le_top⟩
    | coe a =>
      have hax : a ≤ x := EReal.coe_le_coe_iff.1 hA
      have hafin : ¬ ((a : EReal) = ⊤ ∨ (a : EReal) = ⊥) := by simp
      rcases le_or_gt 0 a with ha | ha
      · left
        refine ⟨fun h => hafin h.1, hC0, ?_⟩
        induction C using EReal.rec with
        | top => exact absurd hC (by simp)
        | bot =>
          rw [EReal.div_bot]
          exact EReal.coe_nonpos.2 (div_nonpos_of_nonneg_of_nonpos (by linarith) hy.le)
        | coe c =>
          have hcy : c ≤ y := EReal.coe_le_coe_iff.1 hC
          exact coe_le_div (rdiv_le_neg hy (by linarith) (by nlinarith))
      · right
        exact ⟨fun h => hafin h.1, hd0, coe_le_div (rdiv_le_neg hy hd (by nlinarith))⟩

end RealFP

end
