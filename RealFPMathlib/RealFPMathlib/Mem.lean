/-
Real membership (enclosure) for `Interval64` `+ - * / sqrt`.

`add` / `sub` hold with no finiteness assumption (infinite endpoints are
allowed, as in the core). `mul`, `div` and `sqrt` assume finite endpoints, as
the core theorems do; `div` needs only `y ≠ 0` (if `Y ∋ 0` the result is
`whole`, which contains everything).

Proof idea: a real `x ∈ X.toSet` is bracketed by rational points of `X`
(`exists_rat_le_of_mem` / `exists_rat_ge_of_mem`, or the endpoints). The core
theorems put the corresponding rational results into the computed interval,
and `toSet` is convex.
-/
import RealFPMathlib.Basic

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.IntervalMem Interval64Proofs.Sub Interval64Proofs.Div
open Interval64Proofs.TightIv Interval64Proofs.TightSqrt

namespace RealFP

theorem add_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    x + y ∈ (X + Y).toSet := by
  obtain ⟨p₁, hp₁, h₁⟩ := exists_rat_le_of_mem hx
  obtain ⟨q₁, hq₁, h₂⟩ := exists_rat_ge_of_mem hx
  obtain ⟨p₂, hp₂, h₃⟩ := exists_rat_le_of_mem hy
  obtain ⟨q₂, hq₂, h₄⟩ := exists_rat_ge_of_mem hy
  exact mem_toSet_of_rat_bounds (add_mem_iv hp₁ hp₂) (add_mem_iv hq₁ hq₂)
    (by push_cast; linarith) (by push_cast; linarith)

theorem sub_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet) :
    x - y ∈ (X - Y).toSet := by
  obtain ⟨p₁, hp₁, h₁⟩ := exists_rat_le_of_mem hx
  obtain ⟨q₁, hq₁, h₂⟩ := exists_rat_ge_of_mem hx
  obtain ⟨p₂, hp₂, h₃⟩ := exists_rat_le_of_mem hy
  obtain ⟨q₂, hq₂, h₄⟩ := exists_rat_ge_of_mem hy
  exact mem_toSet_of_rat_bounds (sub_mem_iv hp₁ hq₂) (sub_mem_iv hq₁ hp₂)
    (by push_cast; linarith) (by push_cast; linarith)

/-- Endpoints of a finite interval that contains a real are points of it. -/
theorem memIv_endpoints {X : Interval64} {a b : ℚ} {x : ℝ}
    (ha : bitsToRat? X.lo.toBits = some a) (hb : bitsToRat? X.hi.toBits = some b)
    (hx : x ∈ X.toSet) : MemIv a X ∧ MemIv b X ∧ (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) := by
  rw [toSet_eq_Icc ha hb] at hx
  have hab : (a : ℝ) ≤ b := le_trans hx.1 hx.2
  refine ⟨cast_mem_toSet_iff.1 ?_, cast_mem_toSet_iff.1 ?_, hx.1, hx.2⟩ <;>
    rw [toSet_eq_Icc ha hb]
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩

theorem exists_corner_le {a b c d : ℝ} {x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b)
    (hy1 : c ≤ y) (hy2 : y ≤ d) :
    a * c ≤ x * y ∨ a * d ≤ x * y ∨ b * c ≤ x * y ∨ b * d ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · rcases le_total 0 a with ha | ha
    · left; nlinarith [mul_nonneg (sub_nonneg.2 hx1) hy, mul_nonneg ha (sub_nonneg.2 hy1)]
    · right; left
      nlinarith [mul_nonneg (sub_nonneg.2 hx1) hy, mul_nonneg (neg_nonneg.2 ha) (sub_nonneg.2 hy2)]
  · rcases le_total 0 b with hb | hb
    · right; right; left
      nlinarith [mul_nonneg (sub_nonneg.2 hx2) (neg_nonneg.2 hy), mul_nonneg hb (sub_nonneg.2 hy1)]
    · right; right; right
      nlinarith [mul_nonneg (sub_nonneg.2 hx2) (neg_nonneg.2 hy),
        mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 hy2)]

theorem exists_corner_ge {a b c d : ℝ} {x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b)
    (hy1 : c ≤ y) (hy2 : y ≤ d) :
    x * y ≤ a * c ∨ x * y ≤ a * d ∨ x * y ≤ b * c ∨ x * y ≤ b * d := by
  rcases le_total 0 y with hy | hy
  · rcases le_total 0 b with hb | hb
    · right; right; right
      nlinarith [mul_nonneg (sub_nonneg.2 hx2) hy, mul_nonneg hb (sub_nonneg.2 hy2)]
    · right; right; left
      nlinarith [mul_nonneg (sub_nonneg.2 hx2) hy, mul_nonneg (neg_nonneg.2 hb) (sub_nonneg.2 hy1)]
  · rcases le_total 0 a with ha | ha
    · right; left
      nlinarith [mul_nonneg (sub_nonneg.2 hx1) (neg_nonneg.2 hy), mul_nonneg ha (sub_nonneg.2 hy2)]
    · left
      nlinarith [mul_nonneg (sub_nonneg.2 hx1) (neg_nonneg.2 hy),
        mul_nonneg (neg_nonneg.2 ha) (sub_nonneg.2 hy1)]

theorem mul_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q)
    (hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    x * y ∈ (X * Y).toSet := by
  obtain ⟨a, ha⟩ := hXlo; obtain ⟨b, hb⟩ := hXhi
  obtain ⟨c, hc⟩ := hYlo; obtain ⟨d, hd⟩ := hYhi
  obtain ⟨ma, mb, hax, hxb⟩ := memIv_endpoints ha hb hx
  obtain ⟨mc, md, hcy, hyd⟩ := memIv_endpoints hc hd hy
  have k : ∀ u v : ℚ, MemIv u X → MemIv v Y → MemIv (u * v) (X * Y) := fun u v hu hv =>
    mul_mem_iv hu hv ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  have lo : ∃ p : ℚ, MemIv p (X * Y) ∧ (p : ℝ) ≤ x * y := by
    rcases exists_corner_le hax hxb hcy hyd with h | h | h | h
    · exact ⟨_, k _ _ ma mc, by push_cast; exact h⟩
    · exact ⟨_, k _ _ ma md, by push_cast; exact h⟩
    · exact ⟨_, k _ _ mb mc, by push_cast; exact h⟩
    · exact ⟨_, k _ _ mb md, by push_cast; exact h⟩
  have hi : ∃ q : ℚ, MemIv q (X * Y) ∧ x * y ≤ (q : ℝ) := by
    rcases exists_corner_ge hax hxb hcy hyd with h | h | h | h
    · exact ⟨_, k _ _ ma mc, by push_cast; exact h⟩
    · exact ⟨_, k _ _ ma md, by push_cast; exact h⟩
    · exact ⟨_, k _ _ mb mc, by push_cast; exact h⟩
    · exact ⟨_, k _ _ mb md, by push_cast; exact h⟩
  obtain ⟨p, hp, hpl⟩ := lo
  obtain ⟨q, hq, hqh⟩ := hi
  exact mem_toSet_of_rat_bounds hp hq hpl hqh

/-! ### Division -/

theorem exists_rat_pos_le {Y : Interval64} {y : ℝ} (hy : y ∈ Y.toSet) (hy0 : 0 < y) :
    ∃ v : ℚ, MemIv v Y ∧ (0 : ℝ) < v ∧ (v : ℝ) ≤ y := by
  obtain ⟨p, hp, hpy⟩ := exists_rat_le_of_mem hy
  by_cases h : (0 : ℝ) < p
  · exact ⟨p, hp, h, hpy⟩
  · obtain ⟨q, hq0, hqy⟩ := exists_rat_btwn hy0
    refine ⟨q, cast_mem_toSet_iff.1 (mem_toSet_of_between (cast_mem_toSet_iff.2 hp) hy
      (by linarith [not_lt.1 h]) hqy.le), hq0, hqy.le⟩

theorem exists_rat_neg_ge {Y : Interval64} {y : ℝ} (hy : y ∈ Y.toSet) (hy0 : y < 0) :
    ∃ v : ℚ, MemIv v Y ∧ (v : ℝ) < 0 ∧ y ≤ (v : ℝ) := by
  obtain ⟨p, hp, hpy⟩ := exists_rat_ge_of_mem hy
  by_cases h : (p : ℝ) < 0
  · exact ⟨p, hp, h, hpy⟩
  · obtain ⟨q, hyq, hq0⟩ := exists_rat_btwn hy0
    refine ⟨q, cast_mem_toSet_iff.1 (mem_toSet_of_between hy (cast_mem_toSet_iff.2 hp)
      hyq.le (by linarith [not_lt.1 h])), hq0, hyq.le⟩

theorem div_le_div_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := (div_le_div_iff₀ hb hd).2 h

theorem div_le_div_neg {a b c d : ℝ} (hb : b < 0) (hd : d < 0) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [← neg_div_neg_eq a b, ← neg_div_neg_eq c d]
  exact div_le_div_pos (neg_pos.2 hb) (neg_pos.2 hd) (by nlinarith)

theorem div_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet)
    (hy0 : y ≠ 0)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q)
    (hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    x / y ∈ (X / Y).toSet := by
  obtain ⟨a, ha⟩ := hXlo; obtain ⟨b, hb⟩ := hXhi
  obtain ⟨ma, mb, hax, hxb⟩ := memIv_endpoints ha hb hx
  have k : ∀ u v : ℚ, MemIv u X → MemIv v Y → (v : ℝ) ≠ 0 → MemIv (u / v) (X / Y) :=
    fun u v hu hv hv0 => div_mem_iv hu hv (by exact_mod_cast hv0) ⟨a, ha⟩ ⟨b, hb⟩ hYlo hYhi
  have lo : ∃ p : ℚ, MemIv p (X / Y) ∧ (p : ℝ) ≤ x / y := by
    rcases lt_or_gt_of_ne hy0 with hn | hp
    · rcases le_total (b : ℝ) 0 with hb0 | hb0
      · obtain ⟨v, hv, hvy⟩ := exists_rat_le_of_mem hy
        have hv0 : (v : ℝ) < 0 := lt_of_le_of_lt hvy hn
        refine ⟨_, k b v mb hv hv0.ne, ?_⟩
        push_cast
        exact div_le_div_neg hv0 hn (by nlinarith [mul_nonneg (sub_nonneg.2 hvy) (neg_nonneg.2 hb0), mul_nonneg (sub_nonneg.2 hxb) (neg_nonneg.2 hv0.le)])
      · obtain ⟨v, hv, hv0, hyv⟩ := exists_rat_neg_ge hy hn
        refine ⟨_, k b v mb hv hv0.ne, ?_⟩
        push_cast
        exact div_le_div_neg hv0 hn (by nlinarith [mul_nonneg (sub_nonneg.2 hyv) hb0, mul_nonneg (sub_nonneg.2 hxb) (neg_nonneg.2 hv0.le)])
    · rcases le_total 0 (a : ℝ) with ha0 | ha0
      · obtain ⟨v, hv, hyv⟩ := exists_rat_ge_of_mem hy
        have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hp hyv
        refine ⟨_, k a v ma hv hv0.ne', ?_⟩
        push_cast
        exact div_le_div_pos hv0 hp (by nlinarith [mul_nonneg (sub_nonneg.2 hyv) ha0, mul_nonneg (sub_nonneg.2 hax) hv0.le])
      · obtain ⟨v, hv, hv0, hvy⟩ := exists_rat_pos_le hy hp
        refine ⟨_, k a v ma hv hv0.ne', ?_⟩
        push_cast
        exact div_le_div_pos hv0 hp (by nlinarith [mul_nonneg (sub_nonneg.2 hvy) (neg_nonneg.2 ha0), mul_nonneg (sub_nonneg.2 hax) hv0.le])
  have hi : ∃ q : ℚ, MemIv q (X / Y) ∧ x / y ≤ (q : ℝ) := by
    rcases lt_or_gt_of_ne hy0 with hn | hp
    · rcases le_total 0 (a : ℝ) with ha0 | ha0
      · obtain ⟨v, hv, hvy⟩ := exists_rat_le_of_mem hy
        have hv0 : (v : ℝ) < 0 := lt_of_le_of_lt hvy hn
        refine ⟨_, k a v ma hv hv0.ne, ?_⟩
        push_cast
        exact div_le_div_neg hn hv0 (by nlinarith [mul_nonneg (sub_nonneg.2 hvy) ha0, mul_nonneg (sub_nonneg.2 hax) (neg_nonneg.2 hv0.le)])
      · obtain ⟨v, hv, hv0, hyv⟩ := exists_rat_neg_ge hy hn
        refine ⟨_, k a v ma hv hv0.ne, ?_⟩
        push_cast
        exact div_le_div_neg hn hv0 (by nlinarith [mul_nonneg (sub_nonneg.2 hyv) (neg_nonneg.2 ha0), mul_nonneg (sub_nonneg.2 hax) (neg_nonneg.2 hv0.le)])
    · rcases le_total 0 (b : ℝ) with hb0 | hb0
      · obtain ⟨v, hv, hv0, hvy⟩ := exists_rat_pos_le hy hp
        refine ⟨_, k b v mb hv hv0.ne', ?_⟩
        push_cast
        exact div_le_div_pos hp hv0 (by nlinarith [mul_nonneg (sub_nonneg.2 hvy) hb0, mul_nonneg (sub_nonneg.2 hxb) hv0.le])
      · obtain ⟨v, hv, hyv⟩ := exists_rat_ge_of_mem hy
        have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hp hyv
        refine ⟨_, k b v mb hv hv0.ne', ?_⟩
        push_cast
        exact div_le_div_pos hp hv0 (by nlinarith [mul_nonneg (sub_nonneg.2 hyv) (neg_nonneg.2 hb0), mul_nonneg (sub_nonneg.2 hxb) hv0.le])
  obtain ⟨p, hp, hpl⟩ := lo
  obtain ⟨q, hq, hqh⟩ := hi
  exact mem_toSet_of_rat_bounds hp hq hpl hqh

/-! ### Square root -/

/-- `Real.sqrt` enclosure for finite-endpoint intervals (negative parts are clipped). -/
theorem sqrt_mem_toSet {X : Interval64} {x : ℝ} (hx : x ∈ X.toSet) (hx0 : 0 ≤ x)
    (hXlo : ∃ q, bitsToRat? X.lo.toBits = some q)
    (hXhi : ∃ q, bitsToRat? X.hi.toBits = some q) :
    Real.sqrt x ∈ (Interval64.sqrt X).toSet := by
  obtain ⟨l, hl⟩ := hXlo; obtain ⟨h, hh⟩ := hXhi
  obtain ⟨-, -, hlx, hxh⟩ := memIv_endpoints hl hh hx
  have hFin : FinIv X l h := ⟨hl, hh, by exact_mod_cast le_trans hlx hxh⟩
  have hh0 : (0 : ℚ) ≤ h := by exact_mod_cast le_trans hx0 hxh
  obtain ⟨⟨ρ, hρ, hρ0, hρsq, -⟩, ⟨σ, hσ, hσ0, hσsq, -⟩⟩ := sqrt_iv_tight hFin hh0
  rw [mem_toSet, hρ, hσ, loR_rat, hiR_rat]
  constructor
  · have hle : ((ρ * ρ : ℚ) : ℝ) ≤ x := by
      have : ρ * ρ ≤ (if l < 0 then 0 else l) := hρsq
      split_ifs at this with hl0
      · exact le_trans (by exact_mod_cast this) hx0
      · exact le_trans (by exact_mod_cast this) hlx
    have hρ0' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ0
    calc (ρ : ℝ) = Real.sqrt ((ρ : ℝ) * ρ) := (Real.sqrt_mul_self hρ0').symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by exact_mod_cast hle)
  · have hσ0' : (0 : ℝ) ≤ σ := by exact_mod_cast hσ0
    calc Real.sqrt x ≤ Real.sqrt ((σ : ℝ) * σ) :=
          Real.sqrt_le_sqrt (le_trans hxh (by exact_mod_cast hσsq))
      _ = σ := Real.sqrt_mul_self hσ0'

end RealFP
