/-
`x ∈ X` for reals and the new conversions (`Interval64.Conv`).

* `Membership ℝ Interval64`: `x ∈ X` is `x ∈ X.toSet` (`RealFP.mem_iff`, simp).
* Literal / cast enclosures: `natCast_mem`, `ofNat_mem`, `zero_mem`, `one_mem`,
  `intCast_mem`, `ratCoe_mem`, `ofScientific_mem` (`(0.1 : ℝ) ∈ (0.1 : Interval64)`),
  `floatCoe_mem` (`f.toReal? = some r → r ∈ (f : Interval64)`).
* The main enclosure theorems restated with `∈` in `RealFP.Iv`
  (`Iv.add_mem`, `Iv.mem_mul`, `Iv.mem_div`, `Iv.mem_sqrt`, …, `Iv.cos_mem`).
  `Iv.mem_mul` / `Iv.mem_div` / `Iv.mem_sqrt` need no finiteness hypotheses; the
  old `Iv.mul_mem` / `Iv.div_mem` / `Iv.sqrt_mem` (with them) are deprecated aliases.
-/
import RealFPMathlib.Tight
import RealFPMathlib.Mem
import RealFPMathlib.Transc
import RealFPMathlib.Trig
import RealFPMathlib.Unbounded

open Interval64 Interval64.Spec

namespace RealFP

instance : Membership ℝ Interval64 := ⟨fun I x => x ∈ I.toSet⟩

@[simp] theorem mem_iff {I : Interval64} {x : ℝ} : x ∈ I ↔ x ∈ I.toSet := Iff.rfl

/-! ### Conversions enclose their exact value -/

theorem ratCoe_mem (q : ℚ) : (q : ℝ) ∈ (q : Interval64) := mem_toSet_ofRat q

theorem natCast_mem (n : ℕ) : (n : ℝ) ∈ (n : Interval64) := by
  have h := mem_toSet_ofRat (n : ℚ)
  rw [Rat.cast_natCast] at h
  exact h

theorem intCast_mem (z : ℤ) : (z : ℝ) ∈ (z : Interval64) := by
  have h := mem_toSet_ofRat (z : ℚ)
  rw [Rat.cast_intCast] at h
  exact h

theorem ofNat_mem (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℝ) ∈ (OfNat.ofNat n : Interval64) := by
  exact natCast_mem n

theorem zero_mem : (0 : ℝ) ∈ (0 : Interval64) := by
  simpa using natCast_mem 0

theorem one_mem : (1 : ℝ) ∈ (1 : Interval64) := by
  simpa using natCast_mem 1

/-- A decimal literal encloses its exact rational value, e.g. `(0.1 : ℝ) ∈ (0.1 : Interval64)`. -/
theorem ofScientific_mem (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℝ) ∈ (OfScientific.ofScientific m s e : Interval64) := by
  have h := mem_toSet_ofRat (OfScientific.ofScientific m s e : ℚ)
  rw [Rat.cast_ofScientific] at h
  exact h

/-- A `Float` coerces to the point interval of its exact value (finite case). -/
theorem floatCoe_mem {f : Float} {r : ℝ} (h : f.toReal? = some r) : r ∈ (f : Interval64) := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.mp h
  show (q : ℝ) ∈ (⟨f, f⟩ : Interval64).toSet
  rw [toSet_eq_Icc (I := ⟨f, f⟩) hq hq]
  exact ⟨le_refl _, le_refl _⟩

/-! ### Enclosure theorems with `∈` -/

namespace Iv

theorem add_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) : x + y ∈ X + Y :=
  add_mem_toSet hx hy

theorem sub_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) : x - y ∈ X - Y :=
  sub_mem_toSet hx hy

/-- `x * y ∈ X * Y`, no finiteness assumption (half-lines and `whole` allowed). -/
theorem mem_mul {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) : x * y ∈ X * Y :=
  mem_toSet_mul hx hy

/-- `x / y ∈ X / Y` for `y ≠ 0`, no finiteness assumption. -/
theorem mem_div {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) (hy0 : y ≠ 0) :
    x / y ∈ X / Y :=
  mem_toSet_div hx hy hy0

/-- `√x ∈ sqrt X` for `0 ≤ x`, no finiteness assumption. -/
theorem mem_sqrt {X : Interval64} {x : ℝ} (hx : x ∈ X) (hx0 : 0 ≤ x) :
    Real.sqrt x ∈ Interval64.sqrt X :=
  mem_toSet_sqrt hx hx0

@[deprecated "use RealFP.Iv.mem_mul (no finiteness hypotheses)" (since := "2026-11-21")]
theorem mul_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y)
    (_hXlo : ∃ q, bitsToRat? X.lo.toBits = some q) (_hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (_hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q) (_hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    x * y ∈ X * Y :=
  mem_mul hx hy

@[deprecated "use RealFP.Iv.mem_div (no finiteness hypotheses)" (since := "2026-11-21")]
theorem div_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) (hy0 : y ≠ 0)
    (_hXlo : ∃ q, bitsToRat? X.lo.toBits = some q) (_hXhi : ∃ q, bitsToRat? X.hi.toBits = some q)
    (_hYlo : ∃ q, bitsToRat? Y.lo.toBits = some q) (_hYhi : ∃ q, bitsToRat? Y.hi.toBits = some q) :
    x / y ∈ X / Y :=
  mem_div hx hy hy0

@[deprecated "use RealFP.Iv.mem_sqrt (no finiteness hypotheses)" (since := "2026-11-21")]
theorem sqrt_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) (hx0 : 0 ≤ x)
    (_hXlo : ∃ q, bitsToRat? X.lo.toBits = some q) (_hXhi : ∃ q, bitsToRat? X.hi.toBits = some q) :
    Real.sqrt x ∈ Interval64.sqrt X :=
  mem_sqrt hx hx0

theorem exp_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.exp x ∈ Interval64.exp X :=
  Transc.exp_mem_toSet hx

theorem log_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) (hx0 : 0 < x) :
    Real.log x ∈ Interval64.log X :=
  Transc.log_mem_toSet hx hx0

theorem sin_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.sin x ∈ Interval64.sin X :=
  Trig.sin_mem_toSet hx

theorem cos_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.cos x ∈ Interval64.cos X :=
  Trig.cos_mem_toSet hx

end Iv

end RealFP
