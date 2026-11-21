/-
Example: `sin` bounds on the whole interval `[1, 2]`.

`[1, 2]` contains the maximum `π/2`, so the upper end is exactly `1`; it avoids
every minimum `3π/2 + 2nπ`, so the lower end is `min (sinDown 1) (sinDown 2) = sinDown 1`.
The endpoint values are checked by `decide +kernel` (the Lean kernel runs the
rational Ziv specification, not the C code; no `native_decide` axiom). The
`fmin` is resolved with `bitsToRat?_fmin`, since the kernel cannot evaluate
`Float.lt`.
-/
import RealFPMathlib.Trig

open Interval64 Interval64.Spec RealFP RealFP.Trig

namespace RealFP.Examples.Trig

/-- `sin [1, 2]`. -/
def S : Interval64 := Interval64.sin (ofRatInterval 1 2)

/-- `sinDown 2` (round-down of `sin 2 ≈ 0.909297…`). -/
def sin2Lo : ℚ := 8190223105242181 / 9007199254740992
/-- `sinDown 1` (round-down of `sin 1 ≈ 0.841470…`). -/
def sin1Lo : ℚ := 3789648413623927 / 4503599627370496

theorem I_lo : bitsToRat? (ofRatInterval 1 2).lo.toBits = some 1 := by decide +kernel
theorem I_hi : bitsToRat? (ofRatInterval 1 2).hi.toBits = some 2 := by decide +kernel
theorem I_lo_nan : (ofRatInterval 1 2).lo.isNaN = false := by decide +kernel
theorem I_hi_nan : (ofRatInterval 1 2).hi.isNaN = false := by decide +kernel
theorem avoids_min : Interval64.Trig.avoids 1 2 3 = true := by decide +kernel
theorem not_avoids_max : Interval64.Trig.avoids 1 2 1 = false := by decide +kernel
theorem sinDown_one :
    bitsToRat? (Directed.sinDown (ofRatInterval 1 2).lo).toBits = some sin1Lo := by
  decide +kernel
theorem sinDown_two :
    bitsToRat? (Directed.sinDown (ofRatInterval 1 2).hi).toBits = some sin2Lo := by
  decide +kernel

theorem S_eq : S = ⟨fmin (Directed.sinDown (ofRatInterval 1 2).lo)
    (Directed.sinDown (ofRatInterval 1 2).hi), plusOne⟩ := by
  unfold S Interval64.sin
  rw [I_lo_nan, I_hi_nan]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [I_lo, I_hi]
  simp only [avoids_min, not_avoids_max, ↓reduceIte, Bool.false_eq_true]

theorem S_lo : bitsToRat? S.lo.toBits = some sin1Lo := by
  rw [S_eq]
  obtain ⟨q, hq, h1, h2⟩ :=
    Interval64Proofs.IntervalMem.bitsToRat?_fmin sinDown_one sinDown_two
  have hf : fmin (Directed.sinDown (ofRatInterval 1 2).lo) (Directed.sinDown (ofRatInterval 1 2).hi)
      = Directed.sinDown (ofRatInterval 1 2).lo ∨
      fmin (Directed.sinDown (ofRatInterval 1 2).lo) (Directed.sinDown (ofRatInterval 1 2).hi)
      = Directed.sinDown (ofRatInterval 1 2).hi := by
    unfold fmin; split <;> simp
  rcases hf with hf | hf
  · show bitsToRat? (fmin _ _).toBits = _
    rw [hf]; exact sinDown_one
  · rw [hf, sinDown_two] at hq
    cases hq
    exact absurd h1 (by unfold sin1Lo sin2Lo; decide +kernel)

theorem S_hi : bitsToRat? S.hi.toBits = some 1 := by decide +kernel

/-- Every `x ∈ [1, 2]` has `sinDown 1 ≤ sin x ≤ 1` (via `sin_mem_toSet`). -/
theorem sin_mem_one_two {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    Real.sin x ∈ Set.Icc (sin1Lo : ℝ) 1 := by
  have hx : x ∈ (ofRatInterval 1 2).toSet :=
    mem_toSet_ofRatInterval (by push_cast; exact h1) (by push_cast; exact h2)
  have h := sin_mem_toSet hx
  rw [show Interval64.sin (ofRatInterval 1 2) = S from rfl, toSet_eq_Icc S_lo S_hi] at h
  push_cast at h
  exact h

/-- `0.84147098480789 < sin x ≤ 1` for all `x ∈ [1, 2]` (`sin 1 = 0.841470984807896…`). -/
theorem sin_bounds_one_two {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    (0.84147098480789 : ℝ) < Real.sin x ∧ Real.sin x ≤ 1 := by
  obtain ⟨l, u⟩ := sin_mem_one_two h1 h2
  refine ⟨lt_of_lt_of_le ?_ l, u⟩
  unfold sin1Lo; norm_num

end RealFP.Examples.Trig
