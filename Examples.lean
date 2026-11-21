/-
Examples you can run:  lake lean Examples.lean
(`lake lean` loads the compiled C kernels; plain `lean` does not.)
-/
import Interval64
import Interval64Proofs

open Interval64 Interval64.Directed Interval64.Spec
open Interval64Proofs.FloatBits Interval64Proofs.IntervalMem Interval64Proofs.OfRat

/-- Exact rational value of a double (`none` for ±inf / NaN). -/
def ex (f : Float) : Option Rat := bitsToRat? f.toBits
def exIv (i : Interval64) : Option Rat × Option Rat := (ex i.lo, ex i.hi)

/-! ## 1. Directed rounding at runtime (AVX-512 C kernels) -/
#eval (addDown 0.1 0.2, addUp 0.1 0.2)          -- prints alike (6 digits)
#eval (ex (addDown 0.1 0.2), ex (addUp 0.1 0.2))  -- exact values: differ by 1 ulp
#eval (addUp 0.1 0.2).toBits - (addDown 0.1 0.2).toBits  -- 1 (adjacent doubles)
#eval (divDown 1.0 3.0, divUp 1.0 3.0)
#eval (sqrtDown 2.0, sqrtUp 2.0)
#eval (addUp 1e308 1e308, ex (addDown 1e308 1e308) == ex 1.7976931348623157e308) -- inf, maxFinite

/-! ## 2. Intervals -/
#eval ofBounds 1.0 2.0 * ofBounds (-3.0) 4.0
#eval ofBounds 1.0 2.0 / ofBounds (-1.0) 1.0      -- divisor contains 0 → whole
#eval Interval64.sqrt (ofBounds (-1.0) 4.0)       -- negative part clipped

/-! ## 3. Rationals: representability and rounding -/
#eval isRepresentable (1/10)       -- false
#eval isRepresentable (3/4)        -- true
#eval exIv (ofRat (1/10))          -- the two doubles adjacent to 1/10
#eval ofRat (3/4)                  -- point interval
#eval ofRatInterval (1/3) (2/3)

example : Representable (3/4) := by decide +kernel
example : ¬ Representable (1/10) := by decide +kernel

/-! ## 4. A real proof: ∀ x ∈ [1/10, 3/10], x*x + x ≤ 13/32.
   The only numeric fact is kernel-checked via the Nat mirror `KI` (`decide +kernel`). -/
def I : Interval64 := ofRatInterval (1/10) (3/10)
def J : Interval64 := I * I + I

#eval J                                   -- about [0.11, 0.39]
#eval exIv J

-- Kernel-checked (no `native_decide`): rewrite `J` to the Nat mirror `KI` and compare bits.
theorem J_hi_le : J.hi ≤ 0.40625 := by
  open Interval64.KF in
  have w := (ofRatInterval_toI (1/10) (3/10)).2
  have wm := mul_wf w w
  refine hi_le_of_KI (add_wf wm w) ?_ (n := 0x3FDA000000000000) (by decide) (by decide +kernel)
    (by decide +kernel)
  show ofRatInterval (1/10) (3/10) * ofRatInterval (1/10) (3/10) + ofRatInterval (1/10) (3/10) = _
  rw [← (ofRatInterval_toI (1/10) (3/10)).1, ← mul_toI w w, ← add_toI wm w]

theorem sq_add_le' {x : Rat} (h1 : 1/10 ≤ x) (h2 : x ≤ 3/10) :
    x * x + x ≤ 13/32 := by
  have hx : MemIv x I := memIv_ofRatInterval h1 h2
  have hlo : ∃ q, bitsToRat? I.lo.toBits = some q := Option.isSome_iff_exists.mp (by decide +kernel)
  have hhi : ∃ q, bitsToRat? I.hi.toBits = some q := Option.isSome_iff_exists.mp (by decide +kernel)
  have hmul := mul_mem_iv hx hx hlo hhi hlo hhi
  exact hi_le_of_native (add_mem_iv hmul hx) J_hi_le (by decide +kernel)

#print axioms sq_add_le'

/-! ## Conversions (`Interval64.Conv`): literals, casts, `Float` points -/
#eval (0.1 : Interval64)                  -- encloses exactly 1/10: two adjacent doubles
#eval (2 : Interval64) * I + 0.5          -- numeric and decimal literals
#eval I + (1/3 : Rat) + (7 : Nat) + (-2 : Int) + (0.25 : Float)  -- coercions
#eval ((Float.inf : Float) : Interval64)  -- [inf, inf]: encloses no real (empty toSet)

example : bitsToRat? (0.1 : Interval64).lo.toBits = some (7205759403792793 / 72057594037927936) := by
  decide +kernel
example : bitsToRat? (0.1 : Interval64).hi.toBits = some (3602879701896397 / 36028797018963968) := by
  decide +kernel

/-! ## Extended division (`Interval64.Split`) -/
#eval divSplit 5 (ofRatInterval (-2) 3)                  -- [-inf, -2.5] ∪ [1.666667, inf]
#eval divSplit 5 (ofRatInterval 0 3)                     -- one [1.666667, inf]
#eval divSplit (ofRatInterval (-1) 1) (ofRatInterval (-2) 3)  -- one whole
#eval divSplit 5 0                                       -- empty
#eval (divSplit 5 (ofRatInterval 2 3) : Interval64)      -- same as 5 / [2, 3]
example : bitsToRat? (divSplit 5 (ofRatInterval (-2) 3)).piece1.hi.toBits = some (-5/2) := by
  decide +kernel
