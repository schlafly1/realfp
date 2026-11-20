/-
`native_decide` demonstration, compiled as part of the library so the theorem
is available to dependents. See `Interval64Native.lean` for the runtime
counter check and axiom report.
-/
import Interval64.Interval

namespace Interval64.NativeDecide

open Interval64.Directed

/-- A concrete interval `[1/2, 3/2]`. -/
def demoIv : Interval64 := ⟨0.5, 1.5⟩

/--
`x * x + x` for `x ∈ [0.5, 1.5]`. The exact range of `t ↦ t² + t` on this
interval is `[0.75, 3.75]`. `1.5`, `2.25` and `3.75` are binary64-exact, so
the directed upper bound is exactly `3.75`.
-/
def demoHi : Float := (demoIv * demoIv + demoIv).hi

-- Observe whether `native_decide` below increments the AVX-512 C debug counter.
#eval debugReset 0

/-- Proved by evaluating the compiled (native) predicate. -/
theorem demoHi_le : demoHi ≤ 3.75 := by native_decide

#eval debugCount 1

def demoHi_le_bool : Bool := decide (demoHi ≤ 3.75)

theorem demoHi_le_bool_true : demoHi_le_bool = true := by native_decide

end Interval64.NativeDecide
