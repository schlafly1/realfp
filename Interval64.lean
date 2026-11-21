/-
A small Lean 4 library for binary64 interval arithmetic with hardware
directed rounding. Each directed scalar operation has a computable Lean
specification (software IEEE binary64 rounding) and an AVX-512 C runtime
attached with `@[implemented_by]`. Interval operations are defined in Lean
on top of those scalars, so they inherit both the spec and the fast path.
-/
import Interval64.Spec
import Interval64.Directed
import Interval64.Interval
import Interval64.Widen
import Interval64.Theorems
import Interval64.NativeDecide
import Interval64.OfRat
import Interval64.Transc
import Interval64.Trig
