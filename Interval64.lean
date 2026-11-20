/-
A small Lean 4 library for binary64 interval arithmetic with hardware
directed rounding. Scalar operations are `@[extern]` C kernels (AVX-512
embedded rounding, plus a fesetround fallback). They do not go through
Lean’s `Float.add` / `Float.mul` / etc.
-/
import Interval64.Directed
import Interval64.Interval
import Interval64.Widen
