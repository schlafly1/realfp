/-
Real power `x ^ y` (`Real.rpow`) for intervals with positive members.

`Interval64.rpow X Y = exp (Y * log X)`: the composition of the outward-rounded `log`, `*`
and `exp` enclosures, so it is sound for every `x ∈ X` with `0 < x` and every `y ∈ Y`
(`RealFP.Pow.rpow_mem_toSet`). It is not correctly rounded: the result is typically a few
ulps wider than `[pow↓(x,y), pow↑(x,y)]`, and more when `|y · log x|` is large (the `exp`
argument interval has absolute width ≈ ulp(y·log x)). Members `x ≤ 0` are not covered by
the theorem (`log` of a non-positive endpoint gives an unbounded/invalid lower part).
The CORE-MATH `cr_pow` objects (`iv64_dir_pow_down/up`) are linked but not yet used: a
correctly rounded pointwise `pow` needs its own exact Lean spec.
-/
import Interval64.Transc

namespace Interval64

/-- `X ^ Y` enclosure for `X > 0`, via `exp (Y * log X)`. -/
def rpow (X Y : Interval64) : Interval64 := exp (Y * log X)

end Interval64
