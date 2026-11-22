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
import Interval64.Conv
import Interval64.Split
import Interval64.Transc
import Interval64.Trig
import Interval64.InvTrig
import Interval64.Hyp
import Interval64.Tan
import Interval64.Asin
import Interval64.Pow
import Interval64.Ops
import Interval64.Kernel.Nat
import Interval64.Kernel.Interval
import Interval64.Kernel.Reflect
import Interval64.Kernel.Deriv
import Interval64.Tape
import Interval64.Matrix
import Interval64.Poly
import Interval64.Quad
import Interval64.Kernel.Matrix
import Interval64.Kernel.MatrixCert
import Interval64.Kernel.Quad
import Interval64.Kernel.QuadCert
import Interval64.Bernstein
import Interval64.Quad2
