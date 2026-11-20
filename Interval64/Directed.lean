/-
Directed binary64 `+`, `-`, `*`, `/`, `sqrt`.

Each operator has a computable Lean specification (`*Spec` / `Interval64.Spec`)
that the kernel can unfold and reason about. The compiled runtime is the
AVX-512 C kernel, attached with `@[implemented_by]`. The two are intended to
be bit-identical (all NaNs equal, signed zeros distinguished); the test
executable checks this differentially.

fesetround fallbacks remain opaque externs (save / compute / restore MXCSR).
They are not used as the logical model.
-/
import Interval64.Spec

namespace Interval64.Directed

/-- True if the CPU advertises AVX-512F (runtime `cpuid`). -/
@[extern "iv64_has_avx512f_unit"]
opaque hasAvx512f (u : Unit) : Bool

def avx512fAvailable : Bool := hasAvx512f ()

@[extern "iv64_next_up"]
opaque nextUp (x : Float) : Float

@[extern "iv64_next_down"]
opaque nextDown (x : Float) : Float

/-- The `token` argument exists so calls are not treated as a constant
    `debugReset () = 0` and dead-code-eliminated (the C functions are impure). -/
@[extern "iv64_debug_reset"]
opaque debugReset (token : UInt64) : UInt64

@[extern "iv64_debug_count"]
opaque debugCount (token : UInt64) : UInt64

/-! # Specifications (kernel-visible, software IEEE directed rounding) -/

def addDownSpec (a b : Float) : Float := Float.ofBits (Spec.addDown a.toBits b.toBits)
def addUpSpec   (a b : Float) : Float := Float.ofBits (Spec.addUp   a.toBits b.toBits)
def subDownSpec (a b : Float) : Float := Float.ofBits (Spec.subDown a.toBits b.toBits)
def subUpSpec   (a b : Float) : Float := Float.ofBits (Spec.subUp   a.toBits b.toBits)
def mulDownSpec (a b : Float) : Float := Float.ofBits (Spec.mulDown a.toBits b.toBits)
def mulUpSpec   (a b : Float) : Float := Float.ofBits (Spec.mulUp   a.toBits b.toBits)
def divDownSpec (a b : Float) : Float := Float.ofBits (Spec.divDown a.toBits b.toBits)
def divUpSpec   (a b : Float) : Float := Float.ofBits (Spec.divUp   a.toBits b.toBits)
def sqrtDownSpec (a : Float) : Float := Float.ofBits (Spec.sqrtDown a.toBits)
def sqrtUpSpec   (a : Float) : Float := Float.ofBits (Spec.sqrtUp   a.toBits)

/-! # Compiled implementations (AVX-512 embedded rounding; no debug counter) -/

@[extern "iv64_avx_add_down"] opaque addDownImpl (a b : Float) : Float
@[extern "iv64_avx_add_up"]   opaque addUpImpl   (a b : Float) : Float
@[extern "iv64_avx_sub_down"] opaque subDownImpl (a b : Float) : Float
@[extern "iv64_avx_sub_up"]   opaque subUpImpl   (a b : Float) : Float
@[extern "iv64_avx_mul_down"] opaque mulDownImpl (a b : Float) : Float
@[extern "iv64_avx_mul_up"]   opaque mulUpImpl   (a b : Float) : Float
@[extern "iv64_avx_div_down"] opaque divDownImpl (a b : Float) : Float
@[extern "iv64_avx_div_up"]   opaque divUpImpl   (a b : Float) : Float
@[extern "iv64_avx_sqrt_down"] opaque sqrtDownImpl (a : Float) : Float
@[extern "iv64_avx_sqrt_up"]   opaque sqrtUpImpl   (a : Float) : Float

/-! # Public operators: spec for the kernel, AVX-512 C at runtime -/

@[implemented_by addDownImpl]
def addDown (a b : Float) : Float := addDownSpec a b
@[implemented_by addUpImpl]
def addUp (a b : Float) : Float := addUpSpec a b
@[implemented_by subDownImpl]
def subDown (a b : Float) : Float := subDownSpec a b
@[implemented_by subUpImpl]
def subUp (a b : Float) : Float := subUpSpec a b
@[implemented_by mulDownImpl]
def mulDown (a b : Float) : Float := mulDownSpec a b
@[implemented_by mulUpImpl]
def mulUp (a b : Float) : Float := mulUpSpec a b
@[implemented_by divDownImpl]
def divDown (a b : Float) : Float := divDownSpec a b
@[implemented_by divUpImpl]
def divUp (a b : Float) : Float := divUpSpec a b
@[implemented_by sqrtDownImpl]
def sqrtDown (a : Float) : Float := sqrtDownSpec a
@[implemented_by sqrtUpImpl]
def sqrtUp (a : Float) : Float := sqrtUpSpec a

/-- Aliases kept for existing tests / call sites. -/
abbrev avxAddDown := addDown
abbrev avxAddUp := addUp
abbrev avxSubDown := subDown
abbrev avxSubUp := subUp
abbrev avxMulDown := mulDown
abbrev avxMulUp := mulUp
abbrev avxDivDown := divDown
abbrev avxDivUp := divUp
abbrev avxSqrtDown := sqrtDown
abbrev avxSqrtUp := sqrtUp

@[extern "iv64_fe_add_down"] opaque feAddDown (a b : Float) : Float
@[extern "iv64_fe_add_up"]   opaque feAddUp   (a b : Float) : Float
@[extern "iv64_fe_sub_down"] opaque feSubDown (a b : Float) : Float
@[extern "iv64_fe_sub_up"]   opaque feSubUp   (a b : Float) : Float
@[extern "iv64_fe_mul_down"] opaque feMulDown (a b : Float) : Float
@[extern "iv64_fe_mul_up"]   opaque feMulUp   (a b : Float) : Float
@[extern "iv64_fe_div_down"] opaque feDivDown (a b : Float) : Float
@[extern "iv64_fe_div_up"]   opaque feDivUp   (a b : Float) : Float
@[extern "iv64_fe_sqrt_down"] opaque feSqrtDown (a : Float) : Float
@[extern "iv64_fe_sqrt_up"]   opaque feSqrtUp   (a : Float) : Float

/-- Run the C self-test (AVX vs fesetround vs software oracles) and print a report.
    Returns the number of recorded failures. The official gate is AVX vs fesetround. -/
@[extern "iv64_selftest_report"]
opaque selftestReport (u : Unit) : UInt64

@[extern "iv64_run_benches"]
opaque runCBenches (u : Unit) : UInt64

/-- Bit-identical, treating all NaNs as equal (payloads may differ). -/
def sameBitsOrNaN (a b : Float) : Bool :=
  if a.isNaN then b.isNaN else a.toBits == b.toBits

end Interval64.Directed
