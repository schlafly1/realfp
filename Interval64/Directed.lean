/-
C FFI for directed binary64 `+`, `-`, `*`, `/`, `sqrt`.

Compiled ABI: each binary operator is `double name(double, double)`.
These are opaque externs; they are not Lean `Float.add` and must not be
used as if they satisfied `Float.Model` (which is round-to-nearest-even).
Each fesetround entry saves and restores the rounding mode before return.
AVX-512 entries use embedded rounding and do not change MXCSR.
-/
namespace Interval64.Directed

/-- True if the CPU advertises AVX-512F (runtime `cpuid`). -/
@[extern "iv64_has_avx512f_unit"]
opaque hasAvx512f (u : Unit) : Bool

def avx512fAvailable : Bool := hasAvx512f ()

@[extern "iv64_next_up"]
opaque nextUp (x : Float) : Float

@[extern "iv64_next_down"]
opaque nextDown (x : Float) : Float

@[extern "iv64_avx_add_down"] opaque avxAddDown (a b : Float) : Float
@[extern "iv64_avx_add_up"]   opaque avxAddUp   (a b : Float) : Float
@[extern "iv64_avx_sub_down"] opaque avxSubDown (a b : Float) : Float
@[extern "iv64_avx_sub_up"]   opaque avxSubUp   (a b : Float) : Float
@[extern "iv64_avx_mul_down"] opaque avxMulDown (a b : Float) : Float
@[extern "iv64_avx_mul_up"]   opaque avxMulUp   (a b : Float) : Float
@[extern "iv64_avx_div_down"] opaque avxDivDown (a b : Float) : Float
@[extern "iv64_avx_div_up"]   opaque avxDivUp   (a b : Float) : Float
@[extern "iv64_avx_sqrt_down"] opaque avxSqrtDown (a : Float) : Float
@[extern "iv64_avx_sqrt_up"]   opaque avxSqrtUp   (a : Float) : Float

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

/-- Default directed ops: AVX-512 embedded rounding. -/
abbrev addDown := avxAddDown
abbrev addUp   := avxAddUp
abbrev subDown := avxSubDown
abbrev subUp   := avxSubUp
abbrev mulDown := avxMulDown
abbrev mulUp   := avxMulUp
abbrev divDown := avxDivDown
abbrev divUp   := avxDivUp
abbrev sqrtDown := avxSqrtDown
abbrev sqrtUp   := avxSqrtUp

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
