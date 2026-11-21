/* Directed-rounding transcendental kernels for Interval64.
 *
 * Each kernel runs a CORE-MATH correctly rounded function (c/coremath/, MIT
 * license) with the hardware rounding mode temporarily set to toward -inf or
 * toward +inf. CORE-MATH functions do not call fegetround(); they are
 * correctly rounded in whatever rounding mode the FPU is in (they only rely on
 * IEEE arithmetic in the current mode), so the result is the correctly rounded
 * RD / RU value.
 *
 * Mode switching: x86_64 writes MXCSR directly (_mm_setcsr; CORE-MATH uses
 * SSE2/FMA only, no x87); aarch64 writes FPCR.RMode; others use fesetround.
 * The CORE-MATH objects are compiled with -frounding-math -ffp-contract=off and
 * live in separate translation units, so no FP operation is moved across the
 * mode switch.
 */
#include <stdint.h>
#include <fenv.h>

double cr_exp(double);
double cr_log(double);
double cr_sin(double);
double cr_cos(double);

#if defined(__x86_64__)
#include <immintrin.h>
typedef unsigned iv64_mode_t;
static inline iv64_mode_t iv64_set_mode(int up) {
  unsigned old = _mm_getcsr();
  _mm_setcsr((old & ~0x6000u) | (up ? 0x4000u : 0x2000u));
  return old;
}
static inline void iv64_restore_mode(iv64_mode_t old) { _mm_setcsr(old); }
#elif defined(__aarch64__)
typedef uint64_t iv64_mode_t;
static inline iv64_mode_t iv64_set_mode(int up) {
  uint64_t old;
  __asm__ __volatile__("mrs %0, fpcr" : "=r"(old) :: "memory");
  /* RMode bits 23:22: 00 RN, 01 RP (+inf), 10 RM (-inf), 11 RZ */
  uint64_t m = (old & ~(UINT64_C(3) << 22)) | ((up ? UINT64_C(1) : UINT64_C(2)) << 22);
  __asm__ __volatile__("msr fpcr, %0" :: "r"(m) : "memory");
  return old;
}
static inline void iv64_restore_mode(iv64_mode_t old) {
  __asm__ __volatile__("msr fpcr, %0" :: "r"(old) : "memory");
}
#else
typedef int iv64_mode_t;
static inline iv64_mode_t iv64_set_mode(int up) {
  int old = fegetround();
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  return old;
}
static inline void iv64_restore_mode(iv64_mode_t old) { fesetround(old); }
#endif

#if defined(__x86_64__)
#define IV64_BARRIER_REG "x"
#else
#define IV64_BARRIER_REG "w"
#endif
#define IV64_DIR(name, fn, up)                                   \
  double name(double x) {                                        \
    iv64_mode_t m = iv64_set_mode(up);                           \
    double r = fn(x);                                            \
    __asm__ __volatile__("" : "+" IV64_BARRIER_REG(r) :: "memory"); \
    iv64_restore_mode(m);                                        \
    return r;                                                    \
  }

IV64_DIR(iv64_dir_exp_down, cr_exp, 0)
IV64_DIR(iv64_dir_exp_up,   cr_exp, 1)
IV64_DIR(iv64_dir_log_down, cr_log, 0)
IV64_DIR(iv64_dir_log_up,   cr_log, 1)
IV64_DIR(iv64_dir_sin_down, cr_sin, 0)
IV64_DIR(iv64_dir_sin_up,   cr_sin, 1)
IV64_DIR(iv64_dir_cos_down, cr_cos, 0)
IV64_DIR(iv64_dir_cos_up,   cr_cos, 1)

/* Round-to-nearest CORE-MATH (for benchmarks / comparison). */
double iv64_cr_exp(double x) { return cr_exp(x); }
double iv64_cr_log(double x) { return cr_log(x); }
double iv64_cr_sin(double x) { return cr_sin(x); }
double iv64_cr_cos(double x) { return cr_cos(x); }
