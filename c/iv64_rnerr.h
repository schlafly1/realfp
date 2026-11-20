/* Interval64 portable directed-rounding kernels: round-to-nearest + exact error term.

   Used as the runtime backend on aarch64 (and on any non-AVX-512 target), and
   compiled natively on x86_64 too so it can be differentially tested against the
   AVX-512 embedded-rounding kernels.

   Header-only (static inline) so the library and the standalone test harness
   compile exactly the same code.

   Assumptions:
     - IEEE binary64 with the current rounding mode = round-to-nearest-even
       (the default; Lean never changes it), gradual underflow (no FTZ/DAZ),
       and a correctly-rounded hardware fma and sqrt.
     - Compiled with -ffp-contract=off -frounding-math -fno-math-errno, no -ffast-math.

   Method (never touches FPCR/MXCSR on the main path):
     add/sub: s = RN(a+b), exact error by branch-free TwoSum (operands < 2^1021;
              larger operands use Fast2Sum on the cold path).
     mul:     p = RN(a*b), e = fma(a,b,-p) exact unless the product is tiny.
     div:     q = RN(a/b), r = fma(-q,b,a) exact unless operands/quotient are tiny;
              a/b - q = r/b, so sign(r)*sign(b) gives the direction.
     sqrt:    s = RN(sqrt(x)), r = fma(-s,s,x) exact; tiny x is pre-scaled by 2^600
              (result scaled back by 2^-300, exact because sqrt results are normal).
   If the exact value is above the RN result, round-up steps one ulp up; if below,
   round-down steps one ulp down; nextUp(maxFinite) = +inf handles overflow past
   maxFinite. RN overflow to +-inf (non-infinite operands) gives +-maxFinite for the
   direction toward zero.

   Rare slow path: tiny products / quotients (|a*b| < 2^-968; for / a quotient below 2^-1022,
   a subnormal divisor or |a| < 2^-968) where the fma error term could itself underflow. These use a
   save/set/restore fesetround (MXCSR on x86, FPCR on aarch64). */
#ifndef IV64_RNERR_H
#define IV64_RNERR_H

#include <math.h>
#include <float.h>
#include <fenv.h>
#include <stdint.h>
#include <string.h>

/* Test hooks (counting slow-path / overflow uses); no-ops by default. */
#ifndef IV64R_SLOW_HOOK
#define IV64R_SLOW_HOOK() ((void)0)
#endif
#ifndef IV64R_OVF_HOOK
#define IV64R_OVF_HOOK() ((void)0)
#endif


static inline uint64_t iv64r_bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static inline double iv64r_from(uint64_t u) { double x; memcpy(&x, &u, 8); return x; }

#define IV64R_MAXF 0x1.fffffffffffffp+1023

/* nextUp / nextDown for non-NaN x (same semantics as iv64_next_up/down). */
static inline double iv64r_next_up(double x) {
  uint64_t u = iv64r_bits(x);
  if (u == 0x7ff0000000000000ull) return x;               /* +inf */
  if (u == 0x8000000000000000ull) return 0.0;             /* -0 -> +0 (not reached) */
  return iv64r_from((u >> 63) ? u - 1 : u + 1);
}
static inline double iv64r_next_down(double x) {
  uint64_t u = iv64r_bits(x);
  if (u == 0xfff0000000000000ull) return x;               /* -inf */
  if (u == 0x0000000000000000ull) return iv64r_from(0x8000000000000000ull);
  return iv64r_from((u >> 63) ? u + 1 : u - 1);
}

#ifdef __GNUC__
#define IV64R_NOINLINE __attribute__((noinline, cold))
#define IV64R_LIKELY(x) __builtin_expect(!!(x), 1)
#else
#define IV64R_NOINLINE
#define IV64R_LIKELY(x) (x)
#endif

/* r is RN(exact), finite and nonzero; err has the sign of (exact - r) (or is 0).
   Branch-free one-ulp step on the bit pattern: for r > 0 nextUp is u+1 and nextDown
   u-1; for r < 0 the reverse. nextUp(maxFinite) = +inf and nextDown(-maxFinite) = -inf
   fall out of the encoding. (r is never 0 here: inexact results are not tiny.) */
static inline double iv64r_fix(double r, double err, int up) {
  uint64_t u = iv64r_bits(r);
  uint64_t step = (uint64_t)(up ? (err > 0) : (err < 0));
  uint64_t sub = (u >> 63) ^ (uint64_t)(up ? 0 : 1);   /* 1: decrement the bits */
  uint64_t m = (uint64_t)0 - sub;                       /* 0 or all-ones */
  return iv64r_from(u + ((step ^ m) + sub));            /* u + step or u - step */
}

/* True iff lo <= |x| <= hi (lo, hi positive finite bit patterns); one unsigned
   compare. NaN and inf are outside every such range. */
static inline int iv64r_absin(double x, uint64_t lo, uint64_t hi) {
  uint64_t m = iv64r_bits(x) & 0x7fffffffffffffffull;
  return m - lo <= hi - lo;
}
#define IV64R_B_MAXF   0x7fefffffffffffffull   /* maxFinite */
#define IV64R_B_MIN    0x0010000000000000ull   /* 2^-1022 (DBL_MIN) */
#define IV64R_B_2M968  0x0370000000000000ull   /* 2^-968 */
#define IV64R_B_2M960  0x03f0000000000000ull   /* 2^-960 */
#define IV64R_B_2P1021 0x7fc0000000000000ull   /* 2^1021 */

/* RN overflowed to +-inf from finite operands: |exact| >= 2^1024 - 2^970 > maxFinite. */
static inline double iv64r_overflow(double s, int up) {
  IV64R_OVF_HOOK();
  if (s > 0) return up ? s : IV64R_MAXF;
  return up ? -IV64R_MAXF : s;
}

/* Slow path: directed rounding via the dynamic rounding mode (save / restore). */
IV64R_NOINLINE static double iv64r_slow_mul(double a, double b, int up) {
  IV64R_SLOW_HOOK();
  int old = fegetround();
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  volatile double va = a, vb = b, r;
  r = va * vb;
  fesetround(old);
  return r;
}
IV64R_NOINLINE static double iv64r_slow_div(double a, double b, int up) {
  IV64R_SLOW_HOOK();
  int old = fegetround();
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  volatile double va = a, vb = b, r;
  r = va / vb;
  fesetround(old);
  return r;
}

/* ---- add / sub ---------------------------------------------------------------
   Hot path: both |a|, |b| < 2^1021 (so no intermediate can overflow), branch-free
   TwoSum (Knuth/Moller: exact for any finite inputs under RN, subnormals included).
   Everything else (NaN, inf, huge operands, overflow) goes to the cold path. */
IV64R_NOINLINE static double iv64r_add_cold(double a, double b, int up) {
  double s = a + b;
  if (!isfinite(s)) {
    if (isnan(s) || isinf(a) || isinf(b)) return s;
    return iv64r_overflow(s, up);
  }
  if (s == 0) {
    if (up) return s;
    return (iv64r_bits(a) == 0 && iv64r_bits(b) == 0) ? s : iv64r_from(0x8000000000000000ull);
  }
  /* Fast2Sum with |x| >= |y|: z = s - x and err = y - z are exact and cannot overflow. */
  int sw = fabs(a) < fabs(b);
  double x = sw ? b : a, y = sw ? a : b;
  double z = s - x;
  return iv64r_fix(s, y - z, up);
}

static inline double iv64r_add(double a, double b, int up) {
  uint64_t ma = iv64r_bits(a) << 1, mb = iv64r_bits(b) << 1;
  if (IV64R_LIKELY((ma < (IV64R_B_2P1021 << 1)) & (mb < (IV64R_B_2P1021 << 1)))) {
    double s = a + b;
    if (s == 0) {
      /* A sum that rounds to 0 is exact (a == -b). RN and RU give +0 unless both
         operands are -0; RD gives -0 unless both operands are +0. */
      if (up) return s;
      return ((iv64r_bits(a) | iv64r_bits(b)) == 0) ? s : iv64r_from(0x8000000000000000ull);
    }
    double bb = s - a;                     /* TwoSum */
    double aa = s - bb;
    double err = (a - aa) + (b - bb);
    return iv64r_fix(s, err, up);
  }
  return iv64r_add_cold(a, b, up);
}

static inline double iv64r_sub(double a, double b, int up) { return iv64r_add(a, -b, up); }

/* ---- mul ---------------------------------------------------------------------
   Hot path: 2^-968 <= |p| <= maxFinite. Then the error a*b - p lies on the 2^-1074
   grid and fits in 53 bits, so fma(a,b,-p) is exact. */
IV64R_NOINLINE static double iv64r_mul_cold(double a, double b, int up) {
  double p = a * b;
  if (!isfinite(p)) {
    if (isnan(p) || isinf(a) || isinf(b)) return p;
    return iv64r_overflow(p, up);
  }
  if (p == 0 && (a == 0 || b == 0)) return p;   /* exact signed zero (sign = xor) */
  return iv64r_slow_mul(a, b, up);              /* tiny or underflow to 0 */
}

static inline double iv64r_mul(double a, double b, int up) {
  double p = a * b;
  if (IV64R_LIKELY(iv64r_absin(p, IV64R_B_2M968, IV64R_B_MAXF)))
    return iv64r_fix(p, fma(a, b, -p), up);
  return iv64r_mul_cold(a, b, up);
}

/* ---- div ---------------------------------------------------------------------
   Hot path: |q| and |b| normal, |a| >= 2^-968 (all finite). Then r = fma(-q,b,a) =
   a - q*b exactly, and a/b - q = r/b, so the direction is sign(r) xor sign(b). */
IV64R_NOINLINE static double iv64r_div_cold(double a, double b, int up) {
  double q = a / b;
  if (!isfinite(q)) {
    if (isnan(q) || isinf(a) || b == 0) return q;   /* NaN, inf/x, x/0: exact */
    return iv64r_overflow(q, up);
  }
  if (q == 0 && (a == 0 || isinf(b))) return q;     /* exact signed zero */
  /* Remaining: finite nonzero operands with |q| < 2^-1022 (incl. underflow to 0),
     a subnormal divisor, or |a| < 2^-968, where the fma remainder could be inexact. */
  return iv64r_slow_div(a, b, up);
}

static inline double iv64r_div(double a, double b, int up) {
  double q = a / b;
  if (IV64R_LIKELY(iv64r_absin(q, IV64R_B_MIN, IV64R_B_MAXF) &
                   iv64r_absin(b, IV64R_B_MIN, IV64R_B_MAXF) &
                   iv64r_absin(a, IV64R_B_2M968, IV64R_B_MAXF))) {
    double r = fma(-q, b, a);
    /* err with the sign of r/b (r == 0 stays +-0, i.e. exact) */
    return iv64r_fix(q, iv64r_from(iv64r_bits(r) ^ (iv64r_bits(b) & 0x8000000000000000ull)), up);
  }
  return iv64r_div_cold(a, b, up);
}

/* ---- sqrt --------------------------------------------------------------------
   Hot path: 2^-960 <= a <= maxFinite (a positive). r = fma(-s,s,a) = a - s*s exactly. */
IV64R_NOINLINE static double iv64r_sqrt_cold(double a, int up) {
  if (!(a > 0) || isinf(a)) return sqrt(a);  /* NaN, negative (NaN), +-0, +inf: exact */
  double x = a * 0x1p600;                    /* tiny a: exact scaling */
  double s = sqrt(x);
  double res = iv64r_fix(s, fma(-s, s, x), up);
  return res * 0x1p-300;                     /* exact: res is normal, >= 2^-237 */
}

static inline double iv64r_sqrt(double a, int up) {
  uint64_t u = iv64r_bits(a);                /* sign bit set => outside the range */
  if (IV64R_LIKELY(u - IV64R_B_2M960 <= IV64R_B_MAXF - IV64R_B_2M960)) {
    double s = sqrt(a);
    return iv64r_fix(s, fma(-s, s, a), up);
  }
  return iv64r_sqrt_cold(a, up);
}

#endif
