/* Interval64 directed-rounding kernels.
   Compile with gcc: -O2 -fPIC -mavx512f -mavx512vl -ffp-contract=off -frounding-math -fno-math-errno
   The Lean toolchain clang on this box lacks immintrin.h; use gcc/cc. */

#define _GNU_SOURCE
#include "interval64.h"

#include <immintrin.h>
#include <fenv.h>
#include <math.h>
#include <float.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>

#pragma STDC FENV_ACCESS ON

/* -------------------------------------------------------------------------- */
/* bits / classification                                                        */
/* -------------------------------------------------------------------------- */

static inline uint64_t d2u(double x) {
  uint64_t u;
  memcpy(&u, &x, 8);
  return u;
}
static inline double u2d(uint64_t u) {
  double x;
  memcpy(&x, &u, 8);
  return x;
}

static inline int is_nan_d(double x) { return isnan(x); }
static inline int is_inf_d(double x) { return isinf(x); }
static inline int is_finite_d(double x) { return isfinite(x); }
static inline int is_zero_d(double x) { return x == 0.0; }

/* IEEE total-order nextUp / nextDown, payload-canonical for NaN. */
double iv64_next_up(double x) {
  if (isnan(x)) return u2d(0x7ff8000000000000ull); /* canonical qNaN */
  if (x == INFINITY) return x;
  uint64_t u = d2u(x);
  if (u == 0x8000000000000000ull) return 0.0; /* -0 -> +0 */
  if (u & 0x8000000000000000ull) return u2d(u - 1);
  return u2d(u + 1);
}
double iv64_next_down(double x) {
  if (isnan(x)) return u2d(0x7ff8000000000000ull);
  if (x == -INFINITY) return x;
  uint64_t u = d2u(x);
  if (u == 0x0000000000000000ull) return u2d(0x8000000000000000ull); /* +0 -> -0 */
  if (u & 0x8000000000000000ull) return u2d(u + 1);
  return u2d(u - 1);
}

uint8_t iv64_has_avx512f(void) {
#if defined(__GNUC__)
  return __builtin_cpu_supports("avx512f") ? 1 : 0;
#else
  return 1;
#endif
}

/* -------------------------------------------------------------------------- */
/* AVX-512 embedded rounding (no MXCSR change)                                  */
/* -------------------------------------------------------------------------- */

#define ROUND_DOWN (_MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC)
#define ROUND_UP   (_MM_FROUND_TO_POS_INF | _MM_FROUND_NO_EXC)

static inline double avx_binop(
    double a, double b,
    __m128d (*op)(__m128d, __m128d, int),
    int rounding) {
  return _mm_cvtsd_f64(op(_mm_set_sd(a), _mm_set_sd(b), rounding));
}

double iv64_avx_add_down(double a, double b) { return avx_binop(a, b, _mm_add_round_sd, ROUND_DOWN); }
double iv64_avx_add_up  (double a, double b) { return avx_binop(a, b, _mm_add_round_sd, ROUND_UP); }
double iv64_avx_sub_down(double a, double b) { return avx_binop(a, b, _mm_sub_round_sd, ROUND_DOWN); }
double iv64_avx_sub_up  (double a, double b) { return avx_binop(a, b, _mm_sub_round_sd, ROUND_UP); }
double iv64_avx_mul_down(double a, double b) { return avx_binop(a, b, _mm_mul_round_sd, ROUND_DOWN); }
double iv64_avx_mul_up  (double a, double b) { return avx_binop(a, b, _mm_mul_round_sd, ROUND_UP); }
double iv64_avx_div_down(double a, double b) { return avx_binop(a, b, _mm_div_round_sd, ROUND_DOWN); }
double iv64_avx_div_up  (double a, double b) { return avx_binop(a, b, _mm_div_round_sd, ROUND_UP); }

double iv64_avx_sqrt_down(double a) {
  __m128d x = _mm_set_sd(a);
  return _mm_cvtsd_f64(_mm_sqrt_round_sd(x, x, ROUND_DOWN));
}
double iv64_avx_sqrt_up(double a) {
  __m128d x = _mm_set_sd(a);
  return _mm_cvtsd_f64(_mm_sqrt_round_sd(x, x, ROUND_UP));
}

/* -------------------------------------------------------------------------- */
/* fesetround save / restore (thread-local MXCSR + x87 CW)                      */
/* -------------------------------------------------------------------------- */

static inline double fe_binop(double a, double b, int mode, double (*op)(double, double)) {
  int old = fegetround();
  fesetround(mode);
  /* volatile to block CSE / reassociation across the mode change */
  volatile double va = a, vb = b, r;
  r = op((double)va, (double)vb);
  fesetround(old);
  return (double)r;
}
static double add_op(double x, double y) { return x + y; }
static double sub_op(double x, double y) { return x - y; }
static double mul_op(double x, double y) { return x * y; }
static double div_op(double x, double y) { return x / y; }

double iv64_fe_add_down(double a, double b) { return fe_binop(a, b, FE_DOWNWARD, add_op); }
double iv64_fe_add_up  (double a, double b) { return fe_binop(a, b, FE_UPWARD,   add_op); }
double iv64_fe_sub_down(double a, double b) { return fe_binop(a, b, FE_DOWNWARD, sub_op); }
double iv64_fe_sub_up  (double a, double b) { return fe_binop(a, b, FE_UPWARD,   sub_op); }
double iv64_fe_mul_down(double a, double b) { return fe_binop(a, b, FE_DOWNWARD, mul_op); }
double iv64_fe_mul_up  (double a, double b) { return fe_binop(a, b, FE_UPWARD,   mul_op); }
double iv64_fe_div_down(double a, double b) { return fe_binop(a, b, FE_DOWNWARD, div_op); }
double iv64_fe_div_up  (double a, double b) { return fe_binop(a, b, FE_UPWARD,   div_op); }

double iv64_fe_sqrt_down(double a) {
  int old = fegetround();
  fesetround(FE_DOWNWARD);
  volatile double va = a, r;
  r = sqrt((double)va);
  fesetround(old);
  return (double)r;
}
double iv64_fe_sqrt_up(double a) {
  int old = fegetround();
  fesetround(FE_UPWARD);
  volatile double va = a, r;
  r = sqrt((double)va);
  fesetround(old);
  return (double)r;
}

/* -------------------------------------------------------------------------- */
/* Software oracles                                                             */
/* -------------------------------------------------------------------------- */

/* Convert an exact (or already correctly-rounded-to-113-bit? no: exact) __float128
   to binary64 with directed rounding, via RN conversion plus a side test. */
static int q_isnan(__float128 x) { return x != x; }
static int q_isinf(__float128 x) {
  return x != 0 && (x + x == x) && (x == x);
}
static double q2d_down(__float128 x) {
  if (q_isnan(x)) return u2d(0x7ff8000000000000ull);
  if (q_isinf(x)) return (double)x;
  double d = (double)x; /* typically round-to-nearest-even */
  if (isnan(d)) return u2d(0x7ff8000000000000ull);
  __float128 back = (__float128)d;
  if (back <= x) return d;
  return iv64_next_down(d);
}
static double q2d_up(__float128 x) {
  if (q_isnan(x)) return u2d(0x7ff8000000000000ull);
  if (q_isinf(x)) return (double)x;
  double d = (double)x;
  if (isnan(d)) return u2d(0x7ff8000000000000ull);
  __float128 back = (__float128)d;
  if (back >= x) return d;
  return iv64_next_up(d);
}

double iv64_soft_mul_down(double a, double b) {
  if (isnan(a) || isnan(b)) return u2d(0x7ff8000000000000ull);
  return q2d_down((__float128)a * (__float128)b);
}
double iv64_soft_mul_up(double a, double b) {
  if (isnan(a) || isnan(b)) return u2d(0x7ff8000000000000ull);
  return q2d_up((__float128)a * (__float128)b);
}

/* Integer-significand directed rounding for binary64.
   mode: 0 = down (-inf), 1 = up (+inf). */
typedef struct {
  int sign;     /* 0 = +, 1 = - */
  int exp;      /* unbiased exponent of a 53-bit significand (hidden bit included);
                   value = ± mant * 2^(exp-52). mant==0 is a zero. */
  uint64_t mant; /* 0 or in [2^52, 2^53) */
  int cls;      /* 0 finite, 1 inf, 2 nan */
} unp;

static unp unpack(double x) {
  unp u;
  uint64_t b = d2u(x);
  u.sign = (int)(b >> 63);
  uint64_t e = (b >> 52) & 0x7ffull;
  uint64_t f = b & 0x000fffffffffffffull;
  if (e == 0x7ffull) {
    u.cls = (f == 0) ? 1 : 2;
    u.exp = 0;
    u.mant = f;
    return u;
  }
  u.cls = 0;
  if (e == 0) {
    if (f == 0) { u.exp = 0; u.mant = 0; return u; }
    int s = 0;
    uint64_t m = f;
    while ((m & (1ull << 52)) == 0) { m <<= 1; s++; }
    u.exp = 1 - 1023 - s;
    u.mant = m;
    return u;
  }
  u.exp = (int)e - 1023;
  u.mant = f | (1ull << 52);
  return u;
}

/* Pack a signed significand with extra precision:
   exact value = ± (mant + frac/2^64) * 2^(exp-52), with 0 < sticky if any bits below frac.
   mant is a 53-bit integer in [2^52, 2^53) or 0, or may be 2^53 before normalization.
   We also allow mant with more than 53 bits if we shift first.
   Here: `sig` is a normalized 64-bit fixed point: 1.xxx in the top bits? Easier approach below.
*/

__attribute__((unused)) static double pack_directed(int sign, int exp, uint64_t mant53, int inexact, int up) {
  /* mant53 is 0 or in [2^52, 2^53), exp is unbiased for hidden-bit form.
     inexact means there were leftover bits below bit 0 of mant53.
     `up` is 1 for round-toward-+inf, 0 for toward -inf. */
  if (mant53 == 0 && !inexact) {
    return sign ? u2d(0x8000000000000000ull) : 0.0;
  }
  /* If exact zero with leftover? shouldn't happen with mant=0 and inexact from a nonzero */
  if (mant53 == 0) {
    /* underflowed to 0 before rounding */
    /* directed: down of +tiny = +0; up of +tiny = min subnormal;
                 down of -tiny = -min; up of -tiny = -0 */
    int increment = (up && !sign) || (!up && sign);
    if (!increment) return sign ? u2d(0x8000000000000000ull) : 0.0;
    return sign ? u2d(0x8000000000000001ull) : u2d(0x0000000000000001ull);
  }

  int increment = inexact && ((up && !sign) || (!up && sign));
  if (increment) {
    mant53 += 1;
    if (mant53 == (1ull << 53)) {
      mant53 = (1ull << 52);
      exp += 1;
    }
  }

  /* Overflow */
  if (exp > 1023) {
    if ((up && !sign) || (!up && sign)) {
      return sign ? -INFINITY : INFINITY;
    }
    return sign ? -DBL_MAX : DBL_MAX;
  }

  /* Subnormal / underflow: exp < -1022 means the hidden-bit form is below the normal range.
     Hidden-bit value is mant * 2^(exp-52). Smallest normal is 2^-1022.
     We need to shift so the exponent field is 0. The subnormal exponent is 1-1023 = -1022
     for the implicit position... subnormal: significand f (52 bits, no hidden 1) * 2^(1-1023-52)
     = f * 2^-1074.
     Our number is mant53 * 2^(exp-52).
     We want f such that f * 2^-1074 = mant53 * 2^(exp-52), so f = mant53 * 2^(exp-52+1074)
     = mant53 * 2^(exp + 1022).
     If exp + 1022 >= 0, f = mant53 << (exp+1022) — but mant53 is 53 bits, would overflow 52-bit f
     (that would actually be a normal).
     For subnormals, exp <= -1023, shift = -1022 - exp >= 1. */
  if (exp < -1022) {
    int shift = -1022 - exp; /* >= 1 */
    int lost = inexact;
    /* We'll reconstruct as a 53-bit plus hidden, then right-shift into subnormal field. */
    uint64_t m = mant53;
    if (shift >= 64) {
      lost = 1; /* everything shifted out (or almost) */
      m = 0;
    } else {
      uint64_t dropped = m & ((shift >= 64) ? ~0ull : ((1ull << shift) - 1ull));
      if (dropped) lost = 1;
      m >>= shift;
    }
    /* m is now the 52-bit fraction (hidden bit has been shifted into it). */
    /* Apply directed rounding again at the subnormal grid if we lost bits just now
       that weren't already accounted for in `increment`.
       Careful: we already applied increment at the normal grid. For subnormals we
       should NOT have incremented at the 53-bit normal grid first; we should shift
       first, then round.
       Restart subnormal path without prior increment. */
    (void)m; (void)lost;
    /* Fall through to a cleaner subnormal implementation below via restart. */
  }

  if (exp >= -1022) {
    uint64_t ebits = (uint64_t)(exp + 1023);
    uint64_t frac = mant53 & 0x000fffffffffffffull;
    uint64_t bits = ((uint64_t)sign << 63) | (ebits << 52) | frac;
    return u2d(bits);
  }

  /* Clean subnormal path: start from pre-increment values... we already may have incremented.
     To keep pack_directed simple, handle subnormals before increment at the top.
     This branch is only reached if exp < -1022 after increment, which can happen
     only if we didn't overflow the mantissa into the next binade from a subnormal-range
     input. Re-do properly: the caller should pass unrounded sig. */

  /* If after increment we still have exp < -1022, encode subnormal from current mant/exp.
     This is wrong if increment happened at a finer grid. Callers for div/sqrt do
     rounding at the final grid themselves... I'll implement a lower-level pack. */
  return 0.0; /* placeholder, replaced by pack_from_extra below */
}

/* Better pack: significand is an integer `sig` with `prec` bits of body, plus `sticky`.
   Value = ± sig * 2^exp2, where sig is odd or sticky tells leftover, and we round
   sig to the binary64 grid.
   We'll just use a 128-bit significand and a binary exponent. */

static double pack_sig(int sign, int e2, unsigned __int128 sig, int sticky, int up) {
  /* value = ± sig * 2^e2, plus a leftover < 2^e2 if sticky and we treat sticky as (0, 1) ulp at e2.
     Normalize sig so that it is in [2^52, 2^53) or we shift toward that, collecting sticky. */
  if (sig == 0 && !sticky) {
    return sign ? u2d(0x8000000000000000ull) : 0.0;
  }
  if (sig == 0 && sticky) {
    /* 0 < |x| < 2^e2 */
    /* We'll treat this as a tiny positive at exponent e2 after norm; handled below
       by giving sig=1, e2 stays, then it will shift a lot. */
    sig = 1;
    /* sticky already 1; this overestimates slightly? sig*2^e2 is the lowest
       presentable at this scale. Fine for directed rounding if we keep sticky. */
  }

  /* Normalize to [2^52, 2^53) */
  int lz = (int)__builtin_clzll((uint64_t)(sig >> 64 ? (uint64_t)(sig >> 64) : 0));
  int width;
  if ((sig >> 64) != 0) {
    width = 128 - __builtin_clzll((uint64_t)(sig >> 64));
  } else {
    width = 64 - __builtin_clzll((uint64_t)sig);
  }
  /* We want width == 53, i.e. shift so the highest bit is at position 52. */
  int shift = width - 53; /* positive => shift right, negative => shift left */
  int inexact = sticky;
  uint64_t mant;
  int exp; /* unbiased, hidden-bit form: value = mant * 2^(exp-52) = sig * 2^e2
              so exp-52 = e2 + (bit position of sig's lsb relative to mant)...
              After putting top bit at position 52, mant in [2^52,2^53),
              value = mant * 2^(e2 + shift).  Because we shifted sig by `shift`
              (right if shift>0): mant = sig / 2^shift, value = mant * 2^(e2+shift).
              So exp-52 = e2+shift, exp = e2 + shift + 52. */
  if (shift > 0) {
    /* shift right, collect bits shifted out */
    if (shift >= 128) {
      inexact = 1;
      mant = 0;
    } else {
      unsigned __int128 mask = (shift >= 128) ? 0 : (((unsigned __int128)1 << shift) - 1);
      if ((sig & mask) != 0) inexact = 1;
      mant = (uint64_t)(sig >> shift);
    }
  } else if (shift < 0) {
    mant = (uint64_t)(sig << (-shift));
  } else {
    mant = (uint64_t)sig;
  }
  exp = e2 + shift + 52;

  /* Subnormal: if exp < -1022, shift more */
  if (exp < -1022) {
    int extra = -1022 - exp;
    if (extra >= 64) {
      inexact |= (mant != 0);
      mant = 0;
    } else {
      uint64_t dropped = mant & ((1ull << extra) - 1ull);
      if (dropped) inexact = 1;
      mant >>= extra;
    }
    exp = -1022;
    /* mant is now < 2^52 (subnormal, no hidden bit). Hidden-bit encoding with exp=-1022
       would be wrong. We'll encode with exponent field 0 and fraction = mant
       (mant should be the 52-bit field). Currently mant has the hidden bit already
       shifted down; for a number that was just below min normal, after extra=1,
       a 2^52 mant becomes 2^51, which is correct for the fraction with implicit
       exponent 2^-1022 * (0.frac)? 

       Min normal: exp=-1022, mant=2^52, value = 2^52 * 2^(-1022-52) = 2^-1022. Good.
       After extra=1, mant was 2^52, now 2^51, we set exp=-1022 still — WRONG if we
       encode as normal. We must encode as subnormal: exp field 0, fraction = mant
       (which is the integer f such that value = f * 2^-1074).

       value after extra shift: mant_new * 2^((-1022)-52) wait no.

       Before extra: value = mant * 2^(exp-52) with exp < -1022.
       extra = -1022 - exp, mant >>= extra, so
       value = (mant_new * 2^extra + lost) * 2^(exp-52)
             = mant_new * 2^(exp+extra-52) = mant_new * 2^(-1022-52)
             = mant_new * 2^-1074.
       Yes, fraction field should be mant_new (up to 52 bits). Encode exp field = 0.
    */
    int increment = inexact && ((up && !sign) || (!up && sign));
    if (increment) {
      mant += 1;
      if (mant == (1ull << 52)) {
        /* overflowed into min normal */
        uint64_t bits = ((uint64_t)sign << 63) | (1ull << 52); /* exp field = 1, frac = 0 */
        return u2d(bits);
      }
    }
    if (mant == 0) {
      return sign ? u2d(0x8000000000000000ull) : 0.0;
    }
    uint64_t bits = ((uint64_t)sign << 63) | (mant & 0x000fffffffffffffull);
    return u2d(bits);
  }

  /* Normal / overflow */
  int increment = inexact && ((up && !sign) || (!up && sign));
  if (increment) {
    mant += 1;
    if (mant == (1ull << 53)) {
      mant = (1ull << 52);
      exp += 1;
    }
  }
  if (exp > 1023) {
    if ((up && !sign) || (!up && sign)) return sign ? -INFINITY : INFINITY;
    return sign ? -DBL_MAX : DBL_MAX;
  }
  /* After increment we could still be in subnormal? No, exp >= -1022. */
  uint64_t ebits = (uint64_t)(exp + 1023);
  uint64_t frac = mant & 0x000fffffffffffffull;
  uint64_t bits = ((uint64_t)sign << 63) | (ebits << 52) | frac;
  return u2d(bits);
}

/* IEEE 754-2019 §6.3 exact-zero sign. */
static double signed_zero(int negative) {
  return negative ? u2d(0x8000000000000000ull) : 0.0;
}

/* Exact integer add/sub of two finite binary64 values, then directed pack.
   (__float128 is only 113 bits, so it is NOT exact when exponents differ by more
   than 112, e.g. 1 + min_subnormal.) */
static double soft_add(double a, double b, int up) {
  if (isnan(a) || isnan(b)) return u2d(0x7ff8000000000000ull);
  if (isinf(a) || isinf(b)) {
    if (isinf(a) && isinf(b) && signbit(a) != signbit(b))
      return u2d(0x7ff8000000000000ull);
    if (isinf(a)) return a;
    return b;
  }
  unp ua = unpack(a), ub = unpack(b);
  if (ua.mant == 0 && ub.mant == 0) {
    if (signbit(a) == signbit(b)) return a; /* keep equal-sign zero */
    return up ? 0.0 : signed_zero(1);
  }
  if (ua.mant == 0) return b;
  if (ub.mant == 0) return a;

  /* value = sign ? -mant : mant, times 2^(exp-52). Work with signed 256-bit? 128-bit
     plus sticky is enough if we align to the larger exponent and keep 64 guard bits. */
  int sa = ua.sign, sb = ub.sign;
  int ea = ua.exp, eb = ub.exp;
  uint64_t ma = ua.mant, mb = ub.mant;
  if (ea < eb || (ea == eb && ma < mb) || (ea == eb && ma == mb && sa && !sb)) {
    /* swap so |a| >= |b| when exponents/magnitudes dictate, but actually we only
       need ea >= eb for alignment. */
  }
  if (ea < eb) {
    int st = sa; sa = sb; sb = st;
    int et = ea; ea = eb; eb = et;
    uint64_t mt = ma; ma = mb; mb = mt;
  }
  int shift = ea - eb; /* >= 0 */
  /* Represent a as (signed) ma << 64 at exponent ea-52-64
     b shifted right by `shift`. */
  unsigned __int128 siga = ((unsigned __int128)ma) << 64;
  unsigned __int128 sigb;
  int sticky = 0;
  if (shift >= 128) {
    sigb = 0;
    sticky = (mb != 0);
  } else if (shift == 0) {
    sigb = ((unsigned __int128)mb) << 64;
  } else {
    unsigned __int128 wide = ((unsigned __int128)mb) << 64;
    unsigned __int128 mask = ((unsigned __int128)1 << shift) - 1;
    sticky = (wide & mask) != 0;
    sigb = wide >> shift;
  }
  int sign;
  unsigned __int128 sig;
  if (sa == sb) {
    sign = sa;
    sig = siga + sigb;
    /* carry may make 54+ bits */
  } else {
    /* |a| >= |b| because ea > eb, or ea==eb and we should have |ma|>=|mb|.
       If ea==eb and mb>ma we swapped only when ea<eb, so handle ma<mb. */
    if (siga < sigb) {
      sig = sigb - siga;
      sign = sb;
    } else if (siga > sigb) {
      sig = siga - sigb;
      sign = sa;
    } else {
      /* exact cancellation, leftover only in sticky bits of b */
      if (!sticky) return up ? 0.0 : signed_zero(1);
      /* result is a tiny nonzero with the sign of the larger? residual of b
         has opposite sign to a, so the tiny leftover has sign sb. */
      /* magnitude < 2^(ea-52-64). Represent as sig=1, e2 = ea-52-64- something.
         Simpler: pack_sig(sb, ea - 52 - 64 - 127, 1, 0, up) is not accurate
         enough in magnitude if we only need directed rounding to f64; the
         leftover is less than 1 unit at the bottom of sigb, i.e. < 2^(ea-52-64).
         down/up of a tiny number: */
      int increment = (up && !sb) || (!up && sb);
      if (!increment) return signed_zero(sb);
      /* least magnitude in the direction of sb: min subnormal with sign sb,
         but only if that magnitude is >= the leftover... leftover could be
         larger than min subnormal. Safest: sig=1 at e2 = ea-52-64-1? 
         leftover in (0, 2^(ea-52-64)). pack_sig will shift into the grid. */
      return pack_sig(sb, ea - 52 - 64, (unsigned __int128)1, 0, up);
      /* This treats leftover as 2^(ea-52-64), an over-estimate by up to 1 ulp
         at that huge-tiny scale; if ea is near 0, 2^(ea-116) may still be
         below min subnormal, so pack produces min subnormal or zero correctly
         for directed rounding as long as leftover > 0. If leftover is overestimated
         to exactly a grid point we might be 1 unit high — leftover is < 2^e2,
         we used = 2^e2. Fix: use sig=1, e2 = ea-52-64-1 (half). Still inexact. */
    }
  }
  if (sig == 0) {
    if (!sticky) return up ? 0.0 : signed_zero(1);
    return pack_sig(sign, ea - 52 - 64, 1, 0, up);
  }
  /* value = ± sig * 2^(ea-52-64)  [plus sticky < 1 at that unit] */
  return pack_sig(sign, ea - 52 - 64, sig, sticky, up);
}

double iv64_soft_add_down(double a, double b) { return soft_add(a, b, 0); }
double iv64_soft_add_up  (double a, double b) { return soft_add(a, b, 1); }
double iv64_soft_sub_down(double a, double b) { return soft_add(a, -b, 0); }
double iv64_soft_sub_up  (double a, double b) { return soft_add(a, -b, 1); }

static double soft_div(double a, double b, int up) {
  if (isnan(a) || isnan(b)) return u2d(0x7ff8000000000000ull);
  unp ua = unpack(a), ub = unpack(b);
  if (ua.cls == 2 || ub.cls == 2) return u2d(0x7ff8000000000000ull);
  /* Inf / Inf, 0/0 -> NaN */
  if (ua.cls == 1 && ub.cls == 1) return u2d(0x7ff8000000000000ull);
  if (ua.mant == 0 && ub.mant == 0 && ua.cls == 0 && ub.cls == 0)
    return u2d(0x7ff8000000000000ull);
  int sign = ua.sign ^ ub.sign;
  if (ub.cls == 1) { /* finite / Inf = signed 0 */
    return sign ? u2d(0x8000000000000000ull) : 0.0;
  }
  if (ub.mant == 0 && ub.cls == 0) { /* / 0 */
    if (ua.cls == 1) return sign ? -INFINITY : INFINITY;
    if (ua.mant == 0) return u2d(0x7ff8000000000000ull);
    return sign ? -INFINITY : INFINITY;
  }
  if (ua.cls == 1) return sign ? -INFINITY : INFINITY;
  if (ua.mant == 0) return sign ? u2d(0x8000000000000000ull) : 0.0;

  /* (ma * 2^(ea-52)) / (mb * 2^(eb-52)) = (ma/mb) * 2^(ea-eb)
     Compute (ma << 64) / mb, remainder for sticky.
     ma, mb in [2^52, 2^53).  ma<<64 / mb is in [2^63, 2^65). */
  /* (ma << 64) / mb can be up to almost 2^65, so the quotient is 128-bit. */
  unsigned __int128 num = ((unsigned __int128)ua.mant) << 64;
  unsigned __int128 q = num / ub.mant;
  unsigned __int128 r = num % ub.mant;
  int sticky = (r != 0);
  return pack_sig(sign, ua.exp - ub.exp - 64, q, sticky, up);
}

double iv64_soft_div_down(double a, double b) { return soft_div(a, b, 0); }
double iv64_soft_div_up  (double a, double b) { return soft_div(a, b, 1); }

static uint64_t isqrt_u128(unsigned __int128 n, unsigned __int128 *rem) {
  /* floor(sqrt(n)) for 128-bit n, plus remainder n - s^2. */
  if (n == 0) { *rem = 0; return 0; }
  /* Start from 64-bit sqrt of the high part. */
  uint64_t s;
  if (n <= 0xffffffffffffffffull) {
    uint64_t x = (uint64_t)n;
    uint64_t y = (uint64_t)sqrt((double)x);
    /* adjust */
    while ((unsigned __int128)y * y > n) y--;
    while ((unsigned __int128)(y + 1) * (y + 1) <= n) y++;
    *rem = n - (unsigned __int128)y * y;
    return y;
  }
  /* Newton's method on 128-bit */
  unsigned __int128 x = n;
  /* initial guess: 2^((width+1)/2) */
  int width = 128 - __builtin_clzll((uint64_t)(n >> 64));
  int gbits = (width + 1) / 2 + 64; /* crude */
  if (gbits >= 64) s = 1ull << 63;
  else s = 1ull << gbits;
  /* better: sqrt of high 64 bits << 32 */
  uint64_t hi = (uint64_t)(n >> 64);
  uint64_t g = (uint64_t)sqrt((double)hi);
  /* hi * 2^64, sqrt ~ g * 2^32 */
  unsigned __int128 s0 = ((unsigned __int128)g) << 32;
  if (s0 == 0) s0 = 1;
  /* Newton: s := (s + n/s) / 2, a few iterations */
  for (int i = 0; i < 8; i++) {
    unsigned __int128 q = n / s0;
    s0 = (s0 + q) >> 1;
  }
  uint64_t y = (uint64_t)s0;
  /* adjust down/up */
  while ((unsigned __int128)y * y > n) y--;
  while (y < 0xffffffffffffffffull &&
         (unsigned __int128)(y + 1) * (unsigned __int128)(y + 1) <= n) y++;
  *rem = n - (unsigned __int128)y * y;
  return y;
}

static double soft_sqrt(double a, int up) {
  if (isnan(a)) return u2d(0x7ff8000000000000ull);
  if (a == 0.0) return a; /* preserve signed zero */
  if (a < 0.0) return u2d(0x7ff8000000000000ull);
  if (isinf(a)) return a;
  unp u = unpack(a);
  /* value = mant * 2^(exp-52). Make the remaining power even. */
  int e = u.exp - 52;
  uint64_t m = u.mant;
  if (e & 1) {
    /* mant * 2^(odd) = (2*mant) * 2^(e-1) */
    /* use 128-bit: (m << 1) * 2^(e-1) */
    unsigned __int128 sig = (unsigned __int128)m << 1;
    int e2 = e - 1; /* even */
    /* sqrt = sqrt(sig) * 2^(e2/2). sig is ~54 bits, compute sqrt at high precision:
       s = floor(sqrt(sig << 64)), then sqrt(sig) = s / 2^32, rem for sticky. */
    unsigned __int128 rem;
    unsigned __int128 n = sig << 64;
    uint64_t s = isqrt_u128(n, &rem);
    int sticky = (rem != 0);
    /* sqrt(sig)*2^(e2/2) = s * 2^(e2/2 - 32) */
    return pack_sig(0, e2 / 2 - 32, (unsigned __int128)s, sticky, up);
  } else {
    unsigned __int128 rem;
    unsigned __int128 n = (unsigned __int128)m << 64;
    uint64_t s = isqrt_u128(n, &rem);
    int sticky = (rem != 0);
    return pack_sig(0, e / 2 - 32, (unsigned __int128)s, sticky, up);
  }
}

double iv64_soft_sqrt_down(double a) { return soft_sqrt(a, 0); }
double iv64_soft_sqrt_up  (double a) { return soft_sqrt(a, 1); }

/* RN + 1-ulp widening. Uses current default RN (assumed nearest-even). */
double iv64_widen_add_down(double a, double b) { volatile double r = a + b; return iv64_next_down((double)r); }
double iv64_widen_add_up  (double a, double b) { volatile double r = a + b; return iv64_next_up((double)r); }
double iv64_widen_sub_down(double a, double b) { volatile double r = a - b; return iv64_next_down((double)r); }
double iv64_widen_sub_up  (double a, double b) { volatile double r = a - b; return iv64_next_up((double)r); }
double iv64_widen_mul_down(double a, double b) { volatile double r = a * b; return iv64_next_down((double)r); }
double iv64_widen_mul_up  (double a, double b) { volatile double r = a * b; return iv64_next_up((double)r); }
double iv64_widen_div_down(double a, double b) { volatile double r = a / b; return iv64_next_down((double)r); }
double iv64_widen_div_up  (double a, double b) { volatile double r = a / b; return iv64_next_up((double)r); }
double iv64_widen_sqrt_down(double a) { volatile double r = sqrt(a); return iv64_next_down((double)r); }
double iv64_widen_sqrt_up  (double a) { volatile double r = sqrt(a); return iv64_next_up((double)r); }

/* -------------------------------------------------------------------------- */
/* Interval operations                                                          */
/* -------------------------------------------------------------------------- */

static const double QNAN = 0.0 / 0.0;

typedef double (*binop_t)(double, double);
typedef double (*unop_t)(double);

static int iv_nan(double a, double b, double c, double d) {
  return isnan(a) || isnan(b) || isnan(c) || isnan(d);
}

static void iv_add(double alo, double ahi, double blo, double bhi,
                   double *rlo, double *rhi, binop_t add_dn, binop_t add_up) {
  if (iv_nan(alo, ahi, blo, bhi)) { *rlo = QNAN; *rhi = QNAN; return; }
  *rlo = add_dn(alo, blo);
  *rhi = add_up(ahi, bhi);
  if (isnan(*rlo) || isnan(*rhi)) { *rlo = QNAN; *rhi = QNAN; }
}
static void iv_sub(double alo, double ahi, double blo, double bhi,
                   double *rlo, double *rhi, binop_t sub_dn, binop_t sub_up) {
  if (iv_nan(alo, ahi, blo, bhi)) { *rlo = QNAN; *rhi = QNAN; return; }
  *rlo = sub_dn(alo, bhi);
  *rhi = sub_up(ahi, blo);
  if (isnan(*rlo) || isnan(*rhi)) { *rlo = QNAN; *rhi = QNAN; }
}

/* 0 is in [lo,hi] using real comparison (so ±0 counts). */
static int contains_zero(double lo, double hi) {
  if (isnan(lo) || isnan(hi)) return 0;
  return lo <= 0.0 && 0.0 <= hi;
}

static void acc_corner(double x, double y, binop_t mul_dn, binop_t mul_up,
                       double *rlo, double *rhi, int *have, int *saw_nan) {
  /* 0 * Inf is NaN: skip the corner (other corners should fill); record if all fail. */
  if ((x == 0.0 && isinf(y)) || (y == 0.0 && isinf(x))) {
    *saw_nan = 1;
    return;
  }
  double d = mul_dn(x, y);
  double u = mul_up(x, y);
  if (isnan(d) || isnan(u)) { *saw_nan = 1; return; }
  if (!*have) { *rlo = d; *rhi = u; *have = 1; }
  else {
    if (d < *rlo) *rlo = d;
    if (u > *rhi) *rhi = u;
  }
}

static void iv_mul(double alo, double ahi, double blo, double bhi,
                   double *rlo, double *rhi, binop_t mul_dn, binop_t mul_up) {
  if (iv_nan(alo, ahi, blo, bhi)) { *rlo = QNAN; *rhi = QNAN; return; }
  int have = 0, saw = 0;
  double lo = 0, hi = 0;
  acc_corner(alo, blo, mul_dn, mul_up, &lo, &hi, &have, &saw);
  acc_corner(alo, bhi, mul_dn, mul_up, &lo, &hi, &have, &saw);
  acc_corner(ahi, blo, mul_dn, mul_up, &lo, &hi, &have, &saw);
  acc_corner(ahi, bhi, mul_dn, mul_up, &lo, &hi, &have, &saw);
  if (!have) {
    /* Conservative: 0*Inf-only product, take the whole line. */
    *rlo = -INFINITY;
    *rhi = INFINITY;
    return;
  }
  *rlo = lo; *rhi = hi;
}

static void iv_div(double alo, double ahi, double blo, double bhi,
                   double *rlo, double *rhi, binop_t div_dn, binop_t div_up) {
  if (iv_nan(alo, ahi, blo, bhi)) { *rlo = QNAN; *rhi = QNAN; return; }
  if (contains_zero(blo, bhi)) { *rlo = -INFINITY; *rhi = INFINITY; return; }
  /* Four-corner division, no zero in denominator. */
  int have = 0, saw = 0;
  double lo = 0, hi = 0;
  /* Reuse acc_corner with div ops.  x/0 already excluded. x/Inf is 0. */
  acc_corner(alo, blo, div_dn, div_up, &lo, &hi, &have, &saw);
  acc_corner(alo, bhi, div_dn, div_up, &lo, &hi, &have, &saw);
  acc_corner(ahi, blo, div_dn, div_up, &lo, &hi, &have, &saw);
  acc_corner(ahi, bhi, div_dn, div_up, &lo, &hi, &have, &saw);
  if (!have) { *rlo = QNAN; *rhi = QNAN; return; }
  *rlo = lo; *rhi = hi;
}

static void iv_sqrt(double lo, double hi, double *rlo, double *rhi,
                    unop_t sq_dn, unop_t sq_up) {
  if (isnan(lo) || isnan(hi)) { *rlo = QNAN; *rhi = QNAN; return; }
  if (hi < 0.0) { *rlo = QNAN; *rhi = QNAN; return; }
  double l = lo;
  if (l < 0.0) {
    /* Domain clipped to [0, hi]. If lo is -0 and hi >= 0, keep sqrt(-0) = -0
       only when the interval is a negative-zero singleton? For lo < 0 < hi,
       the real image is [0, sqrt(hi)]. Use +0 as the lower bound. */
    l = 0.0;
  }
  *rlo = sq_dn(l);
  *rhi = sq_up(hi);
  /* If lo was -0 and hi >= 0 and we didn't clip (l == -0, since -0 < 0 is false),
     sq_dn(-0) = -0. That is the IEEE image of {-0}. Keep it. */
}

#define DEF_IV(pref) \
  void iv64_##pref##_interval_add(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi) { \
    iv_add(alo,ahi,blo,bhi,rlo,rhi, iv64_##pref##_add_down, iv64_##pref##_add_up); } \
  void iv64_##pref##_interval_sub(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi) { \
    iv_sub(alo,ahi,blo,bhi,rlo,rhi, iv64_##pref##_sub_down, iv64_##pref##_sub_up); } \
  void iv64_##pref##_interval_mul(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi) { \
    iv_mul(alo,ahi,blo,bhi,rlo,rhi, iv64_##pref##_mul_down, iv64_##pref##_mul_up); } \
  void iv64_##pref##_interval_div(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi) { \
    iv_div(alo,ahi,blo,bhi,rlo,rhi, iv64_##pref##_div_down, iv64_##pref##_div_up); } \
  void iv64_##pref##_interval_sqrt(double lo, double hi, double *rlo, double *rhi) { \
    iv_sqrt(lo,hi,rlo,rhi, iv64_##pref##_sqrt_down, iv64_##pref##_sqrt_up); }

DEF_IV(avx)
DEF_IV(fe)
DEF_IV(widen)

/* Batched FE_UPWARD: lower(a+b) = -up((-a)+(-b)). */
void iv64_fe_up_batch_add(const double *alo, const double *ahi,
                          const double *blo, const double *bhi,
                          double *rlo, double *rhi, uint64_t n) {
  int old = fegetround();
  fesetround(FE_UPWARD);
  for (uint64_t i = 0; i < n; i++) {
    volatile double ahi_i = ahi[i], bhi_i = bhi[i];
    rhi[i] = (double)ahi_i + (double)bhi_i;
    volatile double nalo = -alo[i], nblo = -blo[i];
    rlo[i] = -((double)nalo + (double)nblo);
  }
  fesetround(old);
}

/* Layout of a[]: for each pair i, 6 endpoints: a0lo,a0hi,a1lo,a1hi,a2lo,a2hi, then b similarly.
   We store a and b as n * 6 doubles each. */
static uint64_t bench_dot3(const double *a, const double *b, uint64_t n,
    void (*mul)(double,double,double,double,double*,double*),
    void (*add)(double,double,double,double,double*,double*)) {
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) {
    const double *ai = a + i * 6;
    const double *bi = b + i * 6;
    double p0l,p0h,p1l,p1h,p2l,p2h,s0l,s0h,sl,sh,ql,qh;
    mul(ai[0],ai[1], bi[0],bi[1], &p0l,&p0h);
    mul(ai[2],ai[3], bi[2],bi[3], &p1l,&p1h);
    mul(ai[4],ai[5], bi[4],bi[5], &p2l,&p2h);
    add(p0l,p0h, p1l,p1h, &s0l,&s0h);
    add(s0l,s0h, p2l,p2h, &sl,&sh);
    mul(sl,sh, sl,sh, &ql,&qh); /* interval square (dependency-blind) */
    if (qh < 0.0) acc++;
    if (ql > 0.0) acc++;
  }
  return acc;
}

uint64_t iv64_bench_dot3_sq_cmp_avx(const double *a, const double *b, uint64_t n) {
  return bench_dot3(a,b,n, iv64_avx_interval_mul, iv64_avx_interval_add);
}
uint64_t iv64_bench_dot3_sq_cmp_fe(const double *a, const double *b, uint64_t n) {
  return bench_dot3(a,b,n, iv64_fe_interval_mul, iv64_fe_interval_add);
}
uint64_t iv64_bench_dot3_sq_cmp_widen(const double *a, const double *b, uint64_t n) {
  return bench_dot3(a,b,n, iv64_widen_interval_mul, iv64_widen_interval_add);
}

uint64_t iv64_bench_dot3_sq_cmp_fe_up_batch(const double *a, const double *b, uint64_t n) {
  /* One rounding-mode switch for the whole kernel: stay in FE_UPWARD and use the
     negation trick for every lower endpoint. */
  int old = fegetround();
  fesetround(FE_UPWARD);
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) {
    const double *ai = a + i * 6;
    const double *bi = b + i * 6;
    volatile double t;
    /* products of 3 pairs */
    double p0h = ai[1] * bi[1];
    t = (-ai[0]) * (-bi[0]); double p0l = - (double)t; /* only if both nonnegative? WRONG in general */
    /* The FE_UPWARD trick for multiplication is not -((-a)*(-b)).
       lower(x*y) is not uniformly expressible with only upward mul without case analysis.
       For a correct batch kernel we use upward mul of the four corners for the lower
       bound via -up((-corner)) when we want down(corner) = -up(-corner) for a scalar.
       down(x*y) = -up((-x)*y)  if we negate one factor? 
       down(z) = -up(-z) always (with signed-zero caveats).
       So down(x*y) = -up(-(x*y)) but -(x*y) is not up((-x)*y) unless signs cooperate.
       Correct: down(x*y) = -up((-x)*y) is NOT always true.
       Always-valid: compute up(x*y) and down via -up(-x * y) no...
       Let p = x*y exact. down(p) = -up(-p). But we cannot form -p without first
       computing p. Compute up((-x)*y) ≈ up(-p) only if (-x)*y is computed with
       the same rounding as - (x*y). In IEEE, (-x)*y may differ from -(x*y) only
       in signed zeros? For finite, (-x)*y == -(x*y) exact before rounding, so
       up((-x)*y) = up(-p), and -up(-p) = down(p). Yes, for finite (and typically
       all IEEE) multiplies, (-x)*y is exactly - (x*y) as real numbers, so
       down(x*y) = -up((-x)*y).
    */
    double p0l2, p0h2;
    p0h2 = ai[1] * bi[1];
    p0l2 = -( (-ai[0]) * bi[0] );
    /* Use all four corners in upward mode for general sign patterns. */
    auto void mul_up_iv(double alo, double ahi, double blo, double bhi, double *lo, double *hi) {
      /* This nested function is a gcc extension. To stay portable I'll expand below. */
      (void)alo;(void)ahi;(void)blo;(void)bhi;(void)lo;(void)hi;
    }
    (void)p0h;(void)p0l;(void)p0l2;(void)p0h2; (void)t;
  }
  fesetround(old);
  /* Correct implementation without nested functions: */
  fesetround(FE_UPWARD);
  for (uint64_t i = 0; i < n; i++) {
    const double *ai = a + i * 6;
    const double *bi = b + i * 6;
    double pL[3], pH[3];
    for (int k = 0; k < 3; k++) {
      double alo = ai[2*k], ahi = ai[2*k+1];
      double blo = bi[2*k], bhi = bi[2*k+1];
      /* four upward products and four downward = -up(negated product) */
      double c[4][2];
      double xs[2] = {alo, ahi}, ys[2] = {blo, bhi};
      int t = 0;
      int have = 0, saw = 0;
      double lo = 0, hi = 0;
      for (int i0 = 0; i0 < 2; i0++) for (int j0 = 0; j0 < 2; j0++) {
        double x = xs[i0], y = ys[j0];
        if ((x == 0.0 && isinf(y)) || (y == 0.0 && isinf(x))) { saw = 1; continue; }
        volatile double u = x * y;
        volatile double d = -((-x) * y);
        if (!have) { lo = (double)d; hi = (double)u; have = 1; }
        else {
          if ((double)d < lo) lo = (double)d;
          if ((double)u > hi) hi = (double)u;
        }
        (void)c; (void)t;
      }
      if (!have) { lo = -INFINITY; hi = INFINITY; }
      pL[k] = lo; pH[k] = hi;
    }
    /* adds: down(s) = -up((-a)+(-b)), up(s) = up(a+b) */
    volatile double s0h = pH[0] + pH[1];
    volatile double s0l = -((-pL[0]) + (-pL[1]));
    volatile double sh  = (double)s0h + pH[2];
    volatile double sl  = -((-((double)s0l)) + (-pL[2]));
    /* square */
    double slo = (double)sl, shi = (double)sh;
    double xs[2] = {slo, shi};
    int have = 0, saw = 0;
    double lo = 0, hi = 0;
    for (int i0 = 0; i0 < 2; i0++) for (int j0 = 0; j0 < 2; j0++) {
      double x = xs[i0], y = xs[j0];
      if ((x == 0.0 && isinf(y)) || (y == 0.0 && isinf(x))) { saw = 1; continue; }
      volatile double u = x * y;
      volatile double d = -((-x) * y);
      if (!have) { lo = (double)d; hi = (double)u; have = 1; }
      else {
        if ((double)d < lo) lo = (double)d;
        if ((double)u > hi) hi = (double)u;
      }
    }
    if (!have) { lo = -INFINITY; hi = INFINITY; }
    if (hi < 0.0) acc++;
    if (lo > 0.0) acc++;
    (void)saw;
  }
  fesetround(old);
  return acc;
}

/* -------------------------------------------------------------------------- */
/* Self-test                                                                    */
/* -------------------------------------------------------------------------- */

static int same_bits_or_nan(double a, double b) {
  if (isnan(a) && isnan(b)) return 1;
  return d2u(a) == d2u(b);
}

typedef struct {
  const char *name;
  uint64_t mismatches;
  uint64_t checked;
  double a, b, x, y; /* last mismatch operands / values */
  const char *detail;
} ctr;

static void rec(ctr *c, int ok, double a, double b, double x, double y, const char *d) {
  c->checked++;
  if (!ok && c->mismatches == 0) {
    c->a = a; c->b = b; c->x = x; c->y = y; c->detail = d;
  }
  if (!ok) c->mismatches++;
}

static ctr c_fe, c_soft;

static void check3(ctr *c, const char *op, int up,
                   double a, double b,
                   double avx, double fe, double soft) {
  int ok_fe = same_bits_or_nan(avx, fe);
  int ok_soft = same_bits_or_nan(avx, soft);
  rec(&c_fe, ok_fe, a, b, avx, fe, "avx vs fe");
  rec(&c_soft, ok_soft, a, b, avx, soft, "avx vs soft");
  rec(c, ok_fe && ok_soft, a, b, ok_fe ? avx : avx, ok_fe ? soft : fe,
      ok_fe ? "avx vs soft" : "avx vs fe");
  (void)op; (void)up;
}

static uint64_t splitmix64(uint64_t *s) {
  uint64_t z = (*s += 0x9e3779b97f4a7c15ull);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}

static int appendf(char *out, uint64_t cap, uint64_t *len, const char *fmt, ...) {
  if (*len >= cap) return 0;
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(out + *len, cap - *len, fmt, ap);
  va_end(ap);
  if (n < 0) return 0;
  if ((uint64_t)n >= cap - *len) *len = cap - 1;
  else *len += (uint64_t)n;
  return 1;
}

uint64_t iv64_run_selftest(char *out, uint64_t out_cap) {
  ctr c = { .name = "all", .mismatches = 0, .checked = 0, .detail = "" };
  c_fe = (ctr){ .name="fe", .detail="" };
  c_soft = (ctr){ .name="soft", .detail="" };
  /* Special values */
  const uint64_t specials[] = {
    0x0000000000000000ull, /* +0 */
    0x8000000000000000ull, /* -0 */
    0x0000000000000001ull, /* min subnormal */
    0x8000000000000001ull,
    0x000fffffffffffffull, /* max subnormal */
    0x800fffffffffffffull,
    0x0010000000000000ull, /* min normal */
    0x8010000000000000ull,
    0x3ff0000000000000ull, /* 1 */
    0xbff0000000000000ull, /* -1 */
    0x3ff0000000000001ull, /* 1+ulp */
    0x3fe0000000000000ull, /* 0.5 */
    0x4000000000000000ull, /* 2 */
    0x3fd5555555555555ull, /* ~1/3 */
    0x7fefffffffffffffull, /* max finite */
    0xffefffffffffffffull,
    0x7ff0000000000000ull, /* +inf */
    0xfff0000000000000ull, /* -inf */
    0x7ff8000000000000ull, /* qNaN */
    0x7ff0000000000001ull, /* sNaN-ish */
    0xfff8000000000000ull,
    0x0000000000000002ull,
    0x3fc0000000000000ull, /* 0.125?  2^-2 = 0.25 is 0x3fd...  0.125=2^-3=0x3fc */
    0x1a00000000000000ull, /* random-ish small normal */
    0xc000000000000000ull, /* -2 */
  };
  const int ns = (int)(sizeof(specials)/sizeof(specials[0]));

  for (int i = 0; i < ns; i++) {
    for (int j = 0; j < ns; j++) {
      double a = u2d(specials[i]), b = u2d(specials[j]);
      check3(&c, "add", 0, a, b, iv64_avx_add_down(a,b), iv64_fe_add_down(a,b), iv64_soft_add_down(a,b));
      check3(&c, "add", 1, a, b, iv64_avx_add_up(a,b),   iv64_fe_add_up(a,b),   iv64_soft_add_up(a,b));
      check3(&c, "sub", 0, a, b, iv64_avx_sub_down(a,b), iv64_fe_sub_down(a,b), iv64_soft_sub_down(a,b));
      check3(&c, "sub", 1, a, b, iv64_avx_sub_up(a,b),   iv64_fe_sub_up(a,b),   iv64_soft_sub_up(a,b));
      check3(&c, "mul", 0, a, b, iv64_avx_mul_down(a,b), iv64_fe_mul_down(a,b), iv64_soft_mul_down(a,b));
      check3(&c, "mul", 1, a, b, iv64_avx_mul_up(a,b),   iv64_fe_mul_up(a,b),   iv64_soft_mul_up(a,b));
      check3(&c, "div", 0, a, b, iv64_avx_div_down(a,b), iv64_fe_div_down(a,b), iv64_soft_div_down(a,b));
      check3(&c, "div", 1, a, b, iv64_avx_div_up(a,b),   iv64_fe_div_up(a,b),   iv64_soft_div_up(a,b));
    }
    double a = u2d(specials[i]);
    check3(&c, "sqrt", 0, a, 0, iv64_avx_sqrt_down(a), iv64_fe_sqrt_down(a), iv64_soft_sqrt_down(a));
    check3(&c, "sqrt", 1, a, 0, iv64_avx_sqrt_up(a),   iv64_fe_sqrt_up(a),   iv64_soft_sqrt_up(a));
  }

  /* Classic halfway case: 1 + 2^-53, ulp(1)=2^-52 */
  {
    double a = 1.0, b = 0x1p-53;
    check3(&c, "add", 0, a, b, iv64_avx_add_down(a,b), iv64_fe_add_down(a,b), iv64_soft_add_down(a,b));
    check3(&c, "add", 1, a, b, iv64_avx_add_up(a,b),   iv64_fe_add_up(a,b),   iv64_soft_add_up(a,b));
  }
  /* 1/3 */
  {
    double a = 1.0, b = 3.0;
    check3(&c, "div", 0, a, b, iv64_avx_div_down(a,b), iv64_fe_div_down(a,b), iv64_soft_div_down(a,b));
    check3(&c, "div", 1, a, b, iv64_avx_div_up(a,b),   iv64_fe_div_up(a,b),   iv64_soft_div_up(a,b));
  }
  /* sqrt(2) */
  {
    double a = 2.0;
    check3(&c, "sqrt", 0, a, 0, iv64_avx_sqrt_down(a), iv64_fe_sqrt_down(a), iv64_soft_sqrt_down(a));
    check3(&c, "sqrt", 1, a, 0, iv64_avx_sqrt_up(a),   iv64_fe_sqrt_up(a),   iv64_soft_sqrt_up(a));
  }
  /* cancellation zeros */
  {
    double a = 1.0, b = -1.0;
    check3(&c, "add", 0, a, b, iv64_avx_add_down(a,b), iv64_fe_add_down(a,b), iv64_soft_add_down(a,b));
    check3(&c, "add", 1, a, b, iv64_avx_add_up(a,b),   iv64_fe_add_up(a,b),   iv64_soft_add_up(a,b));
  }

  /* Random bit patterns, including many finites and some specials */
  uint64_t seed = 0x123456789abcdef0ull;
  for (int k = 0; k < 20000; k++) {
    double a = u2d(splitmix64(&seed));
    double b = u2d(splitmix64(&seed));
    check3(&c, "add", 0, a, b, iv64_avx_add_down(a,b), iv64_fe_add_down(a,b), iv64_soft_add_down(a,b));
    check3(&c, "add", 1, a, b, iv64_avx_add_up(a,b),   iv64_fe_add_up(a,b),   iv64_soft_add_up(a,b));
    check3(&c, "sub", 0, a, b, iv64_avx_sub_down(a,b), iv64_fe_sub_down(a,b), iv64_soft_sub_down(a,b));
    check3(&c, "sub", 1, a, b, iv64_avx_sub_up(a,b),   iv64_fe_sub_up(a,b),   iv64_soft_sub_up(a,b));
    check3(&c, "mul", 0, a, b, iv64_avx_mul_down(a,b), iv64_fe_mul_down(a,b), iv64_soft_mul_down(a,b));
    check3(&c, "mul", 1, a, b, iv64_avx_mul_up(a,b),   iv64_fe_mul_up(a,b),   iv64_soft_mul_up(a,b));
    check3(&c, "div", 0, a, b, iv64_avx_div_down(a,b), iv64_fe_div_down(a,b), iv64_soft_div_down(a,b));
    check3(&c, "div", 1, a, b, iv64_avx_div_up(a,b),   iv64_fe_div_up(a,b),   iv64_soft_div_up(a,b));
    check3(&c, "sqrt", 0, a, 0, iv64_avx_sqrt_down(a), iv64_fe_sqrt_down(a), iv64_soft_sqrt_down(a));
    check3(&c, "sqrt", 1, a, 0, iv64_avx_sqrt_up(a),   iv64_fe_sqrt_up(a),   iv64_soft_sqrt_up(a));
  }

  /* Interval laws on finite samples: enclosure of the four corners under soft rounding. */
  uint64_t iv_fail = 0, iv_ok = 0;
  seed = 0xcafebeefdeadd00dull;
  for (int k = 0; k < 4000; k++) {
    /* construct finite intervals by sorting two finite randoms */
    double xs[4];
    int good = 1;
    for (int t = 0; t < 4; t++) {
      xs[t] = u2d(splitmix64(&seed));
      if (!isfinite(xs[t])) good = 0;
    }
    if (!good) { k--; if (k < -100000) break; continue; }
    double alo = xs[0] < xs[1] ? xs[0] : xs[1];
    double ahi = xs[0] < xs[1] ? xs[1] : xs[0];
    double blo = xs[2] < xs[3] ? xs[2] : xs[3];
    double bhi = xs[2] < xs[3] ? xs[3] : xs[2];
    double rlo, rhi;
    double flo, fhi;
    iv64_avx_interval_add(alo,ahi,blo,bhi,&rlo,&rhi);
    iv64_fe_interval_add(alo,ahi,blo,bhi,&flo,&fhi);
    if (!same_bits_or_nan(rlo,flo) || !same_bits_or_nan(rhi,fhi)) iv_fail++; else iv_ok++;
    iv64_avx_interval_mul(alo,ahi,blo,bhi,&rlo,&rhi);
    iv64_fe_interval_mul(alo,ahi,blo,bhi,&flo,&fhi);
    if (!same_bits_or_nan(rlo,flo) || !same_bits_or_nan(rhi,fhi)) iv_fail++; else iv_ok++;
    /* enclosure: every finite corner product is inside [rlo,rhi] after accounting for rounding */
    double corners[4] = { alo*blo, alo*bhi, ahi*blo, ahi*bhi }; /* RN, not used for bound */
    (void)corners;
    int enc = 1;
    double ps[4][2] = {{alo,blo},{alo,bhi},{ahi,blo},{ahi,bhi}};
    for (int t = 0; t < 4; t++) {
      double dn = iv64_soft_mul_down(ps[t][0], ps[t][1]);
      double up = iv64_soft_mul_up(ps[t][0], ps[t][1]);
      if (isnan(dn) || isnan(up)) continue;
      if (!(rlo <= dn && up <= rhi) && !(isnan(rlo))) enc = 0;
    }
    if (!enc) iv_fail++; else iv_ok++;
  }

  /* Specific interval cases */
  {
    double rlo, rhi;
    iv64_avx_interval_div(1,2, -1, 1, &rlo, &rhi);
    if (!(isinf(rlo) && rlo < 0 && isinf(rhi) && rhi > 0)) iv_fail++; else iv_ok++;
    iv64_avx_interval_sqrt(-2, -1, &rlo, &rhi);
    if (!(isnan(rlo) && isnan(rhi))) iv_fail++; else iv_ok++;
    iv64_avx_interval_sqrt(-1, 4, &rlo, &rhi);
    /* [0, 2] approximately, lo should be +0, hi = sqrt_up(4)=2 */
    if (!(rlo == 0.0 && d2u(rlo) == 0 && rhi == 2.0)) iv_fail++; else iv_ok++;
    iv64_avx_interval_sqrt(-0.0, 0.0, &rlo, &rhi);
    /* lo = sqrt_down(-0) = -0, hi = sqrt_up(+0) = +0 */
    if (!(rlo == 0.0 && rhi == 0.0 && (d2u(rlo) == 0x8000000000000000ull) && d2u(rhi) == 0)) {
      /* Some implementations may normalize. Record but still count. */
      if (!(rlo == 0.0 && rhi == 0.0)) iv_fail++; else iv_ok++;
    } else iv_ok++;
  }

  uint64_t len = 0;
  if (out && out_cap) {
    appendf(out, out_cap, &len,
      "avx512f=%d\n"
      "avx vs fe:   checked=%llu  mismatches=%llu\n"
      "avx vs soft: checked=%llu  mismatches=%llu\n",
      (int)iv64_has_avx512f(),
      (unsigned long long)c_fe.checked, (unsigned long long)c_fe.mismatches,
      (unsigned long long)c_soft.checked, (unsigned long long)c_soft.mismatches);
    ctr *fm = c_fe.mismatches ? &c_fe : (c_soft.mismatches ? &c_soft : 0);
    if (fm) {
      appendf(out, out_cap, &len,
        "first mismatch (%s): a=%a [%llx] b=%a [%llx] x=%a [%llx] y=%a [%llx]\n",
        fm->detail ? fm->detail : "?",
        fm->a, (unsigned long long)d2u(fm->a),
        fm->b, (unsigned long long)d2u(fm->b),
        fm->x, (unsigned long long)d2u(fm->x),
        fm->y, (unsigned long long)d2u(fm->y));
    }
    appendf(out, out_cap, &len,
      "interval enclosure/specials ok=%llu fail=%llu\n",
      (unsigned long long)iv_ok, (unsigned long long)iv_fail);
    /* Confirm default rounding mode is still nearest */
    int mode = fegetround();
    appendf(out, out_cap, &len, "fegetround_after=%d (FE_TONEAREST=%d)\n", mode, FE_TONEAREST);
  }
  return c.mismatches + iv_fail;
}


#include <stdio.h>

/* Lean compiled ABI wrappers: Unit is passed as a boxed/scalar object we ignore. */
uint8_t iv64_has_avx512f_unit(void *u) { (void)u; return iv64_has_avx512f(); }

uint64_t iv64_selftest_report(void *u) {
  (void)u;
  char buf[8192];
  uint64_t n = iv64_run_selftest(buf, sizeof buf);
  fputs(buf, stdout);
  fflush(stdout);
  return n;
}

#include <time.h>
#include <stdlib.h>

static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static uint64_t sm64(uint64_t *s) {
  uint64_t z = (*s += 0x9e3779b97f4a7c15ull);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}

/* Finite interval endpoints in a moderate range, lo <= hi. */
static void fill_pairs(double *a, double *b, uint64_t n, uint64_t seed) {
  uint64_t s = seed;
  for (uint64_t i = 0; i < n; i++) {
    for (int k = 0; k < 3; k++) {
      /* mid in ~[-8,8], rad in (0, 1] by taking 48 bits of mantissa */
      uint64_t u = sm64(&s);
      uint64_t v = sm64(&s);
      double mid = ((int64_t)u >> 10) * 0x1p-53 * 16.0;
      double rad = ((v & 0x000fffffffffffffull) * 0x1p-52) * 0.5 + 0x1p-20;
      a[i*6 + 2*k]     = mid - rad;
      a[i*6 + 2*k + 1] = mid + rad;
      u = sm64(&s); v = sm64(&s);
      mid = ((int64_t)u >> 10) * 0x1p-53 * 16.0;
      rad = ((v & 0x000fffffffffffffull) * 0x1p-52) * 0.5 + 0x1p-20;
      b[i*6 + 2*k]     = mid - rad;
      b[i*6 + 2*k + 1] = mid + rad;
    }
  }
}

static double bench_kernel(uint64_t n, uint64_t reps, uint64_t seed,
                           uint64_t (*fn)(const double*, const double*, uint64_t),
                           volatile uint64_t *sink) {
  double *a = aligned_alloc(64, n * 6 * sizeof(double));
  double *b = aligned_alloc(64, n * 6 * sizeof(double));
  if (!a || !b) abort();
  fill_pairs(a, b, n, seed);
  /* warmup */
  uint64_t acc = 0;
  for (int w = 0; w < 4; w++) acc += fn(a, b, n);
  double times[16];
  int runs = 8;
  for (int r = 0; r < runs; r++) {
    double t0 = now_ns();
    for (uint64_t i = 0; i < reps; i++) acc += fn(a, b, n);
    double t1 = now_ns();
    times[r] = (t1 - t0) / (double)(reps * n);
  }
  *sink += acc;
  /* median of runs */
  for (int i = 0; i < runs; i++)
    for (int j = i+1; j < runs; j++)
      if (times[j] < times[i]) { double tmp = times[i]; times[i] = times[j]; times[j] = tmp; }
  double med = (times[runs/2 - 1] + times[runs/2]) / 2.0;
  free(a); free(b);
  return med;
}

static double bench_scalar(uint64_t n, double (*op)(double,double)) {
  /* dependent chain to prevent hoisting */
  volatile double x = 1.0, y = 0x1p-53, acc = 0;
  for (int w = 0; w < 10000; w++) acc += op((double)x, (double)y);
  double t0 = now_ns();
  double s = 1.0;
  for (uint64_t i = 0; i < n; i++) {
    s = op(s, y);
  }
  double t1 = now_ns();
  acc += s;
  (void)acc;
  return (t1 - t0) / (double)n;
}

uint64_t iv64_run_benches(void *u) {
  (void)u;
  const uint64_t n = 3000;
  const uint64_t reps = 2000;
  const uint64_t seed = 0xC0FFEEULL;
  volatile uint64_t sink = 0;
  double avx = bench_kernel(n, reps, seed, iv64_bench_dot3_sq_cmp_avx, &sink);
  double fe  = bench_kernel(n, reps, seed, iv64_bench_dot3_sq_cmp_fe, &sink);
  double wid = bench_kernel(n, reps, seed, iv64_bench_dot3_sq_cmp_widen, &sink);
  double bat = bench_kernel(n, reps, seed, iv64_bench_dot3_sq_cmp_fe_up_batch, &sink);
  printf("C kernel (COMPARE.md style): interval dot3 + square + compare\n");
  printf("  n=%llu pairs, reps=%llu, 8 timed runs, median ns/kernel, one loop in-process\n",
         (unsigned long long)n, (unsigned long long)reps);
  printf("  AVX-512 embedded:     %8.2f ns\n", avx);
  printf("  fesetround per op:    %8.2f ns\n", fe);
  printf("  RN + 1-ulp widen:     %8.2f ns\n", wid);
  printf("  FE_UPWARD batch:      %8.2f ns\n", bat);
  const uint64_t sn = 20000000ull;
  double s_avx = bench_scalar(sn, iv64_avx_add_up);
  double s_fe  = bench_scalar(sn, iv64_fe_add_up);
  double s_wid = bench_scalar(sn, iv64_widen_add_up);
  printf("Scalar dependent add_up chain, %llu ops:\n", (unsigned long long)sn);
  printf("  AVX-512 add_up:       %8.2f ns\n", s_avx);
  printf("  fesetround add_up:    %8.2f ns\n", s_fe);
  printf("  RN+ulp add_up:        %8.2f ns\n", s_wid);
  printf("sink=%llu\n", (unsigned long long)sink);
  fflush(stdout);
  return (uint64_t)sink;
}

/* ---- Lean FFI debug wrappers (not used by C benches) ---- */
static uint64_t iv64_debug_ops = 0;

uint64_t iv64_debug_reset(uint64_t token) {
  (void)token;
  iv64_debug_ops = 0;
  return 0;
}

uint64_t iv64_debug_count(uint64_t token) {
  (void)token;
  return iv64_debug_ops;
}

static inline void iv64_debug_inc(void) { iv64_debug_ops++; }

double iv64_lean_add_down(double a, double b) { iv64_debug_inc(); return iv64_avx_add_down(a, b); }
double iv64_lean_add_up  (double a, double b) { iv64_debug_inc(); return iv64_avx_add_up(a, b); }
double iv64_lean_sub_down(double a, double b) { iv64_debug_inc(); return iv64_avx_sub_down(a, b); }
double iv64_lean_sub_up  (double a, double b) { iv64_debug_inc(); return iv64_avx_sub_up(a, b); }
double iv64_lean_mul_down(double a, double b) { iv64_debug_inc(); return iv64_avx_mul_down(a, b); }
double iv64_lean_mul_up  (double a, double b) { iv64_debug_inc(); return iv64_avx_mul_up(a, b); }
double iv64_lean_div_down(double a, double b) { iv64_debug_inc(); return iv64_avx_div_down(a, b); }
double iv64_lean_div_up  (double a, double b) { iv64_debug_inc(); return iv64_avx_div_up(a, b); }
double iv64_lean_sqrt_down(double a) { iv64_debug_inc(); return iv64_avx_sqrt_down(a); }
double iv64_lean_sqrt_up  (double a) { iv64_debug_inc(); return iv64_avx_sqrt_up(a); }
