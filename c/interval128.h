/* Interval128 C kernels: double-double interval arithmetic.

   Bit-identical to the Lean specification in Interval128/DD.lean and
   Interval128/Interval.lean (the test executable checks this). Header-only
   (static inline) so the Lean wrappers (interval128.c) and the standalone
   benchmark compile the same code.

   Backend (same selection as Interval64):
     x86_64 + AVX-512F  : directed ops and directed FMA by embedded rounding.
     otherwise (aarch64): directed ops by RN + exact error term (iv64_rnerr.h);
                          the error-free FMAs (a*b - RN(a*b), a - RN(a/b)*b,
                          a - RN(sqrt a)^2) by plain RN fma, which is exact in
                          the guarded range, with the IEEE exact-zero sign
                          (-0 for RD, +0 for RU); outside it fesetround + fma.
   Requires -ffp-contract=off -frounding-math (no contraction of a*b+c). */
#ifndef INTERVAL128_H
#define INTERVAL128_H

#include <math.h>
#include <float.h>
#include <fenv.h>
#include <stdint.h>
#include <string.h>
#include "iv64_rnerr.h"

#if defined(__x86_64__) && defined(__AVX512F__) && !defined(IV64_FORCE_RNERR)
#define I128_AVX512 1
#include <immintrin.h>
#else
#define I128_AVX512 0
#endif

typedef struct { double lh, ll, uh, ul; } i128_t;
typedef struct { double hi, lo; } i128_dd;
typedef struct { double lo, hi; } i128_iv64;

#ifndef I128_FE_HOOK
#define I128_FE_HOOK() ((void)0)
#endif

/* fesetround fma: correct directed FMA anywhere (slow; saves/restores the mode). */
static inline double i128_fe_fma(double a, double b, double c, int up) {
  I128_FE_HOOK();
  int old = fegetround();
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  volatile double va = a, vb = b, vc = c;
  volatile double r = fma(va, vb, vc);
  fesetround(old);
  return r;
}

#if I128_AVX512
#define I128_RD (_MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC)
#define I128_RU (_MM_FROUND_TO_POS_INF | _MM_FROUND_NO_EXC)
#define I128_BIN(name, intr, mode) \
  static inline double name(double a, double b) { \
    return _mm_cvtsd_f64(intr(_mm_set_sd(a), _mm_set_sd(b), mode)); }
I128_BIN(add_dn, _mm_add_round_sd, I128_RD)
I128_BIN(add_up, _mm_add_round_sd, I128_RU)
I128_BIN(sub_dn, _mm_sub_round_sd, I128_RD)
I128_BIN(sub_up, _mm_sub_round_sd, I128_RU)
I128_BIN(mul_dn, _mm_mul_round_sd, I128_RD)
I128_BIN(mul_up, _mm_mul_round_sd, I128_RU)
I128_BIN(div_dn, _mm_div_round_sd, I128_RD)
I128_BIN(div_up, _mm_div_round_sd, I128_RU)
static inline double sqrt_dn(double a) { __m128d x = _mm_set_sd(a); return _mm_cvtsd_f64(_mm_sqrt_round_sd(x, x, I128_RD)); }
static inline double sqrt_up(double a) { __m128d x = _mm_set_sd(a); return _mm_cvtsd_f64(_mm_sqrt_round_sd(x, x, I128_RU)); }
static inline double fma_dn(double a, double b, double c) {
  return _mm_cvtsd_f64(_mm_fmadd_round_sd(_mm_set_sd(a), _mm_set_sd(b), _mm_set_sd(c), I128_RD)); }
static inline double fma_up(double a, double b, double c) {
  return _mm_cvtsd_f64(_mm_fmadd_round_sd(_mm_set_sd(a), _mm_set_sd(b), _mm_set_sd(c), I128_RU)); }
/* Error-free patterns: plain directed FMA. */
static inline double perr_dn(double a, double b, double p) { return fma_dn(a, b, -p); }
static inline double perr_up(double a, double b, double p) { return fma_up(a, b, -p); }
static inline double drem_dn(double q, double b, double a) { return fma_dn(-q, b, a); }
static inline double drem_up(double q, double b, double a) { return fma_up(-q, b, a); }
static inline double srem_dn(double s, double a) { return fma_dn(-s, s, a); }
static inline double srem_up(double s, double a) { return fma_up(-s, s, a); }
#else
static inline double add_dn(double a, double b) { return iv64r_add(a, b, 0); }
static inline double add_up(double a, double b) { return iv64r_add(a, b, 1); }
static inline double sub_dn(double a, double b) { return iv64r_sub(a, b, 0); }
static inline double sub_up(double a, double b) { return iv64r_sub(a, b, 1); }
static inline double mul_dn(double a, double b) { return iv64r_mul(a, b, 0); }
static inline double mul_up(double a, double b) { return iv64r_mul(a, b, 1); }
static inline double div_dn(double a, double b) { return iv64r_div(a, b, 0); }
static inline double div_up(double a, double b) { return iv64r_div(a, b, 1); }
static inline double sqrt_dn(double a) { return iv64r_sqrt(a, 0); }
static inline double sqrt_up(double a) { return iv64r_sqrt(a, 1); }
static inline double fma_dn(double a, double b, double c) { return i128_fe_fma(a, b, c, 0); }
static inline double fma_up(double a, double b, double c) { return i128_fe_fma(a, b, c, 1); }
/* Exact RN fma result, with the IEEE exact-zero sign of the directed mode. */
static inline double i128_exact(double r, int up) { return r == 0 ? (up ? 0.0 : -0.0) : r; }
/* a*b - p, p = RN(a*b): exact when 2^-968 <= |p| <= max (error >= 2^-1074 grid). */
static inline double perr_dir(double a, double b, double p, int up) {
  double ap = fabs(p);
  if (ap >= 0x1p-968 && ap <= DBL_MAX) return i128_exact(fma(a, b, -p), up);
  return i128_fe_fma(a, b, -p, up);
}
/* a - q*b, q = RN(a/b): exact for normal q, b and |a| >= 2^-968 (Interval64's guard). */
static inline double drem_dir(double q, double b, double a, int up) {
  double aq = fabs(q), ab = fabs(b), aa = fabs(a);
  if (aq >= 0x1p-1022 && aq <= DBL_MAX && ab >= 0x1p-1022 && ab <= DBL_MAX &&
      aa >= 0x1p-968 && aa <= DBL_MAX)
    return i128_exact(fma(-q, b, a), up);
  return i128_fe_fma(-q, b, a, up);
}
/* a - s*s, s = RN(sqrt a): exact for 2^-968 <= a <= max. */
static inline double srem_dir(double s, double a, int up) {
  if (a >= 0x1p-968 && a <= DBL_MAX) return i128_exact(fma(-s, s, a), up);
  return i128_fe_fma(-s, s, a, up);
}
static inline double perr_dn(double a, double b, double p) { return perr_dir(a, b, p, 0); }
static inline double perr_up(double a, double b, double p) { return perr_dir(a, b, p, 1); }
static inline double drem_dn(double q, double b, double a) { return drem_dir(q, b, a, 0); }
static inline double drem_up(double q, double b, double a) { return drem_dir(q, b, a, 1); }
static inline double srem_dn(double s, double a) { return srem_dir(s, a, 0); }
static inline double srem_up(double s, double a) { return srem_dir(s, a, 1); }
#endif

/* ---------- double-double endpoint kernels (Interval128/DD.lean) ---------- */

static inline int i128_fin(double x) { return isfinite(x); }
static inline int dd_fin(i128_dd d) { return isfinite(d.hi) && isfinite(d.lo); }
static inline int dd_nonneg(double h, double l) { return -h <= l; }
static inline int dd_nonpos(double h, double l) { return l <= -h; }
static inline int dd_pos(double h, double l) { return -h < l; }
static inline int dd_neg(double h, double l) { return l < -h; }

static inline i128_dd dd_add_lo(double ah, double al, double bh, double bl) {
  double s = ah + bh, bb = s - ah;
  double e = add_dn(sub_dn(ah, sub_up(s, bb)), sub_dn(bh, bb));
  double t = al + bl, cc = t - al;
  double f = add_dn(sub_dn(al, sub_up(t, cc)), sub_dn(bl, cc));
  double e2 = add_dn(e, t);
  double s2 = s + e2;
  double g = add_dn(sub_dn(s, s2), e2);
  double e3 = add_dn(g, f);
  double s3 = s2 + e3;
  return (i128_dd){ s3, add_dn(sub_dn(s2, s3), e3) };
}

static inline i128_dd dd_add_hi(double ah, double al, double bh, double bl) {
  double s = ah + bh, bb = s - ah;
  double e = add_up(sub_up(ah, sub_dn(s, bb)), sub_up(bh, bb));
  double t = al + bl, cc = t - al;
  double f = add_up(sub_up(al, sub_dn(t, cc)), sub_up(bl, cc));
  double e2 = add_up(e, t);
  double s2 = s + e2;
  double g = add_up(sub_up(s, s2), e2);
  double e3 = add_up(g, f);
  double s3 = s2 + e3;
  return (i128_dd){ s3, add_up(sub_up(s2, s3), e3) };
}

static inline i128_dd dd_mul_lo(double ah, double al, double bh, double bl) {
  double p = ah * bh;
  double e = perr_dn(ah, bh, p);
  double c = add_dn(add_dn(mul_dn(ah, bl), mul_dn(al, bh)), mul_dn(al, bl));
  double e2 = add_dn(e, c);
  double s = p + e2;
  return (i128_dd){ s, add_dn(sub_dn(p, s), e2) };
}

static inline i128_dd dd_mul_hi(double ah, double al, double bh, double bl) {
  double p = ah * bh;
  double e = perr_up(ah, bh, p);
  double c = add_up(add_up(mul_up(ah, bl), mul_up(al, bh)), mul_up(al, bl));
  double e2 = add_up(e, c);
  double s = p + e2;
  return (i128_dd){ s, add_up(sub_up(p, s), e2) };
}

static inline double dd_quot_lo(double r, double dlo, double dhi) {
  if (0 <= r) return (0 < dhi && dhi < INFINITY) ? div_dn(r, dhi) : -INFINITY;
  return (0 < dlo && dlo < INFINITY) ? div_dn(r, dlo) : -INFINITY;
}
static inline double dd_quot_hi(double r, double dlo, double dhi) {
  if (0 <= r) return (0 < dlo && dlo < INFINITY) ? div_up(r, dlo) : INFINITY;
  return (0 < dhi && dhi < INFINITY) ? div_up(r, dhi) : INFINITY;
}

static inline i128_dd dd_div_lo(double ah, double al, double bh, double bl) {
  double q1 = ah / bh;
  double r1 = drem_dn(q1, bh, ah);
  double q2 = fma(-q1, bl, r1 + al) / bh;
  double x = add_dn(add_dn(r1, al), mul_dn(-q1, bl));
  double p2 = q2 * bh;
  double e2 = perr_up(q2, bh, p2);
  double r = add_dn(sub_dn(sub_dn(x, p2), e2), mul_dn(-q2, bl));
  double c = dd_quot_lo(r, add_dn(bh, bl), add_up(bh, bl));
  double s = q1 + q2;
  double e = add_dn(add_dn(sub_dn(q1, s), q2), c);
  double s2 = s + e;
  return (i128_dd){ s2, add_dn(sub_dn(s, s2), e) };
}

static inline i128_dd dd_div_hi(double ah, double al, double bh, double bl) {
  double q1 = ah / bh;
  double r1 = drem_up(q1, bh, ah);
  double q2 = fma(-q1, bl, r1 + al) / bh;
  double x = add_up(add_up(r1, al), mul_up(-q1, bl));
  double p2 = q2 * bh;
  double e2 = perr_dn(q2, bh, p2);
  double r = add_up(sub_up(sub_up(x, p2), e2), mul_up(-q2, bl));
  double c = dd_quot_hi(r, add_dn(bh, bl), add_up(bh, bl));
  double s = q1 + q2;
  double e = add_up(add_up(sub_up(q1, s), q2), c);
  double s2 = s + e;
  return (i128_dd){ s2, add_up(sub_up(s, s2), e) };
}

static inline i128_dd dd_sqrt_lo(double ah, double al) {
  double s = sqrt(ah);
  if (!(0 < s)) return (i128_dd){ -INFINITY, 0.0 };
  double r = add_dn(srem_dn(s, ah), al);
  double c = dd_quot_lo(r, add_dn(sqrt_dn(add_dn(ah, al)), s), add_up(sqrt_up(add_up(ah, al)), s));
  double s2 = s + c;
  return (i128_dd){ s2, add_dn(sub_dn(s, s2), c) };
}

static inline i128_dd dd_sqrt_hi(double ah, double al) {
  double s = sqrt(ah);
  if (!(0 < s)) return (i128_dd){ INFINITY, 0.0 };
  double r = add_up(srem_up(s, ah), al);
  double c = dd_quot_hi(r, add_dn(sqrt_dn(add_dn(ah, al)), s), add_up(sqrt_up(add_up(ah, al)), s));
  double s2 = s + c;
  return (i128_dd){ s2, add_up(sub_up(s, s2), c) };
}

static inline i128_dd dd_min_lo(i128_dd a, i128_dd b) {
  i128_dd u = dd_add_hi(a.hi, a.lo, -b.hi, -b.lo);
  if (dd_fin(u) && dd_nonpos(u.hi, u.lo)) return a;
  i128_dd w = dd_add_lo(a.hi, a.lo, -b.hi, -b.lo);
  if (dd_fin(w) && dd_pos(w.hi, w.lo)) return b;
  return dd_add_lo(a.hi, a.lo, -u.hi, -u.lo);
}

static inline i128_dd dd_max_hi(i128_dd a, i128_dd b) {
  i128_dd w = dd_add_lo(a.hi, a.lo, -b.hi, -b.lo);
  if (dd_fin(w) && dd_nonneg(w.hi, w.lo)) return a;
  i128_dd u = dd_add_hi(a.hi, a.lo, -b.hi, -b.lo);
  if (dd_fin(u) && dd_neg(u.hi, u.lo)) return b;
  return dd_add_hi(a.hi, a.lo, -w.hi, -w.lo);
}

/* ---------- Interval64 fallback (mirrors Interval64/Interval.lean) ---------- */

static inline i128_iv64 iv_nan(void) { return (i128_iv64){ NAN, NAN }; }
static inline i128_iv64 iv_whole(void) { return (i128_iv64){ -INFINITY, INFINITY }; }
static inline int iv_anynan(i128_iv64 a, i128_iv64 b) {
  return isnan(a.lo) || isnan(a.hi) || isnan(b.lo) || isnan(b.hi);
}
static inline i128_iv64 iv_hull(i128_t x) {
  return (i128_iv64){ add_dn(x.lh, x.ll), add_up(x.uh, x.ul) };
}
static inline i128_iv64 iv_add(i128_iv64 a, i128_iv64 b) {
  if (iv_anynan(a, b)) return iv_nan();
  return (i128_iv64){ add_dn(a.lo, b.lo), add_up(a.hi, b.hi) };
}
static inline i128_iv64 iv_sub(i128_iv64 a, i128_iv64 b) {
  if (iv_anynan(a, b)) return iv_nan();
  return (i128_iv64){ sub_dn(a.lo, b.hi), sub_up(a.hi, b.lo) };
}
static inline void iv_acc(double x, double y, double *lo, double *hi, int *got) {
  if ((x == 0 && isinf(y)) || (y == 0 && isinf(x))) return;
  double d = mul_dn(x, y), u = mul_up(x, y);
  if (isnan(d) || isnan(u)) return;
  if (!*got) { *lo = d; *hi = u; *got = 1; return; }
  *lo = (d < *lo) ? d : *lo;
  *hi = (u > *hi) ? u : *hi;
}
static inline i128_iv64 iv_mul(i128_iv64 a, i128_iv64 b) {
  if (iv_anynan(a, b)) return iv_nan();
  double lo = 0, hi = 0; int got = 0;
  iv_acc(a.lo, b.lo, &lo, &hi, &got);
  iv_acc(a.lo, b.hi, &lo, &hi, &got);
  iv_acc(a.hi, b.lo, &lo, &hi, &got);
  iv_acc(a.hi, b.hi, &lo, &hi, &got);
  if (!got) return iv_whole();
  return (i128_iv64){ lo, hi };
}
static inline double iv_fmin(double x, double y) { return (x < y) ? x : y; }
static inline double iv_fmax(double x, double y) { return (x > y) ? x : y; }
static inline double iv_fminN(double x, double y) { return isnan(x) ? y : isnan(y) ? x : iv_fmin(x, y); }
static inline double iv_fmaxN(double x, double y) { return isnan(x) ? y : isnan(y) ? x : iv_fmax(x, y); }
static inline i128_iv64 iv_div(i128_iv64 a, i128_iv64 b) {
  if (iv_anynan(a, b)) return iv_nan();
  if (b.lo <= 0 && 0 <= b.hi) return iv_whole();
  double d0 = div_dn(a.lo, b.lo), d1 = div_dn(a.lo, b.hi), d2 = div_dn(a.hi, b.lo), d3 = div_dn(a.hi, b.hi);
  double u0 = div_up(a.lo, b.lo), u1 = div_up(a.lo, b.hi), u2 = div_up(a.hi, b.lo), u3 = div_up(a.hi, b.hi);
  double lo = iv_fmin(d0, iv_fmin(d1, iv_fmin(d2, d3)));
  double hi = iv_fmax(u0, iv_fmax(u1, iv_fmax(u2, u3)));
  if (isnan(lo) || isnan(hi)) {
    lo = iv_fminN(d0, iv_fminN(d1, iv_fminN(d2, d3)));
    hi = iv_fmaxN(u0, iv_fmaxN(u1, iv_fmaxN(u2, u3)));
    if (isnan(lo) || isnan(hi)) return iv_whole();
  }
  return (i128_iv64){ lo, hi };
}
static inline i128_iv64 iv_sqrt(i128_iv64 a) {
  if (isnan(a.lo) || isnan(a.hi)) return iv_nan();
  if (a.hi < 0) return iv_nan();
  double l = (a.lo < 0) ? 0.0 : a.lo;
  return (i128_iv64){ sqrt_dn(l), sqrt_up(a.hi) };
}

/* ---------- Interval128 operations (Interval128/Interval.lean) ---------- */

static inline i128_t i128_of64(i128_iv64 j) { return (i128_t){ j.lo, 0.0, j.hi, 0.0 }; }
static inline int i128_isfin(i128_t x) {
  return isfinite(x.lh) && isfinite(x.ll) && isfinite(x.uh) && isfinite(x.ul);
}
static inline i128_t i128_neg(i128_t x) { return (i128_t){ -x.uh, -x.ul, -x.lh, -x.ll }; }

#define I128_PICK(L, U, SLOW) do { \
    int fl_ = dd_fin(L), fu_ = dd_fin(U); \
    if (fl_ && fu_) return (i128_t){ (L).hi, (L).lo, (U).hi, (U).lo }; \
    i128_iv64 j_ = (SLOW); \
    if (fl_) return (i128_t){ (L).hi, (L).lo, j_.hi, 0.0 }; \
    if (fu_) return (i128_t){ j_.lo, 0.0, (U).hi, (U).lo }; \
    return i128_of64(j_); } while (0)

static inline i128_t i128k_add(i128_t x, i128_t y) {
  i128_dd l = dd_add_lo(x.lh, x.ll, y.lh, y.ll);
  i128_dd u = dd_add_hi(x.uh, x.ul, y.uh, y.ul);
  I128_PICK(l, u, iv_add(iv_hull(x), iv_hull(y)));
}

static inline i128_t i128k_sub(i128_t x, i128_t y) {
  i128_dd l = dd_add_lo(x.lh, x.ll, -y.uh, -y.ul);
  i128_dd u = dd_add_hi(x.uh, x.ul, -y.lh, -y.ll);
  I128_PICK(l, u, iv_sub(iv_hull(x), iv_hull(y)));
}

static inline i128_dd i128_mul_lo_f(i128_t x, i128_t y) {
  if (dd_nonneg(y.lh, y.ll))
    return dd_nonneg(x.lh, x.ll) ? dd_mul_lo(x.lh, x.ll, y.lh, y.ll) : dd_mul_lo(x.lh, x.ll, y.uh, y.ul);
  if (dd_nonpos(y.uh, y.ul))
    return dd_nonpos(x.uh, x.ul) ? dd_mul_lo(x.uh, x.ul, y.uh, y.ul) : dd_mul_lo(x.uh, x.ul, y.lh, y.ll);
  if (dd_nonneg(x.lh, x.ll)) return dd_mul_lo(x.uh, x.ul, y.lh, y.ll);
  if (dd_nonpos(x.uh, x.ul)) return dd_mul_lo(x.lh, x.ll, y.uh, y.ul);
  return dd_min_lo(dd_mul_lo(x.lh, x.ll, y.uh, y.ul), dd_mul_lo(x.uh, x.ul, y.lh, y.ll));
}

static inline i128_dd i128_mul_hi_f(i128_t x, i128_t y) {
  if (dd_nonneg(y.lh, y.ll))
    return dd_nonneg(x.uh, x.ul) ? dd_mul_hi(x.uh, x.ul, y.uh, y.ul) : dd_mul_hi(x.uh, x.ul, y.lh, y.ll);
  if (dd_nonpos(y.uh, y.ul))
    return dd_nonneg(x.lh, x.ll) ? dd_mul_hi(x.lh, x.ll, y.uh, y.ul) : dd_mul_hi(x.lh, x.ll, y.lh, y.ll);
  if (dd_nonneg(x.lh, x.ll)) return dd_mul_hi(x.uh, x.ul, y.uh, y.ul);
  if (dd_nonpos(x.uh, x.ul)) return dd_mul_hi(x.lh, x.ll, y.lh, y.ll);
  return dd_max_hi(dd_mul_hi(x.lh, x.ll, y.lh, y.ll), dd_mul_hi(x.uh, x.ul, y.uh, y.ul));
}

static inline i128_t i128k_mul(i128_t x, i128_t y) {
  if (!(i128_isfin(x) && i128_isfin(y))) return i128_of64(iv_mul(iv_hull(x), iv_hull(y)));
  i128_dd l = i128_mul_lo_f(x, y);
  i128_dd u = i128_mul_hi_f(x, y);
  I128_PICK(l, u, iv_mul(iv_hull(x), iv_hull(y)));
}

static inline i128_t i128k_div_pos(i128_t x, i128_t y) {
  i128_dd l = dd_nonneg(x.lh, x.ll) ? dd_div_lo(x.lh, x.ll, y.uh, y.ul) : dd_div_lo(x.lh, x.ll, y.lh, y.ll);
  i128_dd u = dd_nonneg(x.uh, x.ul) ? dd_div_hi(x.uh, x.ul, y.lh, y.ll) : dd_div_hi(x.uh, x.ul, y.uh, y.ul);
  I128_PICK(l, u, iv_div(iv_hull(x), iv_hull(y)));
}

static inline i128_t i128k_div(i128_t x, i128_t y) {
  if (!(i128_isfin(x) && i128_isfin(y))) return i128_of64(iv_div(iv_hull(x), iv_hull(y)));
  if (dd_pos(y.lh, y.ll)) return i128k_div_pos(x, y);
  if (dd_neg(y.uh, y.ul)) return i128k_div_pos(i128_neg(x), i128_neg(y));
  return i128_of64(iv_whole());
}

static inline i128_t i128k_sqrt(i128_t x) {
  if (!i128_isfin(x)) return i128_of64(iv_sqrt(iv_hull(x)));
  if (dd_neg(x.uh, x.ul)) return i128_of64(iv_nan());
  i128_dd l = dd_nonneg(x.lh, x.ll) ? dd_sqrt_lo(x.lh, x.ll) : (i128_dd){ 0.0, 0.0 };
  i128_dd u = dd_sqrt_hi(x.uh, x.ul);
  I128_PICK(l, u, iv_sqrt(iv_hull(x)));
}

#endif /* INTERVAL128_H */
