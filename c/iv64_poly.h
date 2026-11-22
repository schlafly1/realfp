/* Interval64 polynomial, Bernstein and quadrature kernels (header-only, static inline).

   Each routine is a transcription of the Lean specification it implements
   (Interval64/Poly.lean, Bernstein.lean, Quad.lean, Quad2.lean, Kernel/Quad.lean),
   performing the same `Interval64` operations (directed scalar kernels from
   interval128.h, the same NaN / 0*inf / empty-intersection policies) in the same order,
   so the results are bit-identical (checked by the differential tests in
   Interval64Test.lean). Coefficients past the end of an array are `[0, 0]` and are
   combined literally, exactly as in the spec. */
#ifndef IV64_POLY_H
#define IV64_POLY_H

#include "iv64_matrix.h"

typedef iv64m_t ivp_t;

static inline ivp_t ivp_mk(double lo, double hi) { return (ivp_t){ lo, hi }; }
static inline ivp_t ivp_zero(void) { return (ivp_t){ 0.0, 0.0 }; }
static inline ivp_t ivp_whole(void) { return (ivp_t){ -INFINITY, INFINITY }; }
static inline ivp_t ivp_point(double x) { return (ivp_t){ x, x }; }
static inline int ivp_isnan2(ivp_t a) { return isnan(a.lo) || isnan(a.hi); }
/* Interval64.fmin / fmax (`if x < y then x else y`, `if x > y then x else y`). */
static inline double ivp_fmin(double x, double y) { return x < y ? x : y; }
static inline double ivp_fmax(double x, double y) { return x > y ? x : y; }
/* Quad.finite */
static inline int ivp_finite(double x) { return !isnan(x) && !isinf(x); }

#define ivp_add ivm_add
#define ivp_sub ivm_sub
#define ivp_mul ivm_mul
#define ivp_abs ivm_abs

/* Interval64.neg (no NaN test) */
static inline ivp_t ivp_neg(ivp_t a) { return (ivp_t){ -a.hi, -a.lo }; }
/* Interval64.hull */
static inline ivp_t ivp_hull(ivp_t a, ivp_t b) {
  if (ivp_isnan2(a)) return b;
  if (ivp_isnan2(b)) return a;
  return (ivp_t){ ivp_fmin(a.lo, b.lo), ivp_fmax(a.hi, b.hi) };
}
/* Interval64.intersect */
static inline ivp_t ivp_intersect(ivp_t a, ivp_t b) {
  if (ivm_any_nan(a, b)) return ivm_invalid();
  double lo = ivp_fmax(a.lo, b.lo), hi = ivp_fmin(a.hi, b.hi);
  if (lo <= hi) return (ivp_t){ lo, hi };
  return ivm_invalid();
}
#define IVP_MAXFLOAT 1.7976931348623157e308
/* Interval64.mid */
static inline double ivp_mid(ivp_t a) {
  if (ivp_isnan2(a)) return NAN;
  volatile double l = 0.5 * ivp_fmax(a.lo, -IVP_MAXFLOAT);
  volatile double h = 0.5 * ivp_fmin(a.hi, IVP_MAXFLOAT);
  double raw = l + h;
  return ivp_fmin(ivp_fmax(raw, a.lo), a.hi);
}
/* Interval64.width */
static inline double ivp_width(ivp_t a) { return sub_up(a.hi, a.lo); }
/* Interval64.square */
static inline ivp_t ivp_square(ivp_t a) {
  if (ivp_isnan2(a)) return ivm_invalid();
  if (0.0 <= a.lo) return (ivp_t){ mul_dn(a.lo, a.lo), mul_up(a.hi, a.hi) };
  if (a.hi <= 0.0) return (ivp_t){ mul_dn(a.hi, a.hi), mul_up(a.lo, a.lo) };
  return (ivp_t){ 0.0, ivp_fmax(mul_up(a.lo, a.lo), mul_up(a.hi, a.hi)) };
}
/* Interval64.containsZero */
static inline int ivp_contains_zero(ivp_t a) { return !ivp_isnan2(a) && a.lo <= 0.0 && 0.0 <= a.hi; }
/* Interval64.inv */
static inline ivp_t ivp_inv(ivp_t a) {
  if (ivp_isnan2(a)) return ivm_invalid();
  if (ivp_contains_zero(a)) return ivp_whole();
  return (ivp_t){ div_dn(1.0, a.hi), div_up(1.0, a.lo) };
}
/* Interval64.sqrt */
static inline ivp_t ivp_sqrt(ivp_t a) {
  if (ivp_isnan2(a)) return ivm_invalid();
  if (a.hi < 0.0) return ivm_invalid();
  double l = a.lo < 0.0 ? 0.0 : a.lo;
  return (ivp_t){ sqrt_dn(l), sqrt_up(a.hi) };
}
/* KF.sqrtI */
static inline ivp_t ivp_sqrtI(ivp_t a) {
  if (a.lo < 0.0) return ivp_hull(ivp_zero(), ivp_sqrt(a));
  return ivp_sqrt(a);
}
/* Interval64.ipowAux 64 b e [1,1] */
static inline ivp_t ivp_ipow(ivp_t b, uint64_t e) {
  ivp_t acc = { 1.0, 1.0 };
  for (int fuel = 64; ; fuel--) {
    if (fuel == 0) return e == 0 ? acc : ivp_whole();
    if (e == 0) return acc;
    ivp_t nb = ivp_square(b);
    if (e % 2 == 1) acc = ivp_mul(acc, b);
    e /= 2; b = nb;
  }
}
static inline double ivp_powLo(double f, uint64_t n) { return isinf(f) ? f : ivp_ipow(ivp_point(f), n).lo; }
static inline double ivp_powHi(double f, uint64_t n) { return isinf(f) ? f : ivp_ipow(ivp_point(f), n).hi; }
/* Interval64.pown */
static inline ivp_t ivp_pown(ivp_t a, uint64_t n) {
  if (ivp_isnan2(a)) return ivm_invalid();
  if (n == 0) return (ivp_t){ 1.0, 1.0 };
  if (n % 2 == 1) return (ivp_t){ ivp_powLo(a.lo, n), ivp_powHi(a.hi, n) };
  ivp_t b = ivp_abs(a);
  return (ivp_t){ ivp_powLo(b.lo, n), ivp_powHi(b.hi, n) };
}

/* ---------- polynomials (dense arrays of intervals) ---------- */

static inline ivp_t ivp_coeff(const ivp_t *p, size_t n, size_t k) { return k < n ? p[k] : ivp_zero(); }

/* IPoly.eval = hornerAux P.coeff X 0 P.size */
static inline ivp_t ivp_eval(const ivp_t *p, size_t n, ivp_t x) {
  if (n == 0) return ivp_zero();
  ivp_t acc = p[n - 1];
  for (size_t k = n - 1; k-- > 0;) acc = ivp_add(p[k], ivp_mul(x, acc));
  return acc;
}

/* IPoly.evalMV */
static inline ivp_t ivp_eval_mv(const ivp_t *p, size_t n, const ivp_t *dp, size_t dn, ivp_t x) {
  double m = ivp_mid(x);
  ivp_t h = ivp_eval(p, n, x);
  if (isinf(m)) return h;
  ivp_t pm = ivp_point(m);
  return ivp_intersect(h, ivp_add(ivp_eval(p, n, pm), ivp_mul(ivp_eval(dp, dn, x), ivp_sub(x, pm))));
}

static inline void ivp_bisect(ivp_t x, ivp_t *l, ivp_t *r) {
  double m = ivp_mid(x);
  *l = (ivp_t){ x.lo, m };
  *r = (ivp_t){ m, x.hi };
}

/* IPoly.rangeAux */
static ivp_t ivp_range_aux(const ivp_t *p, size_t n, const ivp_t *dp, size_t dn, size_t fuel, ivp_t x) {
  if (fuel == 0) return ivp_eval_mv(p, n, dp, dn, x);
  ivp_t l, r; ivp_bisect(x, &l, &r);
  ivp_t a = ivp_range_aux(p, n, dp, dn, fuel - 1, l);
  ivp_t b = ivp_range_aux(p, n, dp, dn, fuel - 1, r);
  return ivp_hull(a, b);
}

/* The four goal predicates of checkGe / checkGt / checkLe / checkLt. */
static inline int ivp_goal(int mode, double c, ivp_t r) {
  switch (mode) {
    case 0: return c <= r.lo;
    case 1: return c < r.lo;
    case 2: return r.hi <= c;
    default: return r.hi < c;
  }
}

/* IPoly.checkAux */
static int ivp_check_aux(const ivp_t *p, size_t n, const ivp_t *dp, size_t dn, int mode, double c,
                         size_t fuel, ivp_t x) {
  if (ivp_goal(mode, c, ivp_eval_mv(p, n, dp, dn, x))) return 1;
  if (fuel == 0) return 0;
  ivp_t l, r; ivp_bisect(x, &l, &r);
  return ivp_check_aux(p, n, dp, dn, mode, c, fuel - 1, l) &&
         ivp_check_aux(p, n, dp, dn, mode, c, fuel - 1, r);
}

/* Bivariate: P[j] (size sz[j]) is the coefficient of y^j. */
typedef struct { const ivp_t *const *c; const size_t *sz; size_t n; } ivp2_t;

/* IPoly2.eval2 */
static inline ivp_t ivp_eval2(ivp2_t P, ivp_t x, ivp_t y) {
  if (P.n == 0) return ivp_zero();
  ivp_t acc = ivp_eval(P.c[P.n - 1], P.sz[P.n - 1], x);
  for (size_t j = P.n - 1; j-- > 0;) acc = ivp_add(ivp_eval(P.c[j], P.sz[j], x), ivp_mul(y, acc));
  return acc;
}

/* IPoly2.checkAux2 */
static int ivp_check_aux2(ivp2_t P, int mode, double c, size_t fuel, ivp_t x, ivp_t y) {
  if (ivp_goal(mode, c, ivp_eval2(P, x, y))) return 1;
  if (fuel == 0) return 0;
  ivp_t l, r;
  if (ivp_width(y) <= ivp_width(x)) {
    ivp_bisect(x, &l, &r);
    return ivp_check_aux2(P, mode, c, fuel - 1, l, y) && ivp_check_aux2(P, mode, c, fuel - 1, r, y);
  }
  ivp_bisect(y, &l, &r);
  return ivp_check_aux2(P, mode, c, fuel - 1, x, l) && ivp_check_aux2(P, mode, c, fuel - 1, x, r);
}

/* ---------- Bernstein ---------- */

#define IVP_BERN_MAX 56   /* C(N, i) < 2^53 for N <= 56, so ofRat (C(k,i)/C(N,i)) = [÷↓, ÷↑] */

/* Exact binomials C(k, i), 0 <= i <= k <= IVP_BERN_MAX, as doubles. */
static inline double ivp_choose(size_t k, size_t i) {
  if (i > k) return 0.0;
  uint64_t r = 1;
  for (size_t j = 0; j < i; j++) r = r * (k - j) / (j + 1);
  return (double)r;
}

/* IPoly.comp P #[A, B] (compAux: Horner over polynomials, literal `add` / `mul` / `idot`).
   out must have room for n entries; tmp for n entries. Returns the size (n). */
static size_t ivp_comp_lin(const ivp_t *p, size_t n, ivp_t A, ivp_t B, ivp_t *out, ivp_t *tmp) {
  if (n == 0) return 0;
  size_t rs = 1;
  out[0] = p[n - 1];
  ivp_t q[2] = { A, B };
  for (size_t off = n - 1; off-- > 0;) {
    /* M = mul Q R, size 2 + rs - 1 = rs + 1; coeff k = idot (Q.coeff i) (R.coeff (k - i)) (k + 1) */
    size_t ms = rs + 1;
    for (size_t k = 0; k < ms; k++) {
      ivp_t acc = ivp_zero();
      for (size_t i = 0; i <= k; i++)
        acc = ivp_add(acc, ivp_mul(ivp_coeff(q, 2, i), ivp_coeff(out, rs, k - i)));
      tmp[k] = acc;
    }
    /* add #[P_off] M, size max 1 ms = ms */
    for (size_t k = 0; k < ms; k++)
      out[k] = ivp_add(k == 0 ? p[off] : ivp_zero(), tmp[k]);
    rs = ms;
  }
  return rs;
}

/* IPoly.bernCoeffF c N k (c given as a dense array of size n, zero past the end). */
static inline ivp_t ivp_bern_coeff(const ivp_t *c, size_t n, size_t N, size_t k) {
  ivp_t acc = ivp_zero();
  for (size_t i = 0; i <= k; i++) {
    double a = ivp_choose(k, i), b = ivp_choose(N, i);
    ivp_t qi = { div_dn(a, b), div_up(a, b) };
    acc = ivp_add(acc, ivp_mul(qi, ivp_coeff(c, n, i)));
  }
  return acc;
}

/* IPoly.bern01 (caller guarantees bernDeg <= IVP_BERN_MAX) */
static inline ivp_t ivp_bern01(const ivp_t *p, size_t n, size_t deg) {
  size_t N = deg > (n ? n - 1 : 0) ? deg : (n ? n - 1 : 0);
  ivp_t h = ivp_bern_coeff(p, n, N, 0);
  for (size_t k = 1; k <= N; k++) h = ivp_hull(h, ivp_bern_coeff(p, n, N, k));
  return h;
}

/* IPoly.bernOn; buf needs 2 n entries. */
static inline ivp_t ivp_bern_on(const ivp_t *p, size_t n, ivp_t x, size_t deg, ivp_t *buf) {
  if (ivp_finite(x.lo) && ivp_finite(x.hi)) {
    size_t qn = ivp_comp_lin(p, n, ivp_point(x.lo), ivp_sub(ivp_point(x.hi), ivp_point(x.lo)), buf, buf + n);
    return ivp_bern01(buf, qn, deg);
  }
  return ivp_eval(p, n, x);
}

static ivp_t ivp_bern_range(const ivp_t *p, size_t n, size_t deg, size_t fuel, ivp_t x, ivp_t *buf) {
  if (fuel == 0) return ivp_bern_on(p, n, x, deg, buf);
  ivp_t l, r; ivp_bisect(x, &l, &r);
  ivp_t a = ivp_bern_range(p, n, deg, fuel - 1, l, buf);
  ivp_t b = ivp_bern_range(p, n, deg, fuel - 1, r, buf);
  return ivp_hull(a, b);
}

static int ivp_bern_check(const ivp_t *p, size_t n, size_t deg, int mode, double c, size_t fuel, ivp_t x,
                          ivp_t *buf) {
  if (ivp_goal(mode, c, ivp_bern_on(p, n, x, deg, buf))) return 1;
  if (fuel == 0) return 0;
  ivp_t l, r; ivp_bisect(x, &l, &r);
  return ivp_bern_check(p, n, deg, mode, c, fuel - 1, l, buf) &&
         ivp_bern_check(p, n, deg, mode, c, fuel - 1, r, buf);
}

/* IPoly2.bern2On. Work buffers: q (P.n * maxsz), tmp (2 * maxsz), col (P.n), buf1 (2 * P.n). */
typedef struct { ivp_t *q; ivp_t *tmp; ivp_t *col; ivp_t *buf1; size_t maxsz; } ivp2_work_t;

static inline ivp_t ivp_bern2_on(ivp2_t P, ivp_t x, ivp_t y, size_t n, size_t m, ivp2_work_t *w) {
  if (!(ivp_finite(x.lo) && ivp_finite(x.hi))) return ivp_eval2(P, x, y);
  ivp_t A = ivp_point(x.lo), B = ivp_sub(ivp_point(x.hi), ivp_point(x.lo));
  size_t maxs = 0;
  for (size_t j = 0; j < P.n; j++) {
    size_t s = ivp_comp_lin(P.c[j], P.sz[j], A, B, w->q + j * w->maxsz, w->tmp);
    if (s > maxs) maxs = s;
  }
  size_t N = n > (maxs ? maxs - 1 : 0) ? n : (maxs ? maxs - 1 : 0);
  ivp_t h = ivp_zero();
  for (size_t k = 0; k <= N; k++) {
    for (size_t j = 0; j < P.n; j++) w->col[j] = ivp_bern_coeff(w->q + j * w->maxsz, P.sz[j], N, k);
    ivp_t e = ivp_bern_on(w->col, P.n, y, m, w->buf1);
    h = k == 0 ? e : ivp_hull(h, e);
  }
  return h;
}

static int ivp_bern2_check(ivp2_t P, size_t n, size_t m, int mode, double c, size_t fuel, ivp_t x, ivp_t y,
                           ivp2_work_t *w) {
  if (ivp_goal(mode, c, ivp_bern2_on(P, x, y, n, m, w))) return 1;
  if (fuel == 0) return 0;
  ivp_t xl, xr, yl, yr; ivp_bisect(x, &xl, &xr); ivp_bisect(y, &yl, &yr);
  return ivp_bern2_check(P, n, m, mode, c, fuel - 1, xl, yl, w) &&
         ivp_bern2_check(P, n, m, mode, c, fuel - 1, xl, yr, w) &&
         ivp_bern2_check(P, n, m, mode, c, fuel - 1, xr, yl, w) &&
         ivp_bern2_check(P, n, m, mode, c, fuel - 1, xr, yr, w);
}

#endif
