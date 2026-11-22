/* Interval64 matrix kernels (header-only, static inline).

   Bit-identical to the Lean specifications in Interval64/Matrix.lean
   (`Interval64.Mat.pdMarginsSpec`): the same `Interval64` operations
   (`add`, `sub`, `mul`, `abs`, with the same NaN / 0*inf policies) in the same order.
   Directed scalar ops come from interval128.h (AVX-512 embedded rounding, or
   RN + exact error term on aarch64), i.e. the same kernels as `iv64_dir_*`. */
#ifndef IV64_MATRIX_H
#define IV64_MATRIX_H

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include "interval128.h"

typedef struct { double lo, hi; } iv64m_t;

static inline iv64m_t ivm_invalid(void) { return (iv64m_t){ NAN, NAN }; }
static inline int ivm_any_nan(iv64m_t a, iv64m_t b) {
  return isnan(a.lo) || isnan(a.hi) || isnan(b.lo) || isnan(b.hi);
}
/* Interval64.add */
static inline iv64m_t ivm_add(iv64m_t a, iv64m_t b) {
  if (ivm_any_nan(a, b)) return ivm_invalid();
  return (iv64m_t){ add_dn(a.lo, b.lo), add_up(a.hi, b.hi) };
}
/* Interval64.sub */
static inline iv64m_t ivm_sub(iv64m_t a, iv64m_t b) {
  if (ivm_any_nan(a, b)) return ivm_invalid();
  return (iv64m_t){ sub_dn(a.lo, b.hi), sub_up(a.hi, b.lo) };
}
/* Interval64.accCorner */
static inline void ivm_corner(double x, double y, double *lo, double *hi, int *got) {
  if ((x == 0.0 && isinf(y)) || (y == 0.0 && isinf(x))) return;
  double d = mul_dn(x, y), u = mul_up(x, y);
  if (isnan(d) || isnan(u)) return;
  if (!*got) { *lo = d; *hi = u; *got = 1; }
  else { if (d < *lo) *lo = d; if (u > *hi) *hi = u; }
}
/* Interval64.mul (four corners in the spec's order). */
static inline iv64m_t ivm_mul(iv64m_t a, iv64m_t b) {
  if (ivm_any_nan(a, b)) return ivm_invalid();
  double lo = 0.0, hi = 0.0; int got = 0;
  ivm_corner(a.lo, b.lo, &lo, &hi, &got);
  ivm_corner(a.lo, b.hi, &lo, &hi, &got);
  ivm_corner(a.hi, b.lo, &lo, &hi, &got);
  ivm_corner(a.hi, b.hi, &lo, &hi, &got);
  if (!got) return (iv64m_t){ -INFINITY, INFINITY };
  return (iv64m_t){ lo, hi };
}
/* Interval64.mul ⟨x, x⟩ b. Corners 3, 4 repeat corners 1, 2 and cannot change the
   result (a repeated corner is never strictly below lo / above hi), so this is
   bit-identical to ivm_mul((iv64m_t){x, x}, b). */
static inline iv64m_t ivm_pmul(double x, iv64m_t b) {
  if (isnan(x) || isnan(b.lo) || isnan(b.hi)) return ivm_invalid();
  double lo = 0.0, hi = 0.0; int got = 0;
  ivm_corner(x, b.lo, &lo, &hi, &got);
  ivm_corner(x, b.hi, &lo, &hi, &got);
  if (!got) return (iv64m_t){ -INFINITY, INFINITY };
  return (iv64m_t){ lo, hi };
}
/* Interval64.mul a ⟨x, x⟩ (corners 2, 4 repeat 1, 3). */
static inline iv64m_t ivm_mulp(iv64m_t a, double x) {
  if (isnan(a.lo) || isnan(a.hi) || isnan(x)) return ivm_invalid();
  double lo = 0.0, hi = 0.0; int got = 0;
  ivm_corner(a.lo, x, &lo, &hi, &got);
  ivm_corner(a.hi, x, &lo, &hi, &got);
  if (!got) return (iv64m_t){ -INFINITY, INFINITY };
  return (iv64m_t){ lo, hi };
}
static inline double ivm_fmax(double x, double y) { return x > y ? x : y; }
/* Interval64.abs */
static inline iv64m_t ivm_abs(iv64m_t a) {
  if (isnan(a.lo) || isnan(a.hi)) return ivm_invalid();
  if (0.0 <= a.lo) return a;
  if (a.hi <= 0.0) return (iv64m_t){ -a.hi, -a.lo };
  return (iv64m_t){ 0.0, ivm_fmax(-a.lo, a.hi) };
}

/* pdMarginsSpec on dense row-major n×n arrays alo, ahi, x (already padded with 0).
   out has 2n entries. Returns 0 on success, -1 on allocation failure. */
static inline int iv64m_pd_margins(size_t n, const double *alo, const double *ahi,
                                   const double *x, double *out) {
  iv64m_t *T = (iv64m_t *)malloc(sizeof(iv64m_t) * (n * n ? n * n : 1));
  iv64m_t *B = (iv64m_t *)malloc(sizeof(iv64m_t) * (n * n ? n * n : 1));
  if (!T || !B) { free(T); free(B); return -1; }
  /* T i k = Σ_{j ≤ i} X i j * A j k */
  for (size_t i = 0; i < n; i++) {
    for (size_t k = 0; k < n; k++) {
      iv64m_t acc = { 0.0, 0.0 };
      for (size_t j = 0; j <= i; j++) {
        iv64m_t a = { alo[j * n + k], ahi[j * n + k] };
        acc = ivm_add(acc, ivm_pmul(x[i * n + j], a));
      }
      T[i * n + k] = acc;
    }
  }
  /* B i l = Σ_{k ≤ l} T i k * X l k, l ≤ i */
  for (size_t i = 0; i < n; i++) {
    for (size_t l = 0; l <= i; l++) {
      iv64m_t acc = { 0.0, 0.0 };
      for (size_t k = 0; k <= l; k++)
        acc = ivm_add(acc, ivm_mulp(T[i * n + k], x[l * n + k]));
      B[i * n + l] = acc;
    }
  }
  for (size_t i = 0; i < n; i++) {
    iv64m_t s = { 0.0, 0.0 };
    for (size_t l = 0; l < n; l++) {
      if (l == i) continue;
      iv64m_t b = l <= i ? B[i * n + l] : B[l * n + i];
      s = ivm_add(s, ivm_abs(b));
    }
    iv64m_t r = ivm_sub(B[i * n + i], s);
    out[2 * i] = r.lo;
    out[2 * i + 1] = r.hi;
  }
  free(T); free(B);
  return 0;
}

#endif
