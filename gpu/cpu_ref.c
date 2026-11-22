/* CPU reference for the GPU benchmark.
   _r : the repo's portable directed-rounding kernels (../c/iv64_rnerr.h: RN + exact
        error term, the Interval64 runtime backend on aarch64), 1 thread or OpenMP.
   _fe: an independent, slow reference that sets the rounding mode with fesetround
        around every single operation (fp64 and fp32), used on samples. */
#include <math.h>
#include <fenv.h>
#include <stdint.h>
#include <stddef.h>
#include <omp.h>
#include "../c/iv64_rnerr.h"
#include "bench_common.h"
#include "cpu_ref.h"

#pragma STDC FENV_ACCESS ON

/* ---- rnerr instantiation (fp64) ---- */
#define IVQ static inline
#define IVT double
#define IVN(n) n##_r
#define ADD_D(a, b) iv64r_add(a, b, 0)
#define ADD_U(a, b) iv64r_add(a, b, 1)
#define SUB_D(a, b) iv64r_sub(a, b, 0)
#define SUB_U(a, b) iv64r_sub(a, b, 1)
#define MUL_D(a, b) iv64r_mul(a, b, 0)
#define MUL_U(a, b) iv64r_mul(a, b, 1)
#define DIV_D(a, b) iv64r_div(a, b, 0)
#define DIV_U(a, b) iv64r_div(a, b, 1)
#define SQRT_D(a) iv64r_sqrt(a, 0)
#define SQRT_U(a) iv64r_sqrt(a, 1)
#include "ivexpr.h"
#undef IVT
#undef IVN
#undef ADD_D
#undef ADD_U
#undef SUB_D
#undef SUB_U
#undef MUL_D
#undef MUL_U
#undef DIV_D
#undef DIV_U
#undef SQRT_D
#undef SQRT_U

/* ---- fesetround instantiations (fp64 and fp32) ---- */
#define FE_OP(T, name, expr)                                                   \
  static T name(T a, T b, int mode) {                                          \
    int old = fegetround(); fesetround(mode);                                  \
    volatile T va = a, vb = b; volatile T r = expr; (void)vb;                  \
    fesetround(old); return r; }
FE_OP(double, fe_add, va + vb)
FE_OP(double, fe_sub, va - vb)
FE_OP(double, fe_mul, va * vb)
FE_OP(double, fe_div, va / vb)
FE_OP(double, fe_sqrt, sqrt(va))
FE_OP(float, fe_addf, va + vb)
FE_OP(float, fe_subf, va - vb)
FE_OP(float, fe_mulf, va * vb)
FE_OP(float, fe_divf, va / vb)
FE_OP(float, fe_sqrtf, sqrtf(va))

#define IVT double
#define IVN(n) n##_fe
#define ADD_D(a, b) fe_add(a, b, FE_DOWNWARD)
#define ADD_U(a, b) fe_add(a, b, FE_UPWARD)
#define SUB_D(a, b) fe_sub(a, b, FE_DOWNWARD)
#define SUB_U(a, b) fe_sub(a, b, FE_UPWARD)
#define MUL_D(a, b) fe_mul(a, b, FE_DOWNWARD)
#define MUL_U(a, b) fe_mul(a, b, FE_UPWARD)
#define DIV_D(a, b) fe_div(a, b, FE_DOWNWARD)
#define DIV_U(a, b) fe_div(a, b, FE_UPWARD)
#define SQRT_D(a) fe_sqrt(a, 0, FE_DOWNWARD)
#define SQRT_U(a) fe_sqrt(a, 0, FE_UPWARD)
#undef IV_MIN
#undef IV_MAX
#include "ivexpr.h"
#undef IVT
#undef IVN
#undef ADD_D
#undef ADD_U
#undef SUB_D
#undef SUB_U
#undef MUL_D
#undef MUL_U
#undef DIV_D
#undef DIV_U
#undef SQRT_D
#undef SQRT_U

#define IVT float
#define IVN(n) n##_fef
#define ADD_D(a, b) fe_addf(a, b, FE_DOWNWARD)
#define ADD_U(a, b) fe_addf(a, b, FE_UPWARD)
#define SUB_D(a, b) fe_subf(a, b, FE_DOWNWARD)
#define SUB_U(a, b) fe_subf(a, b, FE_UPWARD)
#define MUL_D(a, b) fe_mulf(a, b, FE_DOWNWARD)
#define MUL_U(a, b) fe_mulf(a, b, FE_UPWARD)
#define DIV_D(a, b) fe_divf(a, b, FE_DOWNWARD)
#define DIV_U(a, b) fe_divf(a, b, FE_UPWARD)
#define SQRT_D(a) fe_sqrtf(a, 0, FE_DOWNWARD)
#define SQRT_U(a) fe_sqrtf(a, 0, FE_UPWARD)
#undef IV_MIN
#undef IV_MAX
#include "ivexpr.h"

static inline int is_fail(int fn, double lo, double hi) {
  return FN_UPPER[fn] ? !(hi <= FN_BOUND[fn]) : !(lo >= FN_BOUND[fn]);
}

red_t cpu_grid(int fn, int k, int nthreads, double *lo_out, double *hi_out) {
  const uint64_t n = 1ull << k;
  const double R = FN_R[fn], h = 2 * R / (double)n;
  int nt = nthreads > 0 ? nthreads : omp_get_max_threads();
  red_t parts[256];
  if (nt > 256) nt = 256;
#pragma omp parallel num_threads(nt)
  {
    red_t r = {INFINITY, -INFINITY, 0};
#pragma omp for schedule(static)
    for (int64_t j = 0; j < (int64_t)n; j++) {
      iv_r Y = {-R + (double)j * h, -R + (double)(j + 1) * h};
      for (uint64_t i = 0; i < n; i++) {
        iv_r X = {-R + (double)i * h, -R + (double)(i + 1) * h};
        iv_r F = iv_eval_r(fn, X, Y);
        r.minlo = IV_MIN(r.minlo, F.lo);
        r.maxhi = IV_MAX(r.maxhi, F.hi);
        r.fails += is_fail(fn, F.lo, F.hi);
        if (lo_out) { lo_out[j * n + i] = F.lo; hi_out[j * n + i] = F.hi; }
      }
    }
    parts[omp_get_thread_num()] = r;
  }
  red_t r = {INFINITY, -INFINITY, 0};
  for (int t = 0; t < nt; t++) {
    r.minlo = IV_MIN(r.minlo, parts[t].minlo);
    r.maxhi = IV_MAX(r.maxhi, parts[t].maxhi);
    r.fails += parts[t].fails;
  }
  return r;
}

void cpu_list(int fn, const double *boxes, size_t N, double *out, int nthreads) {
  int nt = nthreads > 0 ? nthreads : omp_get_max_threads();
#pragma omp parallel for num_threads(nt) schedule(static) if (nt > 1)
  for (int64_t b = 0; b < (int64_t)N; b++) {
    iv_r X = {boxes[4 * b], boxes[4 * b + 1]}, Y = {boxes[4 * b + 2], boxes[4 * b + 3]};
    iv_r F = iv_eval_r(fn, X, Y);
    out[2 * b] = F.lo; out[2 * b + 1] = F.hi;
  }
}

void cpu_box_fe(int fn, const double *box, double *out) {
  iv_fe X = {box[0], box[1]}, Y = {box[2], box[3]};
  iv_fe F = iv_eval_fe(fn, X, Y);
  out[0] = F.lo; out[1] = F.hi;
}
void cpu_box_fef(int fn, const float *box, float *out) {
  iv_fef X = {box[0], box[1]}, Y = {box[2], box[3]};
  iv_fef F = iv_eval_fef(fn, X, Y);
  out[0] = F.lo; out[1] = F.hi;
}
