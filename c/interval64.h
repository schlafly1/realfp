/* Interval64: binary64 directed-rounding kernels (AVX-512 + fesetround fallback).
   Not used from Lean's Float.add / Float.mul / etc. */
#ifndef INTERVAL64_H
#define INTERVAL64_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

uint8_t iv64_has_avx512f(void);

/* nextafter-style helpers (bit-identical IEEE nextUp / nextDown, independent of rounding mode). */
double iv64_next_up(double x);
double iv64_next_down(double x);

/* AVX-512 embedded rounding (does not change MXCSR). */
double iv64_avx_add_down(double a, double b);
double iv64_avx_add_up(double a, double b);
double iv64_avx_sub_down(double a, double b);
double iv64_avx_sub_up(double a, double b);
double iv64_avx_mul_down(double a, double b);
double iv64_avx_mul_up(double a, double b);
double iv64_avx_div_down(double a, double b);
double iv64_avx_div_up(double a, double b);
double iv64_avx_sqrt_down(double a);
double iv64_avx_sqrt_up(double a);

/* Per-operation fesetround / MXCSR save-restore. */
double iv64_fe_add_down(double a, double b);
double iv64_fe_add_up(double a, double b);
double iv64_fe_sub_down(double a, double b);
double iv64_fe_sub_up(double a, double b);
double iv64_fe_mul_down(double a, double b);
double iv64_fe_mul_up(double a, double b);
double iv64_fe_div_down(double a, double b);
double iv64_fe_div_up(double a, double b);
double iv64_fe_sqrt_down(double a);
double iv64_fe_sqrt_up(double a);

/* Independent software oracles: +,-,* via exact __float128 then directed conversion;
   / and sqrt via integer significand rounding. */
double iv64_soft_add_down(double a, double b);
double iv64_soft_add_up(double a, double b);
double iv64_soft_sub_down(double a, double b);
double iv64_soft_sub_up(double a, double b);
double iv64_soft_mul_down(double a, double b);
double iv64_soft_mul_up(double a, double b);
double iv64_soft_div_down(double a, double b);
double iv64_soft_div_up(double a, double b);
double iv64_soft_sqrt_down(double a);
double iv64_soft_sqrt_up(double a);

/* RN + one-ulp outward widening (sound if hardware RN matches IEEE, slightly looser). */
double iv64_widen_add_down(double a, double b);
double iv64_widen_add_up(double a, double b);
double iv64_widen_sub_down(double a, double b);
double iv64_widen_sub_up(double a, double b);
double iv64_widen_mul_down(double a, double b);
double iv64_widen_mul_up(double a, double b);
double iv64_widen_div_down(double a, double b);
double iv64_widen_div_up(double a, double b);
double iv64_widen_sqrt_down(double a);
double iv64_widen_sqrt_up(double a);

/* Interval endpoints written to *rlo / *rhi.
   Policy:
     - if any endpoint is NaN: result is [NaN, NaN] (invalid)
     - div: if 0 is in the denominator interval, result is [-Inf, +Inf] (whole)
     - sqrt: if hi < 0, result is [NaN, NaN] (empty/invalid);
             if lo < 0 <= hi, lower endpoint is +0 (or -0 if lo is -0 and hi == 0 is handled via sqrt).
*/
void iv64_avx_interval_add(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_avx_interval_sub(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_avx_interval_mul(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_avx_interval_div(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_avx_interval_sqrt(double lo, double hi, double *rlo, double *rhi);

void iv64_fe_interval_add(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_fe_interval_sub(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_fe_interval_mul(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_fe_interval_div(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_fe_interval_sqrt(double lo, double hi, double *rlo, double *rhi);

void iv64_widen_interval_add(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_widen_interval_sub(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_widen_interval_mul(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_widen_interval_div(double alo, double ahi, double blo, double bhi, double *rlo, double *rhi);
void iv64_widen_interval_sqrt(double lo, double hi, double *rlo, double *rhi);

/* Batched FE_UPWARD kernels: set FE_UPWARD once, use -(-x-y) for lower bounds, restore after.
   n is the number of interval operations. Arrays are not aliased. */
void iv64_fe_up_batch_add(const double *alo, const double *ahi,
                          const double *blo, const double *bhi,
                          double *rlo, double *rhi, uint64_t n);

/* COMPARE.md-style kernel over n pairs of 3-vectors: 3 interval muls + 2 adds, interval square, compare.
   Returns the number of times hi < 0 after the square (just a sink / comparison result). */
uint64_t iv64_bench_dot3_sq_cmp_avx(const double *a, const double *b, uint64_t n);
uint64_t iv64_bench_dot3_sq_cmp_fe(const double *a, const double *b, uint64_t n);
uint64_t iv64_bench_dot3_sq_cmp_widen(const double *a, const double *b, uint64_t n);
uint64_t iv64_bench_dot3_sq_cmp_fe_up_batch(const double *a, const double *b, uint64_t n);

/* Exhaustive-style differential test. Returns the number of mismatches.
   Prints a short report to *out_chars (NUL-terminated, cap out_cap). */
uint64_t iv64_run_selftest(char *out, uint64_t out_cap);
uint8_t iv64_has_avx512f_unit(void *u);
uint64_t iv64_selftest_report(void *u);
uint64_t iv64_run_benches(void *u);

#ifdef __cplusplus
}
#endif
#endif
