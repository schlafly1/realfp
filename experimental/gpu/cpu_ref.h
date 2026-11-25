#ifndef CPU_REF_H
#define CPU_REF_H
#include <stddef.h>
#include "bench_common.h"
#ifdef __cplusplus
extern "C" {
#endif
red_t cpu_grid(int fn, int k, int nthreads, double *lo_out, double *hi_out);
void cpu_list(int fn, const double *boxes, size_t N, double *out, int nthreads);
void cpu_box_fe(int fn, const double *box, double *out);
void cpu_box_fef(int fn, const float *box, float *out);
#ifdef __cplusplus
}
#endif
#endif
