#ifndef IVGPU_H
#define IVGPU_H
#include <stdint.h>
#include <stddef.h>
#include "bench_common.h"
#ifdef __cplusplus
extern "C" {
#endif
int ivgpu_init(void);
int ivgpu_info(char *name, int len, int *sms, int *cc_major, int *cc_minor);
int ivgpu_grid(int fn, int k, int prec, red_t *r, float *kernel_ms);
int ivgpu_grid_store(int fn, int k, int prec, void *lo, void *hi, red_t *r);
int ivgpu_list(int fn, const double *boxes, uint64_t N, double *out, float *kernel_ms);
void *ivgpu_host_alloc(size_t bytes);
void ivgpu_host_free(void *p);
#ifdef __cplusplus
}
#endif
#endif
