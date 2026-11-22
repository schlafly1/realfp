/* Shared problem definition (host side, plain C). */
#ifndef BENCH_COMMON_H
#define BENCH_COMMON_H
#include <stdint.h>
/* Function fn: domain [-R,R]^2, claim direction and bound. */
static const double FN_R[2]     = {2.0, 4.0};
static const int    FN_UPPER[2] = {0, 1};            /* 0: claim lo >= bound; 1: hi <= bound */
static const double FN_BOUND[2] = {-0.015625, 0.99};
typedef struct { double minlo, maxhi; uint64_t fails; } red_t;
/* Grid with n = 2^k boxes per side; box (i,j), idx = j*n + i:
   x in [-R + i h, -R + (i+1) h], h = 2R / n (all endpoints exact). */
#endif
