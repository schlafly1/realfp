/* manybox: level-synchronous bisection on [-1,1]^d, same subdivision on every backend.
   Level l: every active box is evaluated; a box whose enclosure proves the claim is a leaf,
   any other box is bisected at its midpoint in dimension (l mod d). Box coordinates are
   integers c_j, with c_j in [0, 2^{s_j}), s_j = #splits of dimension j so far, and
   x_j in [-1 + c_j h_j, -1 + (c_j + 1) h_j], h_j = 2^{1 - s_j} (all endpoints exact). */
#ifndef MB_H
#define MB_H
#include <stdint.h>
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif
#define MB_MAXD 4
/* prob 0: P1 = T8(x) + T8(y) <= 2 + delta (2-D); prob 1: P2 = Choi-Lam >= -delta (4-D). */
static const int MB_DIM[2] = {2, 4};
static inline int mb_dim(int prob) { return MB_DIM[prob]; }
static inline int mb_splits(int d, int level, int j) { return (level + d - 1 - j) / d; }

typedef struct {
  int ok;              /* 1: every box resolved (claim proved), 0: hit max depth */
  int levels;          /* number of levels evaluated */
  uint64_t evals;      /* boxes evaluated (= nodes of the bisection tree) */
  uint64_t leaves;     /* boxes that proved the claim */
  uint64_t unresolved; /* boxes still failing at max depth */
  uint64_t peak;       /* largest level */
  uint64_t hash;       /* FNV-1a over the per-box split flags, level by level (if computed) */
} mb_stats;

/* Optional certificate output: one byte per evaluated box (1 = split, 0 = leaf),
   level by level, boxes in level order. */
typedef struct { uint8_t *flags; uint64_t cap, len; } mb_cert;

static inline uint64_t mb_fnv(uint64_t h, const uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ull; }
  return h;
}
#define MB_FNV0 1469598103934665603ull

mb_stats mb_cpu_run(int prob, double bound, int maxlevel, int nthreads, mb_cert *cert);
int mb_gpu_init(char *name, int len);
mb_stats mb_gpu_run(int prob, double bound, int maxlevel, mb_cert *cert);
#ifdef __cplusplus
}
#endif
#endif
