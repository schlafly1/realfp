/* manybox v2 engine interface (GPU: mb2gpu.cu, CPU: mb2cpu.cpp). */
#ifndef MB2_HPP
#define MB2_HPP
#include <stdint.h>
#include <stddef.h>
#include <vector>
#include "mb2.h"

struct mb2_opts {
  int prob;
  int prec;          /* 64 or 32 (32: GPU only) */
  double bound;      /* claim f <= bound (upper) or f >= bound */
  int maxlevel;      /* boxes at level >= maxlevel are not evaluated (reported unresolved) */
  uint64_t cap;      /* max boxes per level kept in memory (stats mode recurses beyond) */
  int nthreads;      /* CPU */
};

struct mb2_stats {
  int ok;              /* 1: every box resolved and none refuted */
  int levels;          /* deepest level evaluated + 1 */
  uint64_t evals, leaves, unresolved, refuted, peak;
  int ref_level;       /* first refuted box found (if refuted > 0): level and coordinates */
  uint32_t ref_c[MB2_MAXD];
};

/* A forest: n roots, all at `level`, coordinates c[j][i]. */
struct mb2_forest { int level; uint64_t n; std::vector<uint32_t> c[MB2_MAXD]; };

/* Level-order split flags (1 split, 0 leaf) of the forest, if requested (no recursion then:
   returns ok = -1 if a level exceeds cap). */
mb2_stats mb2_gpu(const mb2_opts &o, const mb2_forest &f, std::vector<uint8_t> *flags);
mb2_stats mb2_cpu(const mb2_opts &o, const mb2_forest &f, std::vector<uint8_t> *flags);
int mb2_gpu_init(char *name, int len);
static inline int mb2_splits(int d, int level, int j) { return (level + d - 1 - j) / d; }
#endif
