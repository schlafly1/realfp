/* manybox CPU backend: realfp's portable directed-rounding kernels (RN + exact error term,
   ../../../c/iv64_rnerr.h; the Interval64 runtime backend on aarch64), 1 thread or OpenMP. */
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include "../../../c/iv64_rnerr.h"
#include "mb.h"

#define IVQ static inline
#define ADD_D(a, b) iv64r_add(a, b, 0)
#define ADD_U(a, b) iv64r_add(a, b, 1)
#define SUB_D(a, b) iv64r_sub(a, b, 0)
#define SUB_U(a, b) iv64r_sub(a, b, 1)
#define MUL_D(a, b) iv64r_mul(a, b, 0)
#define MUL_U(a, b) iv64r_mul(a, b, 1)
#include "mbexpr.h"

/* 1 = claim not proved on this box (split it). */
static inline uint32_t mb_fails(int prob, double bound, int level, const uint32_t *const *C, size_t i) {
  int d = MB_DIM[prob];
  mbiv X[MB_MAXD];
  for (int j = 0; j < d; j++) {
    double h = ldexp(2.0, -mb_splits(d, level, j));
    double c = (double)C[j][i];
    X[j].lo = -1.0 + c * h; X[j].hi = -1.0 + (c + 1.0) * h;
  }
  if (prob == 0) { mbiv F = mb_p1(X); return !(F.hi <= bound); }
  mbiv F = mb_p2(X); return !(F.lo >= bound);
}

static void grow(uint32_t **P, int d, size_t *cap, size_t need) {
  if (need <= *cap) return;
  size_t nc = *cap ? *cap : 1024; while (nc < need) nc *= 2;
  for (int j = 0; j < d; j++) P[j] = realloc(P[j], nc * 4);
  *cap = nc;
}

mb_stats mb_cpu_run(int prob, double bound, int maxlevel, int nthreads, mb_cert *cert) {
  int d = MB_DIM[prob], T = nthreads;
  mb_stats st = {0, 0, 0, 0, 0, 0, MB_FNV0};
  /* buffers persist across calls (as the GPU's do), so repeated runs do not pay page faults */
  static uint32_t *A[MB_MAXD], *B[MB_MAXD];
  static size_t capA, capB, capF, cntcap;
  static uint8_t *fl;
  static size_t *cnt;
  size_t n = 1;
  if (capA < capB) { for (int j = 0; j < MB_MAXD; j++) { uint32_t *t = A[j]; A[j] = B[j]; B[j] = t; } size_t t = capA; capA = capB; capB = t; }
  grow(A, MB_MAXD, &capA, 1);
  for (int j = 0; j < d; j++) A[j][0] = 0;
  if (!fl) { capF = 1024; fl = malloc(capF); }
  for (int level = 0; n > 0; level++) {
    st.levels = level + 1; st.evals += n; if (n > st.peak) st.peak = n;
    if (n > capF) { while (capF < n) capF *= 2; fl = realloc(fl, capF); }
    int sd = level % d, last = level + 1 >= maxlevel;
    /* chunks of n/(16 T) boxes (64..4096), scheduled dynamically: levels are small and the
       GB10 CPU mixes fast and slow cores */
    size_t CH = n / (16 * (size_t)T);
    CH = CH < 64 ? 64 : (CH > 4096 ? 4096 : CH);
    size_t nch = (n + CH - 1) / CH;
    if (nch + 1 > cntcap) { cntcap = 2 * (nch + 1); cnt = realloc(cnt, cntcap * sizeof *cnt); }
#pragma omp parallel for schedule(dynamic, 1) num_threads(T)
    for (size_t q = 0; q < nch; q++) {
      size_t a = q * CH, b = a + CH < n ? a + CH : n, k = 0;
      for (size_t i = a; i < b; i++) {
        uint8_t f = (uint8_t)mb_fails(prob, bound, level, (const uint32_t *const *)A, i);
        fl[i] = f; k += f;
      }
      cnt[q + 1] = k;
    }
    cnt[0] = 0;
    for (size_t q = 1; q <= nch; q++) cnt[q] += cnt[q - 1];
    size_t nf = cnt[nch];
    if (!last && nf) {
      grow(B, MB_MAXD, &capB, 2 * nf);
#pragma omp parallel for schedule(dynamic, 1) num_threads(T)
      for (size_t q = 0; q < nch; q++) {
        size_t a = q * CH, b = a + CH < n ? a + CH : n, o = 2 * cnt[q];
        for (size_t i = a; i < b; i++) if (fl[i]) {
          for (int j = 0; j < d; j++) {
            uint32_t c = A[j][i];
            if (j == sd) { B[j][o] = 2 * c; B[j][o + 1] = 2 * c + 1; }
            else { B[j][o] = c; B[j][o + 1] = c; }
          }
          o += 2;
        }
      }
    }
    if (cert) {
      if (cert->len + n > cert->cap) {
        while (cert->len + n > cert->cap) cert->cap = cert->cap ? 2 * cert->cap : 1 << 20;
        cert->flags = realloc(cert->flags, cert->cap);
      }
      memcpy(cert->flags + cert->len, fl, n); cert->len += n;
      st.hash = mb_fnv(st.hash, fl, n);
    }
    st.leaves += n - nf;
    if (nf == 0) { st.ok = 1; break; }
    if (last) { st.unresolved = nf; break; }
    for (int j = 0; j < MB_MAXD; j++) { uint32_t *t = A[j]; A[j] = B[j]; B[j] = t; }
    size_t tc = capA; capA = capB; capB = tc;
    n = 2 * nf;
  }
  return st;
}
