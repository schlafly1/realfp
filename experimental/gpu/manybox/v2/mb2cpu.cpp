/* manybox v2 CPU engine: the same bisection as mb2gpu.cu, fp64 with realfp's portable
   directed-rounding kernels (RN + exact error term, ../../../../c/iv64_rnerr.h), OpenMP. */
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include "../../../../c/iv64_rnerr.h"
#include "mb2.hpp"

struct C64 {
  typedef double T;
  static inline double add_d(double a, double b) { return iv64r_add(a, b, 0); }
  static inline double add_u(double a, double b) { return iv64r_add(a, b, 1); }
  static inline double sub_d(double a, double b) { return iv64r_sub(a, b, 0); }
  static inline double sub_u(double a, double b) { return iv64r_sub(a, b, 1); }
  static inline double mul_d(double a, double b) { return iv64r_mul(a, b, 0); }
  static inline double mul_u(double a, double b) { return iv64r_mul(a, b, 1); }
  static inline double div_d(double a, double b) { return iv64r_div(a, b, 0); }
  static inline double div_u(double a, double b) { return iv64r_div(a, b, 1); }
  static inline double sqrt_d(double a) { return iv64r_sqrt(a, 0); }
  static inline double sqrt_u(double a) { return iv64r_sqrt(a, 1); }
  static inline bool nonfinite(double a) { return !isfinite(a); }
  static inline double inf() { return INFINITY; }
};

typedef std::vector<uint32_t> Col;
struct Lvl { Col c[MB2_MAXD]; };

struct CCtx { const mb2_opts *o; mb2_stats *st; std::vector<uint8_t> *flags; int d, upper, T; uint64_t cap; };

/* 0 leaf, 1 split, 2 refuted */
template <int PROB>
static inline uint8_t eval1(int level, const Lvl &A, size_t i, double bound, int upper) {
  constexpr int d = mb2_dim(PROB);
  IV<double> X[MB2_MAXD];
  for (int j = 0; j < d; j++) {
    double h = ldexp(2.0, -mb2_splits(d, level, j));
    double c = (double)A.c[j][i];
    X[j].lo = -1.0 + c * h; X[j].hi = -1.0 + (c + 1.0) * h;
  }
  IV<double> F = mb2_eval<C64>(PROB, X);
  if (upper) return F.lo > bound ? 2 : !(F.hi <= bound);
  return F.hi < bound ? 2 : !(F.lo >= bound);
}
template <int PROB>
static void eval_level(int level, const Lvl &A, size_t a, size_t b, uint8_t *fl, double bound, int upper) {
  for (size_t i = a; i < b; i++) fl[i] = eval1<PROB>(level, A, i, bound, upper);
}
static void eval_dispatch(int prob, int level, const Lvl &A, size_t a, size_t b, uint8_t *fl, double bound, int upper) {
#define L(P) case P: eval_level<P>(level, A, a, b, fl, bound, upper); break;
  switch (prob) { L(MB_P1) L(MB_P2) L(MB_NES) L(MB_PM) L(MB_C6) L(MB_M6) L(MB_R8) L(MB_C8) }
#undef L
}

static void bfs(CCtx &x, int level, Lvl &A, uint64_t n) {
  const mb2_opts &o = *x.o; mb2_stats &st = *x.st; int d = x.d, T = x.T;
  std::vector<uint8_t> fl; std::vector<size_t> cnt; Lvl B;
  for (; n > 0; level++) {
    if (level + 1 > st.levels) st.levels = level + 1;
    if (level >= o.maxlevel) { st.unresolved += n; return; }
    st.evals += n; if (n > st.peak) st.peak = n;
    fl.resize(n);
    size_t CH = n / (16 * (size_t)T); CH = CH < 64 ? 64 : (CH > 4096 ? 4096 : CH);
    size_t nch = (n + CH - 1) / CH;
    cnt.assign(nch + 1, 0);
#pragma omp parallel for schedule(dynamic, 1) num_threads(T)
    for (size_t q = 0; q < nch; q++) {
      size_t a = q * CH, b = a + CH < n ? a + CH : n, k = 0;
      eval_dispatch(o.prob, level, A, a, b, fl.data(), o.bound, x.upper);
      for (size_t i = a; i < b; i++) k += fl[i] != 0;
      cnt[q + 1] = k;
    }
    for (size_t i = 0; i < n; i++) if (fl[i] == 2) {
      if (st.refuted == 0) { st.ref_level = level; for (int j = 0; j < d; j++) st.ref_c[j] = A.c[j][i]; }
      st.refuted++;
    }
    if (x.flags) { size_t o0 = x.flags->size(); x.flags->resize(o0 + n); for (size_t i = 0; i < n; i++) (*x.flags)[o0 + i] = fl[i] != 0; }
    if (st.refuted) return;
    for (size_t q = 1; q <= nch; q++) cnt[q] += cnt[q - 1];
    uint64_t nf = cnt[nch];
    st.leaves += n - nf;
    if (nf == 0) return;
    int sd = level % d;
    if (2 * nf > x.cap && x.flags) { st.ok = -1; return; }
    if (2 * nf <= x.cap) {
      for (int j = 0; j < d; j++) B.c[j].resize(2 * nf);
#pragma omp parallel for schedule(dynamic, 1) num_threads(T)
      for (size_t q = 0; q < nch; q++) {
        size_t a = q * CH, b = a + CH < n ? a + CH : n, oo = 2 * cnt[q];
        for (size_t i = a; i < b; i++) if (fl[i]) {
          for (int j = 0; j < d; j++) {
            uint32_t c = A.c[j][i];
            if (j == sd) { B.c[j][oo] = 2 * c; B.c[j][oo + 1] = 2 * c + 1; } else { B.c[j][oo] = c; B.c[j][oo + 1] = c; }
          }
          oo += 2;
        }
      }
      for (int j = 0; j < d; j++) A.c[j].swap(B.c[j]);
      n = 2 * nf;
      continue;
    }
    /* depth first over chunks of the parents */
    Lvl P;
    for (int j = 0; j < d; j++) { P.c[j].reserve(nf); for (size_t i = 0; i < n; i++) if (fl[i]) P.c[j].push_back(A.c[j][i]); }
    uint64_t ch = x.cap / 2;
    for (uint64_t a = 0; a < nf; a += ch) {
      uint64_t m = nf - a < ch ? nf - a : ch;
      Lvl K;
      for (int j = 0; j < d; j++) {
        K.c[j].resize(2 * m);
        for (uint64_t k = 0; k < m; k++) {
          uint32_t c = P.c[j][a + k];
          if (j == sd) { K.c[j][2 * k] = 2 * c; K.c[j][2 * k + 1] = 2 * c + 1; } else { K.c[j][2 * k] = c; K.c[j][2 * k + 1] = c; }
        }
      }
      bfs(x, level + 1, K, 2 * m);
      if (st.refuted || st.ok < 0) break;
    }
    return;
  }
}

mb2_stats mb2_cpu(const mb2_opts &o, const mb2_forest &f, std::vector<uint8_t> *flags) {
  mb2_stats st; memset(&st, 0, sizeof st);
  int d = MB2_DIM[o.prob];
  CCtx x = {&o, &st, flags, d, MB2_UPPER[o.prob], o.nthreads > 0 ? o.nthreads : omp_get_max_threads(),
            o.cap ? o.cap : (1ull << 27)};
  Lvl A;
  for (int j = 0; j < d; j++) A.c[j] = f.c[j];
  bfs(x, f.level, A, f.n);
  if (st.ok == 0) st.ok = st.unresolved == 0 && st.refuted == 0;
  return st;
}
