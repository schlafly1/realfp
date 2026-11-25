/* Interval128 vs Interval64 vs Arb (FLINT) throughput benchmark, C level.
   Build: see bench/i128/run.sh.  Reports ns per interval operation. */
#include "interval128.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#ifdef WITH_ARB
#include <flint/arb.h>
#endif

#define N 4096
#define REPS 400

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ull;
static double rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (double)(rs >> 11) / 9007199254740992.0; }

static i128_t X[N], Y[N], Z[N];
static i128_iv64 A[N], B[N], C[N];
static volatile double sink;

#define BENCH(name, body) do { \
    double t0 = now(); \
    for (int r = 0; r < REPS; r++) for (int i = 0; i < N; i++) { body; } \
    double t = (now() - t0) / ((double)REPS * N) * 1e9; \
    printf("%-22s %8.2f ns/op\n", name, t); } while (0)

int main(void) {
  for (int i = 0; i < N; i++) {
    double a = 1.0 + 3.0 * rnd(), b = 1.0 + 3.0 * rnd();
    if (rnd() < 0.5) a = -a;                       /* mixed signs for X, Y > 0 for div/sqrt */
    double w = ldexp(rnd(), -60);
    X[i] = (i128_t){ a, -ldexp(rnd(), -60), a + w, ldexp(rnd(), -60) };
    Y[i] = (i128_t){ b, -ldexp(rnd(), -60), b + w, ldexp(rnd(), -60) };
    A[i] = iv_hull(X[i]); B[i] = iv_hull(Y[i]);
  }
  printf("backend: %s\n", I128_AVX512 ? "AVX-512" : "rn+err");
  BENCH("Interval64  add", C[i] = iv_add(A[i], B[i]));
  BENCH("Interval64  mul", C[i] = iv_mul(A[i], B[i]));
  BENCH("Interval64  div", C[i] = iv_div(A[i], B[i]));
  BENCH("Interval64  sqrt", C[i] = iv_sqrt(B[i]));
  sink = C[N / 2].lo;
  BENCH("Interval128 add", Z[i] = i128k_add(X[i], Y[i]));
  BENCH("Interval128 mul", Z[i] = i128k_mul(X[i], Y[i]));
  BENCH("Interval128 div", Z[i] = i128k_div(X[i], Y[i]));
  BENCH("Interval128 sqrt", Z[i] = i128k_sqrt(Y[i]));
  sink = Z[N / 2].lh;
#ifdef WITH_ARB
  static arb_t ax[N], ay[N], az[N];
  for (int i = 0; i < N; i++) {
    arb_init(ax[i]); arb_init(ay[i]); arb_init(az[i]);
    arf_t lo, hi, t; arf_init(lo); arf_init(hi); arf_init(t);
    arf_set_d(lo, X[i].lh); arf_set_d(t, X[i].ll); arf_add(lo, lo, t, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_set_d(hi, X[i].uh); arf_set_d(t, X[i].ul); arf_add(hi, hi, t, ARF_PREC_EXACT, ARF_RND_UP);
    arb_set_interval_arf(ax[i], lo, hi, 128);
    arf_set_d(lo, Y[i].lh); arf_set_d(t, Y[i].ll); arf_add(lo, lo, t, ARF_PREC_EXACT, ARF_RND_DOWN);
    arf_set_d(hi, Y[i].uh); arf_set_d(t, Y[i].ul); arf_add(hi, hi, t, ARF_PREC_EXACT, ARF_RND_UP);
    arb_set_interval_arf(ay[i], lo, hi, 128);
    arf_clear(lo); arf_clear(hi); arf_clear(t);
  }
  int precs[2] = { 106, 128 };
  for (int k = 0; k < 2; k++) {
    slong p = precs[k]; char nm[64];
    snprintf(nm, sizeof nm, "Arb(p=%ld)  add", (long)p);  BENCH(nm, arb_add(az[i], ax[i], ay[i], p));
    snprintf(nm, sizeof nm, "Arb(p=%ld)  mul", (long)p);  BENCH(nm, arb_mul(az[i], ax[i], ay[i], p));
    snprintf(nm, sizeof nm, "Arb(p=%ld)  div", (long)p);  BENCH(nm, arb_div(az[i], ax[i], ay[i], p));
    snprintf(nm, sizeof nm, "Arb(p=%ld)  sqrt", (long)p); BENCH(nm, arb_sqrt(az[i], ay[i], p));
  }
  sink = arf_get_d(arb_midref(az[N / 2]), ARF_RND_NEAR);
#endif
  return 0;
}
