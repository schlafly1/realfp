/* Interval64 GPU vs CPU benchmark driver (see README.md). */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <omp.h>
#include "bench_common.h"
#include "cpu_ref.h"
#include "ivgpu.h"

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int cmpd(const void *a, const void *b) { double x = *(double *)a, y = *(double *)b; return (x > y) - (x < y); }
static uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static uint32_t bitsf(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }
static uint64_t rs = 0x9e3779b97f4a7c15ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * 0x1p-53; }
static int same_red(red_t a, red_t b) { return bits(a.minlo) == bits(b.minlo) && bits(a.maxhi) == bits(b.maxhi) && a.fails == b.fails; }

#define MAXREP 200
/* median wall seconds of a closure-like call, at most MAXREP reps or ~tbudget s */
#define TIME_MEDIAN(out, tbudget, stmt) do { double ts_[MAXREP]; int n_ = 0; double st_ = now(); \
  stmt; /* warm-up */ \
  do { double a_ = now(); stmt; ts_[n_++] = now() - a_; } while (n_ < MAXREP && (now() - st_ < (tbudget) || n_ < 3)); \
  qsort(ts_, n_, sizeof(double), cmpd); out = ts_[n_ / 2]; } while (0)

static void random_boxes(int fn, double *bx, size_t N) {
  double R = FN_R[fn];
  for (size_t b = 0; b < N; b++)
    for (int d = 0; d < 2; d++) {
      double c = (2 * urand() - 1) * R, w = R * ldexp(urand(), -(int)(rnd() % 40));
      bx[4 * b + 2 * d] = c - w; bx[4 * b + 2 * d + 1] = c + w;   /* rounding irrelevant: any box */
    }
}

int main(int argc, char **argv) {
  int quick = argc > 1 && !strcmp(argv[1], "quick");
  int kmax = quick ? 11 : 13;
  int ncpu = omp_get_max_threads();
  char gname[256]; int sms, ccM, ccm;
  if (ivgpu_init() || ivgpu_info(gname, sizeof gname, &sms, &ccM, &ccm)) { fprintf(stderr, "no GPU\n"); return 1; }
  printf("GPU: %s, %d SMs, compute capability %d.%d; CPU threads (OpenMP): %d\n\n", gname, sms, ccM, ccm, ncpu);
  int bad = 0;

  /* ---------------- correctness ---------------- */
  printf("## Correctness\n\n");
  for (int fn = 0; fn < 2; fn++) {
    int k = quick ? 10 : 12; size_t N = 1ull << (2 * k);
    double *glo = malloc(N * 8), *ghi = malloc(N * 8), *clo = malloc(N * 8), *chi = malloc(N * 8);
    red_t rg, rc;
    if (ivgpu_grid_store(fn, k, 64, glo, ghi, &rg)) return 1;
    rc = cpu_grid(fn, k, 0, clo, chi);
    size_t mism = 0;
    for (size_t b = 0; b < N; b++) mism += bits(glo[b]) != bits(clo[b]) || bits(ghi[b]) != bits(chi[b]);
    /* independent fesetround reference on a sample */
    size_t S = 1u << 18, mfe = 0; double R = FN_R[fn], h = 2 * R / (double)(1u << k);
    for (size_t s = 0; s < S; s++) {
      size_t b = rnd() % N, i = b & ((1u << k) - 1), j = b >> k; double box[4] = {-R + i * h, -R + (i + 1) * h, -R + j * h, -R + (j + 1) * h}, o[2];
      cpu_box_fe(fn, box, o); mfe += bits(o[0]) != bits(glo[b]) || bits(o[1]) != bits(ghi[b]);
    }
    printf("f%d grid 2^%d boxes, fp64: GPU vs CPU(rnerr) endpoint mismatches %zu / %zu; reduced result %s; "
           "GPU vs fesetround reference on %zu sampled boxes: %zu mismatches\n",
           fn, 2 * k, mism, N, same_red(rg, rc) ? "identical" : "DIFFERENT", S, mfe);
    bad |= mism || mfe || !same_red(rg, rc);
    /* random arbitrary boxes (all scales, zero-crossing, unaligned endpoints) */
    size_t M = quick ? 1u << 18 : 1u << 22;
    double *bx = ivgpu_host_alloc(M * 32), *go = ivgpu_host_alloc(M * 16), *co = malloc(M * 16);
    random_boxes(fn, bx, M);
    if (ivgpu_list(fn, bx, M, go, 0)) return 1;
    cpu_list(fn, bx, M, co, 0);
    size_t ml = 0, mlf = 0, SL = 1u << 18;
    for (size_t b = 0; b < 2 * M; b++) ml += bits(go[b]) != bits(co[b]);
    for (size_t b = 0; b < SL; b++) { double o[2]; cpu_box_fe(fn, bx + 4 * b, o); mlf += bits(o[0]) != bits(go[2 * b]) || bits(o[1]) != bits(go[2 * b + 1]); }
    printf("f%d %zu random boxes, fp64: GPU vs CPU(rnerr) endpoint mismatches %zu; GPU vs fesetround on %zu: %zu\n",
           fn, M, ml, SL, mlf);
    bad |= ml || mlf;
    ivgpu_host_free(bx); ivgpu_host_free(go); free(co); free(glo); free(ghi); free(clo); free(chi);
    /* fp32 contrast version vs a CPU fp32 fesetround reference */
    int k32 = 10; size_t N32 = 1u << 20; float *flo = malloc(N32 * 4), *fhi = malloc(N32 * 4); red_t r32;
    if (ivgpu_grid_store(fn, k32, 32, flo, fhi, &r32)) return 1;
    size_t m32 = 0; float Rf = (float)R, hf = 2 * Rf / (float)(1u << k32);
    for (size_t b = 0; b < N32; b++) {
      size_t i = b & ((1u << k32) - 1), j = b >> k32; float box[4] = {-Rf + i * hf, -Rf + (i + 1) * hf, -Rf + j * hf, -Rf + (j + 1) * hf}, o[2];
      cpu_box_fef(fn, box, o); m32 += bitsf(o[0]) != bitsf(flo[b]) || bitsf(o[1]) != bitsf(fhi[b]);
    }
    printf("f%d grid 2^20 boxes, fp32 (contrast only): GPU vs CPU fp32 fesetround mismatches %zu\n\n", fn, m32);
    bad |= m32 != 0;
    free(flo); free(fhi);
  }
  printf("CORRECTNESS: %s\n\n", bad ? "FAIL" : "all bit-identical");

  /* ---------------- grid timing ---------------- */
  for (int fn = 0; fn < 2; fn++) {
    printf("## f%d grid (claim %s %g on [-%g,%g]^2)\n\n", fn, FN_UPPER[fn] ? "f <=" : "f >=", FN_BOUND[fn], FN_R[fn], FN_R[fn]);
    printf("| boxes | failing boxes | GPU kernel | GPU call | CPU 1 thread | CPU %d threads | GPU fp32 kernel | GPU call vs 1 thread | GPU call vs %d threads |\n", ncpu, ncpu);
    printf("|---|---|---|---|---|---|---|---|---|\n");
    for (int k = 5; k <= kmax; k++) {
      double N = ldexp(1, 2 * k), tg, t1, tm, t32; red_t rg, r1, rm, r32; float kms = 0, kms32 = 0;
      double kk[MAXREP]; int nk = 0;
      TIME_MEDIAN(tg, 0.3, (ivgpu_grid(fn, k, 64, &rg, &kms), kk[nk < MAXREP ? nk++ : nk - 1] = kms));
      qsort(kk, nk, sizeof(double), cmpd); double tk = kk[nk / 2] * 1e-3;
      nk = 0;
      TIME_MEDIAN(t32, 0.2, (ivgpu_grid(fn, k, 32, &r32, &kms32), kk[nk < MAXREP ? nk++ : nk - 1] = kms32));
      qsort(kk, nk, sizeof(double), cmpd); double tk32 = kk[nk / 2] * 1e-3;
      TIME_MEDIAN(t1, 0.3, r1 = cpu_grid(fn, k, 1, 0, 0));
      TIME_MEDIAN(tm, 0.3, rm = cpu_grid(fn, k, 0, 0, 0));
      if (!same_red(rg, r1) || !same_red(rg, rm)) { printf("REDUCTION MISMATCH k=%d\n", k); bad = 1; }
      printf("| 2^%d | %llu | %.3g ms (%.3g G/s) | %.3g ms | %.3g ms (%.3g M/s) | %.3g ms (%.3g M/s) | %.3g ms | %.2fx | %.2fx |\n",
             2 * k, (unsigned long long)rg.fails, tk * 1e3, N / tk * 1e-9, tg * 1e3, t1 * 1e3, N / t1 * 1e-6, tm * 1e3, N / tm * 1e-6,
             tk32 * 1e3, t1 / tg, tm / tg);
      fflush(stdout);
    }
    printf("\n");
  }

  /* ---------------- box-list timing (includes host<->device copies) ---------------- */
  printf("## Arbitrary box list, f1 (H2D 32 B/box + kernel + D2H 16 B/box)\n\n");
  printf("| boxes | GPU call | GPU kernel | CPU 1 thread | CPU %d threads | GPU vs 1 thread | GPU vs %d threads |\n", ncpu, ncpu);
  printf("|---|---|---|---|---|---|---|\n");
  {
    size_t M = 1u << 24; double *bx = ivgpu_host_alloc(M * 32), *go = ivgpu_host_alloc(M * 16), *co = malloc(M * 16);
    random_boxes(1, bx, M);
    for (int e = 0; e <= 24; e += 2) {
      size_t n = 1ull << e; double tg, t1, tm; float kms = 0;
      TIME_MEDIAN(tg, 0.2, ivgpu_list(1, bx, n, go, &kms));
      TIME_MEDIAN(t1, 0.2, cpu_list(1, bx, n, co, 1));
      TIME_MEDIAN(tm, 0.2, cpu_list(1, bx, n, co, 0));
      if (memcmp(go, co, n * 16)) { printf("LIST MISMATCH n=%zu\n", n); bad = 1; }
      printf("| 2^%d | %.3g us | %.3g us | %.3g us | %.3g us | %.2fx | %.2fx |\n", e, tg * 1e6, kms * 1e3, t1 * 1e6, tm * 1e6, t1 / tg, tm / tg);
      fflush(stdout);
    }
    ivgpu_host_free(bx); ivgpu_host_free(go); free(co);
  }
  printf("\nOVERALL: %s\n", bad ? "FAIL" : "OK (all GPU results bit-identical to CPU)");
  return bad;
}
