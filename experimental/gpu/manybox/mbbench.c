/* manybox benchmark: same bisection on CPU 1 thread, CPU all threads and GPU.
   usage: mbbench [quick]   (exits nonzero if any backend disagrees) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include "mb.h"

static double now(void) { return omp_get_wtime(); }
static int cmp(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }
static double med(double *v, int n) { qsort(v, n, sizeof *v, cmp); return v[n / 2]; }
static int same(mb_stats a, mb_stats b) {
  return a.ok == b.ok && a.levels == b.levels && a.evals == b.evals && a.leaves == b.leaves &&
         a.unresolved == b.unresolved && a.peak == b.peak && a.hash == b.hash;
}
static void fmt(char *s, double t) {
  if (t < 1e-3) sprintf(s, "%.1f µs", t * 1e6);
  else if (t < 1) sprintf(s, "%.3g ms", t * 1e3);
  else sprintf(s, "%.3g s", t);
}

int main(int argc, char **argv) {
  int quick = argc > 1 && !strcmp(argv[1], "quick");
  int T = omp_get_max_threads();
  char gname[256]; mb_gpu_init(gname, sizeof gname);
  printf("GPU: %s; CPU threads (OpenMP): %d\n\n", gname, T);
  const char *pname[2] = {"P1: T8(x)+T8(y) <= 2+delta on [-1,1]^2", "P2: Choi-Lam S(x,y,z,w) >= -delta on [-1,1]^4"};
  double deltas[2][8] = {{4, 1, 0.25, 0.0625, 0.015625, 0.00390625, 0.0009765625, 0},
                         {2, 1, 0.5, 0.25, 0.125, 0.0625, 0, 0}};
  int bad = 0;
  for (int p = 0; p < 2; p++) {
    printf("## %s\n\n", pname[p]);
    printf("| delta | boxes evaluated | leaves | levels | peak level | GPU | GPU + cert copy | CPU 1 thread | CPU %d threads | GPU vs 1 thread | GPU vs %d threads | GPU Mbox/s | 1-thr Mbox/s | %d-thr Mbox/s |\n", T, T, T);
    printf("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n");
    for (int k = 0; deltas[p][k] != 0; k++) {
      double delta = deltas[p][k], bound = p == 0 ? 2 + delta : -delta;
      if (quick && ((p == 0 && delta < 0.01) || (p == 1 && delta < 0.2))) continue;
      int maxlevel = 80;
      /* agreement, with the full split-flag stream hashed */
      mb_cert c1 = {0}, cT = {0}, cg = {0};
      mb_stats s1 = mb_cpu_run(p, bound, maxlevel, 1, &c1);
      mb_stats sT = mb_cpu_run(p, bound, maxlevel, T, &cT);
      mb_stats sg = mb_gpu_run(p, bound, maxlevel, &cg);
      int agree = same(s1, sT) && same(s1, sg) && c1.len == cg.len && !memcmp(c1.flags, cg.flags, c1.len);
      if (!agree) { bad = 1; fprintf(stderr, "MISMATCH p=%d delta=%g\n", p, delta); }
      free(c1.flags); free(cT.flags); free(cg.flags);
      /* timings (median); fewer repetitions for big runs */
      int R = s1.evals < 1000000 ? 21 : (s1.evals < 20000000 ? 5 : 3);
      double tg[21], tgc[21], t1[21], tT[21];
      mb_gpu_run(p, bound, maxlevel, NULL);  /* warm-up */
      for (int r = 0; r < R; r++) { double a = now(); mb_gpu_run(p, bound, maxlevel, NULL); tg[r] = now() - a; }
      for (int r = 0; r < R; r++) { mb_cert c = {0}; double a = now(); mb_gpu_run(p, bound, maxlevel, &c); tgc[r] = now() - a; free(c.flags); }
      for (int r = 0; r < R; r++) { double a = now(); mb_cpu_run(p, bound, maxlevel, 1, NULL); t1[r] = now() - a; }
      mb_cpu_run(p, bound, maxlevel, T, NULL);
      for (int r = 0; r < R; r++) { double a = now(); mb_cpu_run(p, bound, maxlevel, T, NULL); tT[r] = now() - a; }
      double g = med(tg, R), gc = med(tgc, R), c1t = med(t1, R), cTt = med(tT, R);
      char sg_[32], sgc[32], s1_[32], sT_[32];
      fmt(sg_, g); fmt(sgc, gc); fmt(s1_, c1t); fmt(sT_, cTt);
      printf("| %g | %llu | %llu | %d | %llu | %s | %s | %s | %s | %.2fx | %.2fx | %.1f | %.1f | %.1f |%s\n", delta,
             (unsigned long long)s1.evals, (unsigned long long)s1.leaves, s1.levels, (unsigned long long)s1.peak,
             sg_, sgc, s1_, sT_, c1t / g, cTt / g, s1.evals / g / 1e6, s1.evals / c1t / 1e6, s1.evals / cTt / 1e6,
             agree ? (s1.ok ? "" : " (NOT proved)") : " MISMATCH");
      fflush(stdout);
    }
    printf("\n");
  }
  printf(bad ? "AGREEMENT: MISMATCH\n" : "AGREEMENT: all runs identical (stats and full split-flag stream, CPU 1 thread = CPU all threads = GPU)\n");
  return bad;
}
