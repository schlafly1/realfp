/* Standalone check of c/iv64_transc.c (CORE-MATH under RD / RU) against an
   mpmath oracle file (tests/transc_oracle.txt). Also times the kernels.
   Build: see scripts/test_arm64.sh. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

double iv64_dir_exp_down(double), iv64_dir_exp_up(double);
double iv64_dir_log_down(double), iv64_dir_log_up(double);
double iv64_dir_sin_down(double), iv64_dir_sin_up(double);
double iv64_dir_cos_down(double), iv64_dir_cos_up(double);
double iv64_cr_exp(double), iv64_cr_log(double), iv64_cr_sin(double), iv64_cr_cos(double);

static uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static double fromb(uint64_t u) { double x; memcpy(&x, &u, 8); return x; }
static int same(double got, const char *exp) {
  if (!strcmp(exp, "nan")) return got != got;
  unsigned long long e; sscanf(exp, "%llx", &e);
  return bits(got) == (uint64_t)e;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static double bench(double (*f)(double), const double *xs, int n, int reps) {
  volatile double sink = 0; double t0 = now();
  for (int r = 0; r < reps; r++) for (int i = 0; i < n; i++) sink += f(xs[i]);
  return (now() - t0) * 1e9 / ((double)n * reps);
}

int main(int argc, char **argv) {
  const char *path = argc > 1 ? argv[1] : "tests/transc_oracle.txt";
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); return 2; }
  char line[256], fn[16], xs[32], d[32], u[32];
  long n = 0, bad = 0;
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '#') continue;
    if (sscanf(line, "%15s %31s %31s %31s", fn, xs, d, u) != 4) continue;
    unsigned long long xb; sscanf(xs, "%llx", &xb); double x = fromb(xb);
    double rd, ru;
    if (!strcmp(fn, "exp")) { rd = iv64_dir_exp_down(x); ru = iv64_dir_exp_up(x); }
    else if (!strcmp(fn, "log")) { rd = iv64_dir_log_down(x); ru = iv64_dir_log_up(x); }
    else if (!strcmp(fn, "sin")) { rd = iv64_dir_sin_down(x); ru = iv64_dir_sin_up(x); }
    else if (!strcmp(fn, "cos")) { rd = iv64_dir_cos_down(x); ru = iv64_dir_cos_up(x); }
    else continue;
    n++;
    if (!same(rd, d) || !same(ru, u)) {
      if (bad < 10) printf("  MISMATCH %s(%s): got %016llx %016llx want %s %s\n", fn, xs,
        (unsigned long long)bits(rd), (unsigned long long)bits(ru), d, u);
      bad++;
    }
  }
  fclose(f);
  printf("transc oracle: %ld inputs (RD and RU each), %ld mismatches\n", n, bad);
  enum { N = 4096 };
  static double ex[N], lx[N], sx[N];
  uint64_t s = 0x1234;
  for (int i = 0; i < N; i++) {
    s = s * 6364136223846793005ULL + 1442695040888963407ULL;
    double t = (double)(s >> 11) / 9007199254740992.0;
    ex[i] = t * 40 - 20; lx[i] = 1e-9 + t * 1e6; sx[i] = t * 200 - 100;
  }
  int R = 200;
  printf("ns/call (C, direct):  exp RN %.1f  RD %.1f  RU %.1f | log RN %.1f  RD %.1f  RU %.1f\n",
    bench(iv64_cr_exp, ex, N, R), bench(iv64_dir_exp_down, ex, N, R), bench(iv64_dir_exp_up, ex, N, R),
    bench(iv64_cr_log, lx, N, R), bench(iv64_dir_log_down, lx, N, R), bench(iv64_dir_log_up, lx, N, R));
  printf("                      sin RN %.1f  RD %.1f  RU %.1f | cos RN %.1f  RD %.1f  RU %.1f\n",
    bench(iv64_cr_sin, sx, N, R), bench(iv64_dir_sin_down, sx, N, R), bench(iv64_dir_sin_up, sx, N, R),
    bench(iv64_cr_cos, sx, N, R), bench(iv64_dir_cos_down, sx, N, R), bench(iv64_dir_cos_up, sx, N, R));
  return bad ? 1 : 0;
}
