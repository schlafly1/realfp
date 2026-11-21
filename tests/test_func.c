/* Standalone check of the CORE-MATH RD/RU kernels in c/iv64_transc.c beyond
   exp/log/sin/cos against an mpmath oracle (tests/func_oracle.txt, written by
   scripts/gen_func_oracle.py). Build: see scripts/test_arm64_qemu.sh. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

double iv64_dir_atan_down(double), iv64_dir_atan_up(double), iv64_cr_atan(double);
double iv64_dir_atan2_down(double, double), iv64_dir_atan2_up(double, double);
double iv64_cr_atan2(double, double);

typedef struct { const char *name; int nargs; double (*d1)(double), (*u1)(double);
                 double (*d2)(double, double), (*u2)(double, double); } fn_t;
static const fn_t FNS[] = {
  {"atan", 1, iv64_dir_atan_down, iv64_dir_atan_up, 0, 0},
  {"atan2", 2, 0, 0, iv64_dir_atan2_down, iv64_dir_atan2_up},
};

static uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static double fromb(uint64_t u) { double x; memcpy(&x, &u, 8); return x; }
static int same(double got, const char *exp) {
  if (!strcmp(exp, "nan")) return got != got;
  unsigned long long e; sscanf(exp, "%llx", &e);
  return bits(got) == (uint64_t)e;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
  const char *path = argc > 1 ? argv[1] : "tests/func_oracle.txt";
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); return 2; }
  char line[256], tok[5][32];
  long n = 0, bad = 0, per[sizeof FNS / sizeof FNS[0]] = {0};
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '#') continue;
    int k = sscanf(line, "%31s %31s %31s %31s %31s", tok[0], tok[1], tok[2], tok[3], tok[4]);
    for (unsigned i = 0; i < sizeof FNS / sizeof FNS[0]; i++) {
      const fn_t *F = &FNS[i];
      if (strcmp(tok[0], F->name) || k != F->nargs + 3) continue;
      unsigned long long a, b = 0; sscanf(tok[1], "%llx", &a);
      if (F->nargs == 2) sscanf(tok[2], "%llx", &b);
      double rd, ru;
      if (F->nargs == 1) { rd = F->d1(fromb(a)); ru = F->u1(fromb(a)); }
      else { rd = F->d2(fromb(a), fromb(b)); ru = F->u2(fromb(a), fromb(b)); }
      const char *ed = tok[F->nargs + 1], *eu = tok[F->nargs + 2];
      n++; per[i]++;
      if (!same(rd, ed) || !same(ru, eu)) {
        if (bad < 10) printf("  MISMATCH %s(%s%s%s): got %016llx %016llx want %s %s\n", F->name,
          tok[1], F->nargs == 2 ? "," : "", F->nargs == 2 ? tok[2] : "",
          (unsigned long long)bits(rd), (unsigned long long)bits(ru), ed, eu);
        bad++;
      }
    }
  }
  fclose(f);
  printf("func oracle: %ld inputs (RD and RU each), %ld mismatches;", n, bad);
  for (unsigned i = 0; i < sizeof FNS / sizeof FNS[0]; i++) printf(" %s %ld", FNS[i].name, per[i]);
  printf("\n");
  enum { N = 4096 };
  static double xs[N], ys[N];
  uint64_t s = 0x1234;
  for (int i = 0; i < N; i++) {
    s = s * 6364136223846793005ULL + 1442695040888963407ULL;
    xs[i] = (double)(s >> 11) / 9007199254740992.0 * 20 - 10;
    s = s * 6364136223846793005ULL + 1442695040888963407ULL;
    ys[i] = (double)(s >> 11) / 9007199254740992.0 * 20 - 10;
  }
  int R = 200;
  volatile double sink = 0;
  double t0, t[6];
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_cr_atan(xs[i]); t[0] = now() - t0;
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_dir_atan_down(xs[i]); t[1] = now() - t0;
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_dir_atan_up(xs[i]); t[2] = now() - t0;
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_cr_atan2(ys[i], xs[i]); t[3] = now() - t0;
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_dir_atan2_down(ys[i], xs[i]); t[4] = now() - t0;
  t0 = now(); for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) sink += iv64_dir_atan2_up(ys[i], xs[i]); t[5] = now() - t0;
  double sc = 1e9 / ((double)N * R);
  printf("ns/call (C, direct): atan RN %.1f RD %.1f RU %.1f | atan2 RN %.1f RD %.1f RU %.1f\n",
    t[0] * sc, t[1] * sc, t[2] * sc, t[3] * sc, t[4] * sc, t[5] * sc);
  return bad ? 1 : 0;
}
