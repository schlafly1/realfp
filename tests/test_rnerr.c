/* Standalone differential test + micro-benchmark for the portable
   round-to-nearest + exact-error-term kernels (c/iv64_rnerr.h), which are the
   Interval64 runtime backend on aarch64.

   Build (any arch):
     cc -O2 -ffp-contract=off -frounding-math -fno-math-errno -Ic tests/test_rnerr.c -o test_rnerr -lm
   On x86_64 add -mavx512f to enable the AVX-512 oracle (--vs-avx, --gen).

   Modes:
     --vs-fe  N [seed]   compare RN+err vs fesetround (FPCR / MXCSR) reference
     --vs-avx N [seed]   compare RN+err vs AVX-512 embedded rounding (x86 + AVX-512)
     --gen FILE N [seed] write cases with AVX-512 expected outputs (x86 + AVX-512)
     --check FILE        check RN+err against a --gen file (e.g. under qemu-aarch64)
     --bench [N]         micro-benchmark RN+err vs fesetround (and AVX-512 on x86)
   N is the number of (a,b) pairs; each pair checks 10 ops (add/sub/mul/div down/up,
   sqrt(a) down/up). The special-value cross product is always included.
   Exit status 0 iff there are no mismatches. NaN results compare equal to any NaN. */
#define _GNU_SOURCE
#include <stdint.h>
static uint64_t n_slow, n_ovf;
#define IV64R_SLOW_HOOK() (n_slow++)
#define IV64R_OVF_HOOK() (n_ovf++)
#include "iv64_rnerr.h"

#include <fenv.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(__x86_64__) && defined(__AVX512F__)
#define HAVE_AVX 1
#include <immintrin.h>
#else
#define HAVE_AVX 0
#endif


static inline uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static inline double fromb(uint64_t u) { double x; memcpy(&x, &u, 8); return x; }

enum { OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_SQRT, NOPS };
static const char *opname[NOPS] = {"add", "sub", "mul", "div", "sqrt"};

/* ---------------- kernels under test ---------------- */
static double rn(int op, int up, double a, double b) {
  switch (op) {
    case OP_ADD: return iv64r_add(a, b, up);
    case OP_SUB: return iv64r_sub(a, b, up);
    case OP_MUL: return iv64r_mul(a, b, up);
    case OP_DIV: return iv64r_div(a, b, up);
    default:     return iv64r_sqrt(a, up);
  }
}

/* ---------------- fesetround reference ---------------- */
__attribute__((noinline)) static double fe(int op, int up, double a, double b) {
  int old = fegetround();
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  volatile double va = a, vb = b, r;
  switch (op) {
    case OP_ADD: r = va + vb; break;
    case OP_SUB: r = va - vb; break;
    case OP_MUL: r = va * vb; break;
    case OP_DIV: r = va / vb; break;
    default:     r = sqrt(va); break;
  }
  fesetround(old);
  return r;
}

#if HAVE_AVX
#define RD (_MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC)
#define RU (_MM_FROUND_TO_POS_INF | _MM_FROUND_NO_EXC)
static double avx(int op, int up, double a, double b) {
  __m128d x = _mm_set_sd(a), y = _mm_set_sd(b);
  switch (op) {
    case OP_ADD: return _mm_cvtsd_f64(up ? _mm_add_round_sd(x, y, RU) : _mm_add_round_sd(x, y, RD));
    case OP_SUB: return _mm_cvtsd_f64(up ? _mm_sub_round_sd(x, y, RU) : _mm_sub_round_sd(x, y, RD));
    case OP_MUL: return _mm_cvtsd_f64(up ? _mm_mul_round_sd(x, y, RU) : _mm_mul_round_sd(x, y, RD));
    case OP_DIV: return _mm_cvtsd_f64(up ? _mm_div_round_sd(x, y, RU) : _mm_div_round_sd(x, y, RD));
    default:     return _mm_cvtsd_f64(up ? _mm_sqrt_round_sd(x, x, RU) : _mm_sqrt_round_sd(x, x, RD));
  }
}
#endif

static int same(double x, double y) {
  if (isnan(x)) return isnan(y);
  return bits(x) == bits(y);
}

/* ---------------- case generators ---------------- */
static uint64_t sm(uint64_t *s) {
  uint64_t z = (*s += 0x9e3779b97f4a7c15ull);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}
/* random double with biased exponent in [elo, ehi] (0 = subnormal), random sign/mantissa */
static double rexp(uint64_t *s, int elo, int ehi) {
  uint64_t r = sm(s);
  uint64_t e = (uint64_t)(elo + (int)(sm(s) % (uint64_t)(ehi - elo + 1)));
  uint64_t m = r & 0xfffffffffffffull;
  /* sometimes use short mantissas (exact / tie-prone cases) */
  switch ((r >> 52) & 7) {
    case 0: m &= ~((1ull << 40) - 1); break;
    case 1: m &= ~((1ull << 26) - 1); break;
    case 2: m = (r >> 55) & 1 ? 0xfffffffffffffull : 0; break;
    default: break;
  }
  return fromb(((r >> 63) << 63) | (e << 52) | m);
}
static double ulps(double x, int k) {  /* move x by k ulps (bit steps) */
  uint64_t u = bits(x);
  if (!isfinite(x)) return x;
  return fromb(u + (uint64_t)(int64_t)k);
}

static const uint64_t specials[] = {
  0x0000000000000000ull, 0x8000000000000000ull, 0x0000000000000001ull, 0x8000000000000001ull,
  0x0000000000000002ull, 0x0000000000000003ull, 0x000fffffffffffffull, 0x800fffffffffffffull,
  0x0008000000000000ull, 0x0010000000000000ull, 0x8010000000000000ull, 0x0010000000000001ull,
  0x0020000000000000ull, 0x3ff0000000000000ull, 0xbff0000000000000ull, 0x3ff0000000000001ull,
  0x3fefffffffffffffull, 0x3fe0000000000000ull, 0x4000000000000000ull, 0xc000000000000000ull,
  0x4008000000000000ull, 0x3fd5555555555555ull, 0x3ca0000000000000ull, 0x3cb0000000000000ull,
  0x7fefffffffffffffull, 0xffefffffffffffffull, 0x7feffffffffffffeull, 0x7fe0000000000000ull,
  0x7fd0000000000000ull, 0x5fe0000000000000ull, 0x2000000000000000ull, 0x1ff0000000000000ull,
  0x0370000000000000ull, 0x0360000000000000ull, 0x0380000000000000ull, 0x0370000000000001ull,
  0x7ff0000000000000ull, 0xfff0000000000000ull, 0x7ff8000000000000ull, 0xfff8000000000000ull,
  0x7ff0000000000001ull, 0x7ff4000000000000ull, 0x4330000000000000ull, 0x4340000000000000ull,
  0x3f50000000000000ull, 0xbcb0000000000000ull,
};
#define NSPEC ((int)(sizeof specials / sizeof specials[0]))

static void gen_pair(uint64_t *s, double *pa, double *pb) {
  double a, b;
  switch (sm(s) % 12) {
    case 0: a = fromb(sm(s)); b = fromb(sm(s)); break;                 /* raw bits */
    case 1: a = rexp(s, 0, 2046); b = rexp(s, 0, 2046); break;         /* any finite */
    case 2: a = rexp(s, 1023 - 60, 1023 + 60); b = rexp(s, 1023 - 60, 1023 + 60); break;
    case 3: /* cancellation: b ~ -a +- few ulps, or a shifted */
      a = rexp(s, 1, 2046);
      b = ulps(-a, (int)(sm(s) % 9) - 4);
      if (sm(s) & 1) b = ldexp(b, (int)(sm(s) % 120) - 60);
      break;
    case 4: a = rexp(s, 0, 60); b = rexp(s, 0, 60); break;             /* subnormal / tiny */
    case 5: /* products / quotients near the subnormal range */
      a = rexp(s, 1023 - 600, 1023 - 400); b = rexp(s, 1023 - 680, 1023 - 500);
      if (sm(s) & 1) b = 1.0 / b;
      break;
    case 6: a = rexp(s, 1986, 2046); b = rexp(s, 1986, 2046); break;   /* huge */
    case 7: /* near overflow products / quotients / sums */
      a = rexp(s, 1023 + 500, 1023 + 524); b = rexp(s, 1023 + 490, 1023 + 524);
      if (sm(s) & 1) b = 1.0 / b;
      break;
    case 8: /* small integers (exact) */
      a = (double)((int64_t)(sm(s) % 2001) - 1000); b = (double)((int64_t)(sm(s) % 2001) - 1000);
      if (sm(s) & 1) a = ldexp(a, (int)(sm(s) % 2100) - 1100);
      break;
    case 9: { /* division / sqrt near exact: a = q*b nudged, a = s*s nudged */
      double q = rexp(s, 1023 - 30, 1023 + 30); b = rexp(s, 1023 - 30, 1023 + 30);
      a = ulps(q * b, (int)(sm(s) % 5) - 2);
      if (sm(s) & 1) { double r = rexp(s, 1, 2046); a = ulps(fabs(r * r), (int)(sm(s) % 5) - 2); }
      break; }
    case 10: { /* tiny exact quotients / sqrt of tiny */
      a = rexp(s, 0, 120); b = rexp(s, 1023 - 10, 1023 + 60);
      if (sm(s) & 1) { double t = a; a = b; b = t; }
      break; }
    default: /* mixed specials and randoms */
      a = (sm(s) & 1) ? fromb(specials[sm(s) % NSPEC]) : rexp(s, 0, 2046);
      b = (sm(s) & 1) ? fromb(specials[sm(s) % NSPEC]) : rexp(s, 0, 2046);
      break;
  }
  if (isnan(a) && !(bits(a) & 0x7ffffffffffffull)) a = 0; /* paranoia */
  *pa = a; *pb = b;
}

/* ---------------- driver ---------------- */
typedef double (*ref_t)(int, int, double, double);
static uint64_t checked[NOPS], mism[NOPS];
static int shown = 0;

static void check_pair(ref_t ref, const char *rname, double a, double b) {
  for (int op = 0; op < NOPS; op++)
    for (int up = 0; up < 2; up++) {
      double x = rn(op, up, a, b), y = ref(op, up, a, b);
      checked[op]++;
      if (!same(x, y)) {
        mism[op]++;
        if (shown++ < 20)
          printf("MISMATCH %s.%s a=%a [%016llx] b=%a [%016llx] rn=%a [%016llx] %s=%a [%016llx]\n",
                 opname[op], up ? "up" : "down", a, (unsigned long long)bits(a), b,
                 (unsigned long long)bits(b), x, (unsigned long long)bits(x), rname, y,
                 (unsigned long long)bits(y));
      }
    }
}

static int report(const char *what) {
  uint64_t tc = 0, tm = 0;
  printf("%s\n", what);
  for (int op = 0; op < NOPS; op++) {
    printf("  %-5s checked=%llu mismatches=%llu\n", opname[op], (unsigned long long)checked[op],
           (unsigned long long)mism[op]);
    tc += checked[op]; tm += mism[op];
  }
  printf("  TOTAL checked=%llu mismatches=%llu\n", (unsigned long long)tc, (unsigned long long)tm);
  printf("  (RN+err calls that took the tiny-result fesetround slow path: %llu; RN overflow fixups: %llu)\n",
         (unsigned long long)n_slow, (unsigned long long)n_ovf);
  printf("  rounding mode after: %s\n", fegetround() == FE_TONEAREST ? "nearest" : "CHANGED");
  return tm == 0 && fegetround() == FE_TONEAREST ? 0 : 1;
}

static void run(ref_t ref, const char *rname, uint64_t n, uint64_t seed) {
  for (int i = 0; i < NSPEC; i++)
    for (int j = 0; j < NSPEC; j++) check_pair(ref, rname, fromb(specials[i]), fromb(specials[j]));
  uint64_t s = seed;
  for (uint64_t k = 0; k < n; k++) {
    double a, b;
    gen_pair(&s, &a, &b);
    check_pair(ref, rname, a, b);
    check_pair(ref, rname, b, a);
  }
}

/* file record: op(1) up(1) pad(6) a b expected = 32 bytes */
typedef struct { uint8_t op, up, pad[6]; uint64_t a, b, r; } rec_t;

static double now_s(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + 1e-9 * t.tv_nsec;
}

typedef double (*bin_t)(double, double);
static inline double rn_add_up(double a, double b) { return iv64r_add(a, b, 1); }
static inline double rn_mul_up(double a, double b) { return iv64r_mul(a, b, 1); }
static inline double rn_div_up(double a, double b) { return iv64r_div(a, b, 1); }
static inline double rn_sqrt_up(double a, double b) { (void)b; return iv64r_sqrt(a, 1); }
static inline double fe_add_up(double a, double b) { return fe(OP_ADD, 1, a, b); }
static inline double fe_mul_up(double a, double b) { return fe(OP_MUL, 1, a, b); }
static inline double fe_div_up(double a, double b) { return fe(OP_DIV, 1, a, b); }
static inline double fe_sqrt_up(double a, double b) { return fe(OP_SQRT, 1, a, b); }
static inline double rn_plain_add(double a, double b) { return a + b; }
#if HAVE_AVX
static inline double avx_add_up(double a, double b) { return avx(OP_ADD, 1, a, b); }
static inline double avx_mul_up(double a, double b) { return avx(OP_MUL, 1, a, b); }
static inline double avx_div_up(double a, double b) { return avx(OP_DIV, 1, a, b); }
static inline double avx_sqrt_up(double a, double b) { return avx(OP_SQRT, 1, a, b); }
#endif

/* Throughput over independent inputs; ns/op, best of reps. always_inline so each
   call site with a constant kernel is specialized (no indirect call in the loop). */
static inline __attribute__((always_inline))
double bench(bin_t f, const double *xa, const double *xb, size_t n, int reps) {
  volatile double sink = 0;
  double best = 1e30;
  for (int r = 0; r < reps; r++) {
    double t0 = now_s(), acc = 0;
    for (size_t i = 0; i < n; i++) acc += f(xa[i], xb[i]);
    double t = (now_s() - t0) / (double)n * 1e9;
    sink += acc;
    if (t < best) best = t;
  }
  (void)sink;
  return best;
}

static void bench_table(const char *title, const double *xa, const double *xb, size_t n) {
  printf("%s\n", title);
  printf("  plain RN add (no rounding control) %6.2f\n", bench(rn_plain_add, xa, xb, n, 5));
  printf("  op      rn+err   fesetround");
#if HAVE_AVX
  printf("   avx512");
#endif
  printf("\n");
#if HAVE_AVX
#define ROW(nm, r, f, a) printf("  %-7s %7.2f   %9.2f   %6.2f\n", nm, bench(r, xa, xb, n, 5), bench(f, xa, xb, n, 5), bench(a, xa, xb, n, 5))
#else
#define ROW(nm, r, f, a) printf("  %-7s %7.2f   %9.2f\n", nm, bench(r, xa, xb, n, 5), bench(f, xa, xb, n, 5))
#endif
  ROW("add_up", rn_add_up, fe_add_up, avx_add_up);
  ROW("mul_up", rn_mul_up, fe_mul_up, avx_mul_up);
  ROW("div_up", rn_div_up, fe_div_up, avx_div_up);
  ROW("sqrt_up", rn_sqrt_up, fe_sqrt_up, avx_sqrt_up);
#undef ROW
}

static void count_paths(const char *nm, const double *xa, const double *xb, size_t n) {
  uint64_t s0 = n_slow, o0 = n_ovf;
  volatile double t = 0;
  for (size_t i = 0; i < n; i++)
    t += rn_add_up(xa[i], xb[i]) + rn_mul_up(xa[i], xb[i]) + rn_div_up(xa[i], xb[i]) + rn_sqrt_up(xa[i], 0);
  (void)t;
  printf("  (%s set: fesetround slow paths %llu, overflow fixups %llu, over 4 x %zu ops)\n", nm,
         (unsigned long long)(n_slow - s0), (unsigned long long)(n_ovf - o0), n);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: see header of tests/test_rnerr.c\n"); return 2; }
  const char *mode = argv[1];
  if (!strcmp(mode, "--vs-fe") || !strcmp(mode, "--vs-avx")) {
    uint64_t n = argc > 2 ? strtoull(argv[2], 0, 0) : 1000000;
    uint64_t seed = argc > 3 ? strtoull(argv[3], 0, 0) : 0x1234567ull;
    if (!strcmp(mode, "--vs-fe")) {
      run(fe, "fe", n, seed);
      return report("RN+err vs fesetround reference");
    }
#if HAVE_AVX
    run(avx, "avx", n, seed);
    return report("RN+err vs AVX-512 embedded rounding");
#else
    fprintf(stderr, "--vs-avx needs x86_64 built with -mavx512f\n");
    return 2;
#endif
  }
  if (!strcmp(mode, "--gen")) {
#if HAVE_AVX
    if (argc < 4) return 2;
    FILE *f = fopen(argv[2], "wb");
    if (!f) { perror("fopen"); return 2; }
    uint64_t n = strtoull(argv[3], 0, 0), seed = argc > 4 ? strtoull(argv[4], 0, 0) : 0xabcdefull;
    uint64_t cnt = 0, s = seed;
    for (int64_t k = -(int64_t)(NSPEC * NSPEC); k < (int64_t)n; k++) {
      double a, b;
      if (k < 0) { int idx = (int)(k + NSPEC * NSPEC); a = fromb(specials[idx / NSPEC]); b = fromb(specials[idx % NSPEC]); }
      else gen_pair(&s, &a, &b);
      for (int op = 0; op < NOPS; op++)
        for (int up = 0; up < 2; up++) {
          rec_t r = {(uint8_t)op, (uint8_t)up, {0}, bits(a), bits(b), bits(avx(op, up, a, b))};
          fwrite(&r, sizeof r, 1, f);
          cnt++;
        }
    }
    fclose(f);
    printf("wrote %llu cases to %s\n", (unsigned long long)cnt, argv[2]);
    return 0;
#else
    fprintf(stderr, "--gen needs x86_64 built with -mavx512f\n");
    return 2;
#endif
  }
  if (!strcmp(mode, "--check")) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[2], "rb");
    if (!f) { perror("fopen"); return 2; }
    rec_t r;
    while (fread(&r, sizeof r, 1, f) == 1) {
      double a = fromb(r.a), b = fromb(r.b), y = fromb(r.r), x = rn(r.op, r.up, a, b);
      checked[r.op]++;
      if (!same(x, y)) {
        mism[r.op]++;
        if (shown++ < 20)
          printf("MISMATCH %s.%s a=%a b=%a rn=%a expected=%a\n", opname[r.op], r.up ? "up" : "down", a, b, x, y);
      }
    }
    fclose(f);
#if defined(__aarch64__)
    const char *arch = "aarch64";
#elif defined(__x86_64__)
    const char *arch = "x86_64";
#else
    const char *arch = "other";
#endif
    char what[128];
    snprintf(what, sizeof what, "RN+err (%s build) vs AVX-512 expected outputs from %s", arch, argv[2]);
    return report(what);
  }
  if (!strcmp(mode, "--bench")) {
    size_t n = argc > 2 ? strtoull(argv[2], 0, 0) : 1000000;
    double *xa = malloc(n * sizeof *xa), *xb = malloc(n * sizeof *xb);
    uint64_t s = 42;
    printf("micro-benchmark, ns/op (throughput), best of 5, %zu independent inputs\n", n);
    /* normal range: |x| in [2^-20, 2^21), random sign (a > 0 so sqrt is meaningful) */
    for (size_t i = 0; i < n; i++) {
      xa[i] = fabs(rexp(&s, 1023 - 20, 1023 + 20)); xb[i] = rexp(&s, 1023 - 20, 1023 + 20);
    }
    bench_table("[normal] random normal-range operands", xa, xb, n);
    count_paths("normal", xa, xb, n);
    s = 4242;
    for (size_t i = 0; i < n; i++) gen_pair(&s, &xa[i], &xb[i]);
    bench_table("[mixed] test-generator operands (specials, subnormal, huge, NaN, cancellation, ...)", xa, xb, n);
    count_paths("mixed", xa, xb, n);
    free(xa); free(xb);
    return 0;
  }
  fprintf(stderr, "unknown mode %s\n", mode);
  return 2;
}
