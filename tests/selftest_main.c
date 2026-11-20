/* Run the library's C self-test without Lean (e.g. cross-compiled for aarch64 and
   run under qemu-aarch64, or natively on an arm64 box):
     cc -O2 -fPIC -ffp-contract=off -frounding-math -fno-math-errno -Ic \
        c/interval64.c tests/selftest_main.c -o selftest -lm && ./selftest
   Exit status 0 iff the backend matches fesetround and RN+err matches fesetround
   (the software-oracle column is informational, as in `lake exe interval64_tests`). */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "interval64.h"

int main(void) {
  char buf[8192];
  uint64_t n = iv64_run_selftest(buf, sizeof buf);
  fputs(buf, stdout);
  unsigned long long c1, m1, c2, m2;
  const char *p = strstr(buf, "dir vs fe:"), *q = strstr(buf, "rn+err vs fe:");
  const char *iv = strstr(buf, "fail=");
  unsigned long long ivf = 1;
  if (!p || !q || !iv || sscanf(p, "dir vs fe: checked=%llu mismatches=%llu", &c1, &m1) != 2 ||
      sscanf(q, "rn+err vs fe: checked=%llu mismatches=%llu", &c2, &m2) != 2 ||
      sscanf(iv, "fail=%llu", &ivf) != 1) {
    printf("could not parse report (total recorded=%llu)\n", (unsigned long long)n);
    return 2;
  }
  int ok = m1 == 0 && m2 == 0 && ivf == 0;
  printf("%s: backend id=%d, dir-vs-fe mismatches=%llu, rn+err-vs-fe mismatches=%llu, interval fails=%llu\n",
         ok ? "PASS" : "FAIL", (int)iv64_backend_id(), m1, m2, ivf);
  return ok ? 0 : 1;
}
