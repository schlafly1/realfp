#!/usr/bin/env bash
# C-level benchmark: Interval128 vs Interval64 kernels vs Arb (if libflint-dev is installed).
set -euo pipefail
cd "$(dirname "$0")"
CF="-O2 -ffp-contract=off -frounding-math -fno-math-errno -I../../../c"
ARCH=""
if [ "$(uname -m)" = x86_64 ]; then ARCH="-mavx512f -mfma"; fi
ARB=""; LIBS="-lm"
if [ -f /usr/include/flint/arb.h ]; then ARB="-DWITH_ARB"; LIBS="-lflint -lm"; fi
cc $CF $ARCH $ARB i128_bench.c -o /tmp/i128_bench $LIBS
/tmp/i128_bench
if [ "$(uname -m)" = x86_64 ]; then
  cc $CF -mfma -DIV64_FORCE_RNERR $ARB i128_bench.c -o /tmp/i128_bench_rn $LIBS
  /tmp/i128_bench_rn | grep -v Arb
fi
