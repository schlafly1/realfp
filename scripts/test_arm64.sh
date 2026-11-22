#!/usr/bin/env bash
# Build and test Interval64 on a native Linux box (arm64 / aarch64, e.g. Jetson Orin
# or DGX Spark; also works on x86_64 with AVX-512).
#
#   scripts/test_arm64.sh            # full run
#   N=2000000 scripts/test_arm64.sh  # more random pairs for the C differential test
#   SKIP_LEAN=1 scripts/test_arm64.sh  # only the standalone C tests (no Lean needed)
#
# Needs: a C compiler (`sudo apt install -y build-essential`), curl, git.
set -euo pipefail
cd "$(dirname "$0")/.."
N="${N:-1000000}"
ARCH="$(uname -m)"
CFLAGS="-O2 -ffp-contract=off -frounding-math -fno-math-errno -Ic"
X86FLAGS=""
if [ "$ARCH" = x86_64 ]; then X86FLAGS="-mavx512f -mavx512vl"; fi
OUT="${TMPDIR:-/tmp}/interval64_test_$$"
mkdir -p "$OUT"

command -v cc >/dev/null || { echo "no C compiler: run  sudo apt install -y build-essential"; exit 1; }
echo "== arch: $ARCH   cc: $(cc --version | head -1)"

echo "== 1. standalone C: RN+exact-error kernels vs fesetround reference ($N random pairs + specials)"
cc $CFLAGS $X86FLAGS tests/test_rnerr.c -o "$OUT/test_rnerr" -lm
"$OUT/test_rnerr" --vs-fe "$N"
if [ "$ARCH" = x86_64 ] && grep -q avx512f /proc/cpuinfo; then
  echo "== 1b. RN+exact-error vs AVX-512 embedded rounding"
  "$OUT/test_rnerr" --vs-avx "$N"
fi

echo "== 1c. CORE-MATH exp/log/sin/cos under RD/RU vs mpmath oracle (tests/transc_oracle.txt)"
TFLAGS="-O2 -frounding-math -ffp-contract=off -fno-math-errno"
if [ "$ARCH" = x86_64 ]; then TFLAGS="$TFLAGS -mfma"; fi
for f in exp log sin cos atan atan2 tan asin acos sinh cosh tanh log2 log10/log10 pow/pow; do cc $TFLAGS -c c/coremath/$f.c -o "$OUT/cm_$(basename $f).o"; done
cc $TFLAGS -c c/iv64_transc.c -o "$OUT/iv64_transc.o"
cc -O2 tests/test_transc.c "$OUT"/cm_*.o "$OUT/iv64_transc.o" -o "$OUT/test_transc" -lm
"$OUT/test_transc" tests/transc_oracle.txt
cc -O2 tests/test_func.c "$OUT"/cm_*.o "$OUT/iv64_transc.o" -o "$OUT/test_func" -lm
"$OUT/test_func" tests/func_oracle.txt

echo "== 2. library C self-test (backend + RN+err vs fesetround, interval policy)"
cc $CFLAGS -fPIC $X86FLAGS c/interval64.c tests/selftest_main.c -o "$OUT/selftest" -lm
"$OUT/selftest"

echo "== 3. micro-benchmark (ns/op, independent random inputs)"
"$OUT/test_rnerr" --bench 2000000

if [ "${SKIP_LEAN:-0}" = 1 ]; then echo "SKIP_LEAN=1: done"; exit 0; fi

if ! command -v lake >/dev/null; then
  if [ -x "$HOME/.elan/bin/lake" ]; then export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "== installing elan (Lean toolchain manager) into ~/.elan"
    curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  fi
fi

echo "== 4. lake build (library; C backend chosen by architecture)"
lake build
echo "== 5. lake exe interval64_tests (C runtime vs Lean spec, bit-exact; incl. exp/log/sin/cos Ziv spec, pi certificate, interval sin/cos)"
lake exe interval64_tests
echo "== 5b. lake exe interval128_tests (Interval128: C vs Lean spec bit-exact, enclosure vs exact rationals, tightness)"
lake build interval128_tests && lake exe interval128_tests
echo "== 5c. Interval128 C benchmark (vs Interval64 kernels; vs Arb if libflint-dev is installed)"
bench/i128/run.sh
echo "== 6. lake lean Examples.lean"
lake lean Examples.lean
echo "== 7. proofs + axiom report"
lake build Interval64Proofs
scripts/check_axioms.sh   # counts #print axioms results, fails on sorryAx / unexpected axioms
if [ "${SKIP_MATHLIB:-0}" != 1 ]; then
  echo "== 8. Mathlib layer: real enclosure proofs (exp/log/sin/cos), axiom report, examples"
  (cd RealFPMathlib && lake build && scripts/check_axioms.sh && lake lean Examples.lean)
fi
echo "== ALL DONE ($ARCH)"
