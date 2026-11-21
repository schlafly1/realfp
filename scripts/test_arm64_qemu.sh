#!/usr/bin/env bash
# Cross-test the aarch64 build of the RN+exact-error backend on an x86_64 box with
# AVX-512, using qemu-user. Expected outputs come from the AVX-512 kernels.
#   sudo apt install -y gcc-aarch64-linux-gnu libc6-dev-arm64-cross qemu-user
#   N=1000000 scripts/test_arm64_qemu.sh
set -euo pipefail
cd "$(dirname "$0")/.."
N="${N:-1000000}"
CFLAGS="-O2 -ffp-contract=off -frounding-math -fno-math-errno -Ic"
OUT="${TMPDIR:-/tmp}/interval64_qemu_$$"
mkdir -p "$OUT"
trap 'rm -rf "$OUT"' EXIT
cc $CFLAGS -mavx512f -mavx512vl tests/test_rnerr.c -o "$OUT/x86" -lm
aarch64-linux-gnu-gcc $CFLAGS -static tests/test_rnerr.c -o "$OUT/arm" -lm
aarch64-linux-gnu-gcc $CFLAGS -fPIC -static c/interval64.c tests/selftest_main.c -o "$OUT/arm_selftest" -lm
echo "== native x86: RN+err vs AVX-512 in-process"
"$OUT/x86" --vs-avx "$N"
echo "== aarch64 (qemu): RN+err vs AVX-512 expected-output file"
"$OUT/x86" --gen "$OUT/cases.bin" "$N"
qemu-aarch64 "$OUT/arm" --check "$OUT/cases.bin"
echo "== aarch64 (qemu): RN+err vs fesetround (FPCR) reference"
qemu-aarch64 "$OUT/arm" --vs-fe "$N"
echo "== aarch64 (qemu): library C self-test"
qemu-aarch64 "$OUT/arm_selftest"
echo "== aarch64 (qemu): CORE-MATH exp/log/sin/cos under RD/RU (FPCR) vs mpmath oracle"
TFLAGS="-O2 -frounding-math -ffp-contract=off -fno-math-errno"
for f in exp log sin cos; do aarch64-linux-gnu-gcc $TFLAGS -c c/coremath/$f.c -o "$OUT/cm_$f.o"; done
aarch64-linux-gnu-gcc $TFLAGS -c c/iv64_transc.c -o "$OUT/iv64_transc.o"
aarch64-linux-gnu-gcc -O2 -static tests/test_transc.c "$OUT"/cm_*.o "$OUT/iv64_transc.o" -o "$OUT/arm_transc" -lm
qemu-aarch64 "$OUT/arm_transc" tests/transc_oracle.txt
