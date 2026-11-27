#!/usr/bin/env bash
# Build manybox v2 (needs nvcc + g++ (or $CXX) with OpenMP; `NOGPU=1` builds the CPU engine only).
set -euo pipefail
cd "$(dirname "$0")"
CXX=${CXX:-g++}
CUDA=${CUDA:-/usr/local/cuda}
ARCH=${ARCH:-native}
mkdir -p build
CFL="-O2 -std=c++17 -ffp-contract=off -frounding-math -fno-math-errno -fopenmp"
"$CXX" $CFL -c mb2cpu.cpp -o build/mb2cpu.o
if [ -n "${NOGPU:-}" ]; then
  "$CXX" $CFL -DMB2_NO_GPU mb2.cpp build/mb2cpu.o -o build/mb2 -lm
else
  "$CUDA/bin/nvcc" -O3 -std=c++17 -arch="$ARCH" -fmad=false -ftz=false -prec-div=true -prec-sqrt=true \
    -Xcompiler -fPIC -c mb2gpu.cu -o build/mb2gpu.o
  "$CXX" $CFL -c mb2.cpp -o build/mb2.o
  "$CXX" -fopenmp build/mb2.o build/mb2cpu.o build/mb2gpu.o -o build/mb2 -L"$CUDA/lib64" -lcudart -lm -Wl,-rpath,"$CUDA/lib64"
fi
echo "built v2/build/mb2"
