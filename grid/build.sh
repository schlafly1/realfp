#!/usr/bin/env bash
# Build realfp-grid (docs/GPU.md). With CUDA (nvcc on PATH or in $CUDA/bin) it includes the GPU
# engine; otherwise, or with NOGPU=1, the CPU engine only. Output: grid/build/realfp-grid.
set -euo pipefail
cd "$(dirname "$0")"
CXX=${CXX:-c++}
CUDA=${CUDA:-/usr/local/cuda}
ARCH=${ARCH:-native}
mkdir -p build
CFL="-O2 -std=c++17 -ffp-contract=off -fno-math-errno -pthread"
NVCC=""
if [ -z "${NOGPU:-}" ]; then
  if command -v nvcc >/dev/null 2>&1; then NVCC=$(command -v nvcc)
  elif [ -x "$CUDA/bin/nvcc" ]; then NVCC="$CUDA/bin/nvcc"; fi
fi
"$CXX" $CFL -c src/problem.cpp -o build/problem.o
"$CXX" $CFL -c src/cpu.cpp -o build/cpu.o
"$CXX" $CFL -c src/main.cpp -o build/main.o
if [ -n "$NVCC" ]; then
  CUDADIR=$(dirname "$(dirname "$NVCC")")
  { echo 'static const char *RFG_OPS_HPP = R"RFG('; cat src/ops.hpp; echo ')RFG";'
    echo 'static const char *RFG_POL_HPP = R"RFG('; cat src/gpu_pol.hpp; echo ')RFG";'; } > build/embed.h
  # no fused multiply-add, IEEE division and square root: the directed-rounding intrinsics
  # (__dadd_rd ...) are exact regardless, but plain operations (midpoints) must round like the checker
  "$NVCC" -O3 -std=c++17 -arch="$ARCH" -fmad=false -ftz=false -prec-div=true -prec-sqrt=true \
    -Ibuild -c src/gpu.cu -o build/gpu.o
  "$CXX" -pthread build/main.o build/problem.o build/cpu.o build/gpu.o -o build/realfp-grid \
    -L"$CUDADIR/lib64" -lcudart -lnvrtc -lcuda -lm -Wl,-rpath,"$CUDADIR/lib64"
  echo "built grid/build/realfp-grid (CPU + CUDA)"
else
  "$CXX" $CFL -c src/nogpu.cpp -o build/nogpu.o
  "$CXX" -pthread build/main.o build/problem.o build/cpu.o build/nogpu.o -o build/realfp-grid -lm
  echo "built grid/build/realfp-grid (CPU only)"
fi
