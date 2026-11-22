#!/usr/bin/env bash
# Build the GPU benchmark (needs nvcc + gcc with OpenMP). Not part of `lake build`.
set -euo pipefail
cd "$(dirname "$0")"
CUDA=${CUDA:-/usr/local/cuda}
ARCH=${ARCH:-native}            # e.g. sm_121 for GB10, sm_110 for Thor
mkdir -p build
# -fmad=false: no fma contraction (directed-rounding intrinsics are never fused anyway)
"$CUDA/bin/nvcc" -O3 -arch="$ARCH" -fmad=false -Xcompiler -fPIC -shared -o build/libivgpu.so ivgpu.cu
CFL="-O2 -ffp-contract=off -frounding-math -fno-math-errno -fopenmp -fPIC"
gcc $CFL -c cpu_ref.c -o build/cpu_ref.o
gcc $CFL -I"$CUDA/include" bench.c build/cpu_ref.o -o build/bench -Lbuild -livgpu \
  -L"$CUDA/lib64" -lcudart -lm -Wl,-rpath,'$ORIGIN' -Wl,-rpath,"$CUDA/lib64"
echo "built gpu/build/bench"
