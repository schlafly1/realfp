#!/usr/bin/env bash
# Build the manybox benchmark (needs nvcc + gcc with OpenMP). Not part of `lake build`.
set -euo pipefail
cd "$(dirname "$0")"
CUDA=${CUDA:-/usr/local/cuda}
ARCH=${ARCH:-native}
mkdir -p build
"$CUDA/bin/nvcc" -O3 -arch="$ARCH" -fmad=false -Xcompiler -fPIC -c mbgpu.cu -o build/mbgpu.o
CFL="-O2 -ffp-contract=off -frounding-math -fno-math-errno -fopenmp"
gcc $CFL -c mbcpu.c -o build/mbcpu.o
gcc $CFL -c mbbench.c -o build/mbbench.o
g++ -fopenmp build/mbbench.o build/mbcpu.o build/mbgpu.o -o build/mbbench \
  -L"$CUDA/lib64" -lcudart -lm -Wl,-rpath,"$CUDA/lib64"
echo "built manybox/build/mbbench"
gcc $CFL -c mbexport.c -o build/mbexport.o
g++ -fopenmp build/mbexport.o build/mbcpu.o build/mbgpu.o -o build/mbexport \
  -L"$CUDA/lib64" -lcudart -lm -Wl,-rpath,"$CUDA/lib64"
echo "built manybox/build/mbexport"
