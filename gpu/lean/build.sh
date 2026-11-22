#!/usr/bin/env bash
# Build the Lean FFI demo against gpu/build/libivgpu.so (run ../build.sh first).
set -euo pipefail
cd "$(dirname "$0")"
CUDA=${CUDA:-/usr/local/cuda}
mkdir -p ../build
lean -c ../build/IvGpu.c IvGpu.lean
leanc -O2 -I.. ../build/IvGpu.c shim.c -o ../build/ivgpu_lean -L../build -livgpu \
  -L"$CUDA/lib64" -lcudart -Wl,-rpath,'$ORIGIN' -Wl,-rpath,"$CUDA/lib64"
echo "built gpu/build/ivgpu_lean"
