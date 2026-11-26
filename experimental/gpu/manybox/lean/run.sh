#!/usr/bin/env bash
# Run a Lean file of this directory with the realfp + Mathlib environment of ../../../../RealFPMathlib
# (which must be built). Usage: lean/run.sh File.lean   (builds ManyBoxCert first if needed)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../../../RealFPMathlib"
LP=$(lake env printenv LEAN_PATH)
# load realfp's compiled code (C kernels + precompiled core modules), as `lake lean` does
lib="$(pwd)/../.lake/build/lib"
LOAD="--load-dynlib=$lib/libleaninterval64.so --plugin=$lib/libinterval64_Interval64.so"
out="$here/../build/olean"; mkdir -p "$out"
if [ ! -f "$out/ManyBoxCert.olean" ] || [ "$here/ManyBoxCert.lean" -nt "$out/ManyBoxCert.olean" ]; then
  LEAN_PATH="$LP:$out" lake env lean $LOAD --root="$here" -o "$out/ManyBoxCert.olean" "$here/ManyBoxCert.lean"
fi
for f in "$@"; do
  echo "== $f"
  start=$(date +%s.%N)
  LEAN_PATH="$LP:$out" lake env lean $LOAD --root="$here" "$here/$f"
  end=$(date +%s.%N)
  echo "== $f: $(python3 -c "print(round($end - $start, 2))") s wall"
done
