#!/usr/bin/env bash
# Mathlib-free benchmark / agreement test of the C checker: `./bench.sh [nomut] [nospec]`.
# Needs `lake build +ManyBoxFast:dynlib +ManyBoxTape:dynlib` here first. `main` is run by
# `lean --run`; checkHex / checkC3 are called from the precompiled libraries.
set -euo pipefail
cd "$(dirname "$0")"
core="$(pwd)/../../../../../.lake/build/lib"
fast="$(pwd)/.lake/build/lib"
so() { ls "$1"/$2 2>/dev/null | head -1; }   # Lake names the module libraries differently by version
LOAD="--load-dynlib=$core/libleaninterval64.so --plugin=$(so "$core" "*interval64_Interval64.so")"
LOAD="$LOAD --plugin=$(so "$fast" "lean/manyboxfast_ManyBoxFast.so" || true)"
LOAD="$LOAD --load-dynlib=$fast/libmbtape.so"
LOAD="$LOAD --plugin=$(so "$fast" "lean/manyboxfast_ManyBoxTape.so" || true)"
lake env lean $LOAD --run TapeBench.lean "$@"
