#!/usr/bin/env bash
# Compile a generated split certificate: split/run_split.sh NAME [JOBS] [THREADS]
#   the sub-files split/NAME/G*.lean (Mathlib-free) are compiled to .olean with up to JOBS lean
#   processes in parallel (MB_THREADS=THREADS C-checker threads each), then split/NAME/Main.lean.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd); name=$1; P=${2:-1}; T=${3:-8}
cd "$here/../../../../RealFPMathlib"
LP=$(lake env printenv LEAN_PATH)
lib="$(pwd)/../.lake/build/lib"; fastlib="$here/fast/.lake/build/lib/lean"
LOAD="--load-dynlib=$lib/libleaninterval64.so --plugin=$lib/libinterval64_Interval64.so --plugin=$fastlib/manyboxfast_ManyBoxFast.so"
LOAD="$LOAD --load-dynlib=$here/fast/.lake/build/lib/libmbtape.so --plugin=$fastlib/manyboxfast_ManyBoxTape.so"
out="$here/../build/olean"; mkdir -p "$out/split/$name"
export LEAN_PATH="$LP:$fastlib:$out" MB_THREADS=$T LOAD here out name
[ -f "$out/ManyBoxCert.olean" ] && [ "$out/ManyBoxCert.olean" -nt "$here/ManyBoxCert.lean" ] || \
  lake env lean $LOAD --root="$here" -o "$out/ManyBoxCert.olean" "$here/ManyBoxCert.lean"
t0=$(date +%s.%N)
ls "$here/split/$name"/G*.lean | xargs -P "$P" -I{} bash -c '
  f={}; b=$(basename $f .lean); s=$(date +%s.%N)
  lake env lean $LOAD --root="$here" -o "$out/split/$name/$b.olean" "$f"
  echo "  $b: $(python3 -c "print(round($(date +%s.%N) - $s, 2))") s"'
t1=$(date +%s.%N)
echo "== $name sub-files: $(python3 -c "print(round($t1 - $t0, 2))") s wall (P=$P, MB_THREADS=$T)"
lake env lean $LOAD --root="$here" "$here/split/$name/Main.lean"
t2=$(date +%s.%N)
echo "== $name Main: $(python3 -c "print(round($t2 - $t1, 2))") s wall"
