#!/usr/bin/env bash
# Prove a showcase bound with a split certificate (docs/GPU.md, RealFPGridShowcase/README.md).
#   grid/showcase.sh NAME MODULE K [K1] [ENGINE]
# NAME: problem in RealFPMathlib/RealFPGridShowcase/problems/NAME.problem (from Export.lean)
# MODULE: e.g. R8 -> generated RealFPGridShowcase/Gen/R8/*.lean, final RealFPGridShowcase/R8.lean
# K: split depth (2^K sub-checks at most), K1: group depth (2^K1 Lean files at most),
# ENGINE: auto (default) | cpu | gpu32 | gpu64.  Times are printed for every step.
set -euo pipefail
NAME=$1; MOD=$2; K=$3; K1=${4:-}; ENGINE=${5:-auto}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
T=${REALFP_GRID:-$ROOT/grid/build/realfp-grid}
[ -x "$T" ] || "$ROOT/grid/build.sh"
cd "$ROOT/RealFPMathlib"
P=RealFPGridShowcase/problems/$NAME.problem
S=RealFPGridShowcase/problems/$NAME.split
G=RealFPGridShowcase/Gen/$MOD
ts() { date +%s.%N; }
el() { python3 -c "print(f'{$2-$1:.1f} s')"; }
t0=$(ts); lake build RealFPGridShowcase.Export >/dev/null; t1=$(ts); echo "[1] problem files: $(el $t0 $t1)"
"$T" prove "$P" -o "$S" --split "$K" --engine "$ENGINE"; t2=$(ts); echo "[2] search: $(el $t1 $t2)"
rm -rf "$G"; python3 "$ROOT/grid/gen_lean.py" "$P" "$S" "$G" "RealFPGridShowcase.Gen.$MOD" ${K1:+--groups $K1}
t3=$(ts); echo "[3] generate: $(el $t2 $t3)"
# group files in parallel (one lean process per core), each C checker single-threaded
mods=$(cd "$G" && ls G*.lean | sed "s/\.lean$//; s/^/RealFPGridShowcase.Gen.$MOD./")
RFG_THREADS=1 lake build $mods >/dev/null; t4=$(ts); echo "[4] sub-checks (lake build, parallel): $(el $t3 $t4)"
lake build "RealFPGridShowcase.Gen.$MOD.Main" >/dev/null; t5=$(ts); echo "[5] glue: $(el $t4 $t5)"
lake build "RealFPGridShowcase.$MOD" 2>&1 | grep -E "axioms|error" || true; t6=$(ts); echo "[6] theorem: $(el $t5 $t6)"
echo "total: $(el $t0 $t6)"
