#!/usr/bin/env bash
# Regenerate the certificates used by lean/Check*.lean (GPU by default; pass `cpu` to use the CPU).
set -euo pipefail
cd "$(dirname "$0")"
how=${1:-gpu}
mkdir -p certs
for a in "0 4 p1_d4" "0 1 p1_d1" "0 0.015625 p1_d64" "0 0.0009765625 p1_d1024" "1 1 p2_d1" "1 0.125 p2_d8"; do
  set -- $a
  build/mbexport "$1" "$2" "certs/$3.cert" "$how"
done
