#!/bin/bash
# LeanCert comparison problems through the `realfp` front door (kernel trust).
# Median of 3 wall times per file with `lake lean` (includes ~3.4 s of imports).
# LeanCert reference timings: see the README section on `realfp` / the comparison notes.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
out="$here/results.txt"; : > "$out"
cd "$here/../../../RealFPMathlib"
for f in "$here"/*.lean; do
  n=$(basename "$f" .lean); ts=()
  for i in 1 2 3; do
    t0=$EPOCHREALTIME; timeout 300 lake lean "$f" > "/tmp/$n.$i.log" 2>&1; rc=$?; t1=$EPOCHREALTIME
    ts+=($(awk "BEGIN{printf \"%.2f\", $t1 - $t0}"))
  done
  med=$(printf "%s\n" "${ts[@]}" | sort -n | sed -n 2p)
  ax=$(grep -o "depends on axioms: \[.*\]" "/tmp/$n.3.log" | head -1)
  echo "$n rc=$rc median=$med samples=${ts[*]} | $ax" >> "$out"
done
cat "$out"
