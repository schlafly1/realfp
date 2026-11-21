#!/usr/bin/env bash
# usage: bench/time.sh file... ; prints seconds and errors
for f in "$@"; do
  s=$(date +%s%N); out=$(lake env lean "$f" 2>&1); e=$(date +%s%N)
  n=$(grep -c '^example\|^theorem' "$f")
  echo "$(basename $f) n=$n ms=$(( (e-s)/1000000 )) errs=$(echo "$out" | grep -c error)"
done
