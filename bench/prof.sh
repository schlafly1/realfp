#!/usr/bin/env bash
# usage: bench/prof.sh file... ; prints kernel "type checking" time per file
for f in "$@"; do
  t=/tmp/prof_$(basename $f)
  awk 'NR==1{print; print "set_option profiler true"; next}{print}' "$f" > $t
  cp $t bench/_prof.lean
  out=$(lake env lean bench/_prof.lean 2>&1)
  n=$(grep -c '^example\|^theorem' "$f")
  tc=$(echo "$out" | grep -E '^\s*type checking' | tail -1 | awk '{print $3}')
  echo "$(basename $f) n=$n typecheck=$tc errs=$(echo "$out" | grep -c 'error')"
done
rm -f bench/_prof.lean
