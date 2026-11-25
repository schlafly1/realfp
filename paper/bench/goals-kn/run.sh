#!/bin/bash
# median of 3 wall times of `lake lean FILE` from RealFPMathlib (includes imports)
export PATH=$HOME/.elan/bin:$PATH
here=/workspace/scratch/paperbench; out=$here/results.txt; : > $out
cd /workspace/interval64_avx512/RealFPMathlib
for f in $here/base.lean $here/*_kernel.lean $here/*_native.lean; do
  n=$(basename $f .lean); ts=()
  for i in 1 2 3; do
    t0=$EPOCHREALTIME; timeout 900 lake lean $f > /tmp/pb_$n.log 2>&1; rc=$?; t1=$EPOCHREALTIME
    ts+=($(awk "BEGIN{printf \"%.2f\", $t1 - $t0}"))
  done
  med=$(printf "%s\n" "${ts[@]}" | sort -n | sed -n 2p)
  ax=$(tr '\n' ' ' < /tmp/pb_$n.log | grep -o "depends on axioms: \[[^]]*\]" | head -1)
  err=$(grep -c "error" /tmp/pb_$n.log)
  echo "$n rc=$rc err=$err median=$med samples=${ts[*]} | $ax" >> $out
done
cat $out
