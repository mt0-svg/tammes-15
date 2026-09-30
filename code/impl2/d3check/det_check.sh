#!/bin/bash
# Deterministic replay of the default mode: the sampled graphs whose recorded pass-1 line is KILLED
# but whose pass-1 rerun stopped at the 5 s wall clock limit (compare_pass1.out) run again with the
# node budget alone (--nodes 30000, no time limit); each line must equal the recorded one outside
# the seconds and the LP counter.
# Usage: ./det_check.sh   Output: det_check.out
cd "$(dirname "$0")"
N=${T15:?see README.md}/n15full
D=${T15:?see README.md}/verify/d3check/l2
R=${T15:?see README.md}/verify/l2
: > det_check.out
for p in "k0 $N/l2/in_k0_0.pc 0 k0_0" "k1 $N/l2/in9_k1_0.pc 1 k1_0" "k2 $N/stageA_k2.pc 2 k2" "k3 $N/stageA_k3.pc 3 k3"; do
  set -- $p; c=$1; in=$2; iso=$3; rec=$R/$4.out
  only=$(awk 'NR == FNR { if ($2 == "KILLED") k[$1] = 1; next } $2 == "BUDGET" && ($1 in k) { print $1 }' $rec $D/p1_${c}_default.out | paste -sd,)
  [ -n "$only" ] || { echo "$c: none" >> det_check.out; continue; }
  ./vkill_probe.sh default det_$c $in $iso $only --nodes 30000
  awk '{ gsub(/ LP=[0-9]+/, ""); $5 = ""; print }' $D/det_${c}_default.out > /tmp/det_a.$$
  awk -v L=",$only," 'index(L, "," $1 ",") { gsub(/ LP=[0-9]+/, ""); $5 = ""; print }' $rec > /tmp/det_b.$$
  echo "$c: graphs $only; $(cat $D/det_${c}_default.time | paste -sd' '); lines equal to the recorded ones: $(comm -12 <(sort /tmp/det_a.$$) <(sort /tmp/det_b.$$) | wc -l) of $(wc -l < /tmp/det_a.$$)" >> det_check.out
  diff /tmp/det_a.$$ /tmp/det_b.$$ >> det_check.out
done
rm -f /tmp/det_a.$$ /tmp/det_b.$$
cat det_check.out
