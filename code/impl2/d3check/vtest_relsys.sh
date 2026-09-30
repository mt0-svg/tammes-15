#!/bin/bash
# Known-answer tests of the relsys model on the true configurations C1 and C3 (vtest, frozen bin_d3):
# 1. the soundness tests of run_vtest.sh with --relsys: on every realised subgraph the boxes around
#    the true values are not refuted and keep them, and Local fires on the truth box (failures 0);
# 2. the search without Local over [dlo, dhi] on the realised subgraphs with at most MAXDEL deleted
#    contacts (--search NODES): a KILLED verdict would kill a genuine configuration (FAIL).
# Usage: ./vtest_relsys.sh MAXDEL NODES   Output: vtest_relsys.out
cd "$(dirname "$0")/.."
B=${D3BIN:-${T15:?see README.md}/verify/bin_d3}/vtest
O=${T15:?see README.md}/verify/d3check/vtest
T=../../data/tie_targets.txt
mkdir -p $O
run() { # name args...
  local n=$1; shift
  /usr/bin/time -f "user %U wall %e" -o $O/$n.time $B "$@" > $O/$n.out 2> $O/$n.err
  echo "$n: exit $? | $(tail -n 1 $O/$n.err) | $(cat $O/$n.time)"
}
{
  for c in c1 c3; do
    run ${c}_edges ../../data/bk15_$c.txt --relsys --maxdel 8 --boxes 24 --local --targets $T &
    run ${c}_vertex ../../data/bk15_$c.txt --relsys --maxdel 4 --vertex --boxes 24 --local --targets $T
    wait
  done
  for c in c1 c3; do
    run ${c}_search ../../data/bk15_$c.txt --relsys --maxdel $1 --boxes 0 --search $2
    echo "${c}_search verdicts: $(awk '/^search/ {print $2}' $O/${c}_search.out | sort | uniq -c | paste -sd' '); KILLED lines in stderr: $(grep -c 'FAIL search' $O/${c}_search.err)"
  done
} > d3check/vtest_relsys.out
cat d3check/vtest_relsys.out
