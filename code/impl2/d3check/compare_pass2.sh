#!/bin/bash
# Pass-2 probe (relsys, probe_pass2.sh) against the recorded runs of the same graphs: the recorded
# pass-1 verdict, and the recorded pass-2 verdict when the recorded pass 1 left the graph.
# Usage: ./compare_pass2.sh   Output: compare_pass2.out
cd "$(dirname "$0")"
D=${T15:?see README.md}/verify/d3check/l2
R=${T15:?see README.md}/verify/l2
{
  echo "# class index | relsys pass 2: verdict nodes seconds | recorded pass 1 | recorded pass 2"
  for p in "k1 k1_0" "k2 k2" "k3 k3"; do
    set -- $p
    cat $D/p2_$1*_relsys.out | sort -n | while read -r i v nc nodes sec rest; do
      r1=$(awk -v i=$i '$1 == i {print $2, $4, $5}' $R/$2.out)
      r2=$(cat $R/$2_s8_*.out 2>/dev/null | awk -v i=$i '$1 == i {print $2, $4, $5}')
      echo "$1 $i | $v $nodes $sec | $r1 | ${r2:-none}"
    done
  done
  echo "relsys pass 2 verdicts: $(cat $D/p2_*_relsys.out | awk '{print $2}' | sort | uniq -c | paste -sd' ')"
} > compare_pass2.out
cat compare_pass2.out
