#!/bin/bash
# Pass-2 probe: the sampled graphs that relsys left not KILLED in pass 1 (probe_pass1.sh), relsys mode
# with the options of the recorded bulk pass 2 (vbulk/pass2.sh), two chunks at a time.
# Usage: ./probe_pass2.sh
cd "$(dirname "$0")"
N=${T15:?see README.md}/n15full
D=${T15:?see README.md}/verify/d3check/l2
left() { awk '$2 != "KILLED" {print $1}' $D/p1_$1_relsys.out; }
k2=$(left k2)
{
  echo "p2_k1 $N/l2/in9_k1_0.pc 1 $(left k1 | paste -sd,)"
  echo "p2_k2a $N/stageA_k2.pc 2 $(echo "$k2" | awk 'NR % 2 == 1' | paste -sd,)"
  echo "p2_k2b $N/stageA_k2.pc 2 $(echo "$k2" | awk 'NR % 2 == 0' | paste -sd,)"
  echo "p2_k3 $N/stageA_k3.pc 3 $(left k3 | paste -sd,)"
} | xargs -P 2 -L 1 bash -c './vkill_probe.sh relsys $0 $1 $2 $3 --shave 8 --incr --maxsec 60 --nodes 1000000'
