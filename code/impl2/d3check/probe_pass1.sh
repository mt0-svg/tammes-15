#!/bin/bash
# Pass-1 probe: stride samples of the stage-A survivor files (k = 0: every 145th graph of in_k0_0,
# k = 1: every 10th of in9_k1_0, k = 2: every 4th of stageA_k2, k = 3: all), vkill_probe.sh in both
# modes side by side (same load), options of the recorded bulk pass 1.
# Usage: ./probe_pass1.sh
cd "$(dirname "$0")"
N=${T15:?see README.md}/n15full
{
  echo "p1_k0 $N/l2/in_k0_0.pc 0 $(seq 0 145 145000 | paste -sd,)"
  echo "p1_k1 $N/l2/in9_k1_0.pc 1 $(seq 0 10 2990 | paste -sd,)"
  echo "p1_k2 $N/stageA_k2.pc 2 $(seq 0 4 440 | paste -sd,)"
  echo "p1_k3 $N/stageA_k3.pc 3 0,1,2,3,4"
} | while read -r name in iso only; do
  ./vkill_probe.sh default $name $in $iso $only --nodes 30000 --maxsec 5 &
  ./vkill_probe.sh relsys $name $in $iso $only --nodes 30000 --maxsec 5
  wait
done
