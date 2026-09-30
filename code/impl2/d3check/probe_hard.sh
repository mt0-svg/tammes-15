#!/bin/bash
# Hard-case probe: eleven recorded hard cases of the second program (free-point graphs of
# jobs156.txt, a k = 0 residue graph, one d slice of k1 #68), relsys mode with the search options
# of their recorded KILLED pass (--shave 8 --incr) and a time limit per case; two at a time.
# Lines: tag file index iso maxsec [extra options]. Recorded records: verify/cases/<pass>/<tag>.txt.
# Usage: ./probe_hard.sh
cd "$(dirname "$0")"
N=${T15:?see README.md}/n15full
cat <<LIST | xargs -P 2 -L 1 bash -c 'tag=$0 f=$1 i=$2 k=$3 s=$4; shift 4; ./vkill_probe.sh relsys hard_$tag $f $k $i --shave 8 --incr --maxsec $s --nodes 100000000 "$@"'
k1_5 $N/l2/b_k1.pc 5 1 120
k1_3 $N/l2/b_k1.pc 3 1 120
k1_69 $N/l2/b_k1.pc 69 1 120
k1_0 $N/l2/b_k1.pc 0 1 120
k1_14 $N/l2/b_k1.pc 14 1 240
k2_4 $N/l2/b_k2.pc 4 2 240
k1_68_d1 $N/l2/b_k1.pc 68 1 240 --dlo 53.7 --dhi 54.6
k2_33 $N/l2/b_k2.pc 33 2 300
k3_0 $N/stageA_k3.pc 0 3 300
k0_0_43064 $N/l2/in_k0_0.pc 43064 0 300
k1_1 $N/l2/b_k1.pc 1 1 600
LIST
