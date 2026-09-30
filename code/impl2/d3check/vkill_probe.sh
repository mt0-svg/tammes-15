#!/bin/bash
# vkill probe on a stride sample of a stage-A survivor file: the frozen vkill (bin_d3) in one of two
# modes, with the options of the recorded bulk pass 1 (vbulk/round.sh: --nodes 30000 --maxsec 5) or
# of pass 2 (vbulk/pass2.sh: --shave 8 --incr --maxsec 60 --nodes 1000000) given in EXTRA:
#   default: --local --pair --edge (the recorded options; the output must repeat the recorded one)
#   relsys:  --relsys --local --pair (only relations of RelSys, Edge off)
# Usage: vkill_probe.sh MODE NAME INPUT ISO ONLY EXTRA...   ONLY = comma list of graph indices
# Output: $T15/verify/d3check/l2/NAME_MODE.{out,err,time}
set -u
MODE=$1; NAME=$2; IN=$3; ISO=$4; ONLY=$5; shift 5
cd "$(dirname "$0")/.."
B=${D3BIN:-${T15:?see README.md}/verify/bin_d3}/vkill
O=${T15:?see README.md}/verify/d3check/l2
T=../../data/tie_targets.txt
mkdir -p $O
case $MODE in
  default) opt="--local --targets $T --pair --edge" ;;
  relsys) opt="--relsys --local --targets $T --pair" ;;
esac
f=$O/${NAME}_$MODE
rm -f $f.out $f.err $f.time
/usr/bin/time -f "user %U wall %e maxrss_kb %M" -o $f.time $B $IN --iso $ISO --only $ONLY $opt "$@" > $f.out 2> $f.err
echo "exit $?" >> $f.time
