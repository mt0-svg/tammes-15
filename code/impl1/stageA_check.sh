#!/bin/bash
# Reruns the enumeration and stage A (Sections 6.1, 6.2) on parts FIRST..LAST of class k and compares
# each part with code/impl1/out/stageA_parts.txt: the statistics of tfilter (graph counts per class of
# faces, kills, survivors) and the sha256 of the survivor file. Prints the complete statistics of every
# part, then one line per part. With VLEVEL1=1 the same plantri stream also goes to vlevel1, the stage A of
# the second implementation (build code/impl2 first), compared with code/impl2/out/vlevel1_parts.txt.
# Usage (from the repository root, after code/impl1/enum/build_plantri.sh and building code/impl1/rust):
#   code/impl1/stageA_check.sh K FIRST LAST [JOBS]     (k = 0: parts 0..1999; k = 1: 0..39; k = 2, 3: 0)
# Exit 0 when every part is identical to the recorded one.
set -u
K=$1; A=$2; B=$3; J=${4:-1}
case $K in 0) M=2000;; 1) M=40;; *) M=1;; esac
export T=$(realpath code/impl1/rust/target/release/tfilter) P=$(realpath data/params15ft.txt)
export E=$(realpath code/impl1/enum/bin/plantri_md5) K M W=$(mktemp -d) VL=${VLEVEL1:-}
export V=$(realpath -m code/impl2/target/release/vlevel1)
trap 'rm -rf "$W"' EXIT
seq "$A" "$B" | xargs -P "$J" -I{} bash -c '
  set -o pipefail
  if [ -n "$VL" ]; then
    $E -p -f6 $((15 - K)) {}/$M 2>/dev/null | tee >($V --iso $K --out $W/{}.v.pc 2> $W/{}.vlog) \
      | $T $P --no-face --no-cuts --iso $K -o $W/{}.pc 2> $W/{}.log
    wait $!
    g=$(sed -n "s/^graphs \([0-9]*\) .* survivors \([0-9]*\) .*/graphs \1 survivors \2/p" $W/{}.vlog)
    echo "k$K {}/$M $g $(sha256sum < $W/{}.v.pc | cut -d" " -f1)" > $W/{}.vline
    rm -f $W/{}.v.pc
  else
    $E -p -f6 $((15 - K)) {}/$M 2>/dev/null | $T $P --no-face --no-cuts --iso $K -o $W/{}.pc 2> $W/{}.log
  fi
  { sed -n 1p $W/{}.log | sed -E "s/ time [0-9.]+s \([0-9.]+ us\/graph\)//"; sed -n 2p $W/{}.log; sha256sum < $W/{}.pc | cut -d" " -f1; } \
    | paste -s -d"|" | sed "s/|/ | /g; s/^/k$K {}\/$M /" > $W/{}.line
  rm -f $W/{}.pc'
bad=0
for r in $(seq "$A" "$B"); do
  l=$(cat "$W/$r.line" 2>/dev/null)
  echo "$l"
  if grep -qxF "$l" code/impl1/out/stageA_parts.txt; then echo "k$K $r/$M: identical to the recorded part"
  else echo "k$K $r/$M: DIFFERENT from the recorded part"; bad=1; fi
  if [ -n "$VL" ]; then
    l=$(cat "$W/$r.vline" 2>/dev/null)
    echo "vlevel1 $l"
    if grep -qxF "$l" code/impl2/out/vlevel1_parts.txt; then echo "k$K $r/$M: vlevel1 identical to the recorded part"
    else echo "k$K $r/$M: vlevel1 DIFFERENT from the recorded part"; bad=1; fi
  fi
done
[ $bad = 0 ] && echo "stage A k = $K, parts $A to $B: PASS" || { echo "stage A k = $K, parts $A to $B: FAIL"; exit 1; }
