#!/bin/bash
# Builds the replay sample of data/sample/ from the full release assets (see ASSETS.md).
# Usage: code/impl1/make_sample.sh ASSETS OUT [SEED]
#   ASSETS: directory holding the unpacked assets (inputs/ and certificates/)
#   OUT: output directory; SEED: seed of the random choice (default 2026)
# For each input file, a random set of graphs that have a tree in the full rerun is copied, in input
# order, with pcpick, and their trees are copied with the graph index renumbered to the position in
# the sample. tdeep --replayfile on the sample then replays exactly those trees (Section 6.4).
set -eu
A=$1; O=$2; SEED=${3:-2026}
B=$(dirname "$0")/rust/target/release
mkdir -p "$O"
rnd() { yes "$SEED" | head -c 1000000; }
pick() { # TAG INPUT CERT M
  tag=$1; inp=$2; cert=$3; m=$4
  grep '^G ' "$cert" | awk '{print $2}' | sort -un | shuf -n "$m" --random-source=<(rnd) | sort -n > "$O/$tag.idx"
  "$B/pcpick" "$O/$tag.idx" "$O/$tag.pc" < "$inp"
  awk 'NR == FNR {r[$1] = FNR - 1; next}
       /^G / {keep = ($2 in r); if (keep) {print "G", r[$2], $3}; next}
       keep {print} /^E$/ {keep = 0}' "$O/$tag.idx" "$cert" > "$O/$tag.cert"
}
for j in 0 1 2; do pick k0_$j "$A/inputs/in_k0_$j.pc" "$A/certificates/full/k0_$j.cert" 100; done
for j in 0 1 2 3 4 5 6 7 8; do pick k1_$j "$A/inputs/in9_k1_$j.pc" "$A/certificates/full/k1_$j.cert" 20; done
pick k2 "$A/inputs/stageA_k2.pc" "$A/certificates/full/k2.cert" 40
pick k3 "$A/inputs/stageA_k3.pc" "$A/certificates/full/k3.cert" 1
# Trees of the second pass (pb) and of the passes of Table 3, on their d ranges and with their options
# (the jobs of code/impl1/replay_all.sh, written to TAG.opt and read by code/impl1/replay_sample.sh):
# every choice of H of each listed graph, with the graph index renumbered. The k = 3 graph 3 of the
# first level is covered by the two slices p1 (above 53.6578502 deg, without Local) and p3w (below it,
# with 3B shaving); the k = 2 graph 10 of b_k2.pc by p1 and pw; the slices p4b and p4c of the k = 1
# graph 77 of b_k1.pc (its third slice, p4a, takes 7 min) carry 3B shaving, as does p3 on the whole
# range.
case_pick() { # TAG PASS CLASS INPUT INDICES OPTIONS
  tag=$1; p=$2; k=$3; inp=$4; opts=$6
  printf '%s\n' $5 | sort -n > "$O/$tag.idx"
  "$B/pcpick" "$O/$tag.idx" "$O/$tag.pc" < "$inp"
  pos=0
  while read -r i; do
    for f in "$A/certificates/$p/${k}_$i"/g"${i}"_c*.cert; do
      c=${f##*_c}; c=${c%.cert}
      printf 'G %s %s\n' "$pos" "$c"; cat "$f"; echo E
    done
    pos=$((pos + 1))
  done < "$O/$tag.idx" > "$O/$tag.cert"
  echo "$opts" > "$O/$tag.opt"
}
LP="--local data/tie_targets.txt --pair"
case_pick pb_k2 pb k2 "$A/inputs/stageA_k2.pc" 55 "--iso 2 $LP"
case_pick p1_k3 p1 k3 "$A/inputs/stageA_k3.pc" 3 "--iso 3 --dlo 53.6578502"
case_pick p3w_k3 p3w k3 "$A/inputs/stageA_k3.pc" 3 "--iso 3 --dhi 53.6578502 --shave 8 $LP"
case_pick p1_k2 p1 k2 "$A/inputs/b_k2.pc" 10 "--iso 2 --dlo 53.6578502"
case_pick pw_k2 pw k2 "$A/inputs/b_k2.pc" 10 "--iso 2 --dhi 53.6578502 $LP"
case_pick p3_k2 p3 k2 "$A/inputs/b_k2.pc" 29 "--iso 2 --shave 8 $LP"
case_pick p4b_k1 p4b k1 "$A/inputs/b_k1.pc" 77 "--iso 1 --dlo 53.7 --dhi 54.6 --shave 8 $LP"
case_pick p4c_k1 p4c k1 "$A/inputs/b_k1.pc" 77 "--iso 1 --dlo 54.6 --shave 8 $LP"
