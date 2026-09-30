#!/bin/sh
# The realised cases of Section 6.6, data/truth/*.pc, written by realize from the true configurations
# (data/bk15_c1.txt, data/bk15_c3.txt): the subgraphs of the contact graph, connected with minimum
# degree 3 and faces of size at most 6, that the configuration realises with every face corner below pi.
#   c1_real.pc, c3_real.pc      realize FILE 6: at most 6 edges removed
#   c1_realv.pc, c3_realv4.pc   realize FILE 4 --vertex: one point turned into a rattler (removed with its
#                               edges, an isolated point in the merged face) and at most 4 more edges removed
# The placement checks place_*_vertex of code/rerun.sh run realize with K = 3 and --vertex, hence fewer
# rattler cases there (95 and 45 against 104 and 48).
# Usage (from the repository root, after building code/impl1/rust): code/impl1/truth.sh
# Rewrites the four files and prints, per file, the realised subgraphs (the lines of realize that end in
# "realised") and the number of subgraphs tested.
set -eu
R=code/impl1/rust/target/release/realize
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
for spec in "c1_real bk15_c1 6" "c3_real bk15_c3 6" "c1_realv bk15_c1 4 --vertex" "c3_realv4 bk15_c3 4 --vertex"; do
  set -- $spec
  f=$1 c=$2; shift 2
  $R data/$c.txt "$@" -o data/truth/$f.pc > "$W/out"
  echo "== data/truth/$f.pc: realize data/$c.txt $*"
  grep ' realised$' "$W/out"
  echo "$f: $(grep -c . "$W/out") subgraphs tested, $(grep -c ' realised$' "$W/out") realised"
done
