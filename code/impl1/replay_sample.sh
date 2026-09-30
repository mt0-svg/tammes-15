#!/bin/sh
# Replays the sample of recorded level-2 trees in data/sample/ (Section 6.4) with tdeep and prints the
# complete output: per file, the verdict line of every graph and the summary of tdeep, then the count.
# The files k<k>_*.cert hold trees of the full rerun (whole range); the files with a TAG.opt hold trees
# of the second pass and of the passes of Table 3 and are replayed with the options and d range of
# TAG.opt (code/impl1/make_sample.sh).
# Usage: code/impl1/replay_sample.sh [SAMPLEDIR]   (from the repository root; build code/impl1/rust first)
# Exit 0 when every sampled graph replays VERIFIED. TRIG=mpfr replays with the MPFR backend.
set -eu
S=${1:-data/sample}
T=code/impl1/rust/target/release/tdeep
BASE="--no-face --no-cuts --trig ${TRIG:-rig}"
OPT="$BASE --local data/tie_targets.txt --pair"
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
bad=0
for f in "$S"/*.cert; do
  tag=$(basename "$f" .cert); k=${tag#k}; k=${k%%_*}
  n=$(wc -l < "$S/$tag.idx")
  if [ -e "$S/$tag.opt" ]; then o="$BASE $(cat "$S/$tag.opt")"; else o="$OPT --iso $k"; fi
  $T data/params15ft.txt $o --replayfile "$f" < "$S/$tag.pc" > "$W/out" 2> "$W/err" || true
  v=$(grep -c ' VERIFIED ' "$W/out" || true)
  echo "== $tag"
  cat "$W/out" "$W/err"
  echo "$tag: $v VERIFIED of $n"
  [ "$v" = "$n" ] || bad=1
done
[ $bad = 0 ] && echo "replay sample: PASS" || { echo "replay sample: FAIL"; exit 1; }
