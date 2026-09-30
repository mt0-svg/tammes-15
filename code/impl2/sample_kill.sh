#!/bin/sh
# The plain pass of vkill (Section 6.5: Local, Pair, Edge, at most 30,000 nodes per graph) on the graphs
# of the replay sample data/sample/ with k = 0 and 1, and the complete output: per file, the verdict
# line of every graph and the summary of vkill.
# Usage (from the repository root, after building code/impl2): code/impl2/sample_kill.sh
# The verdict and node count of each graph are compared with those of the recorded plain pass
# (code/impl2/out/sample_bulk.txt), which ran with a limit of 5 seconds per graph as well.
# Exit 0 when every graph is KILLED and no node count differs from a recorded KILLED line.
set -eu
V=code/impl2/target/release/vkill
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
bad=0
for f in data/sample/k0_*.pc data/sample/k1_*.pc; do
  tag=$(basename "$f" .pc); k=${tag#k}; k=${k%%_*}
  n=$(wc -l < "data/sample/$tag.idx")
  $V "$f" --iso "$k" --targets data/tie_targets.txt --local --pair --edge --nodes 30000 > "$W/out" 2> "$W/err" || true
  echo "== $tag"
  cat "$W/out" "$W/err"
  grep -q "graphs $n killed $n " "$W/err" && echo "$tag: $n KILLED of $n" || { echo "$tag: not all KILLED"; bad=1; }
  awk -v t="$tag" '$1 == t {print $5, $7}' code/impl2/out/sample_bulk.txt > "$W/rec"
  awk '/^[0-9]+ [A-Z]+ /{print $2, $4}' "$W/out" | paste -d' ' - "$W/rec" >> "$W/cmp"
done
awk '{if ($1 == $3 && $2 == $4) s++; else if ($3 == "BUDGET") b++; else d++}
  END {printf "node counts: %d identical to the recorded pass, %d recorded as BUDGET (time limit), %d different\n", s, b, d; exit d > 0}' "$W/cmp" || bad=1
[ $bad = 0 ] && echo "vkill sample: PASS" || { echo "vkill sample: FAIL"; exit 1; }
