#!/bin/bash
# Enumeration and first level (Sections 7.2 and 7.3): plantri_md5 -p -f6 (15 - k) in res/mod parts,
# piped into tfilter with the stage-A options, for k = 0 (2000 parts), 1 (40 parts), 2 and 3 (one
# part each). Survivors go to OUT/k<k>_<r>.pc, statistics to OUT/k<k>_<r>.log.
# Usage (from the repository root, after build_plantri.sh and building code/impl1/rust):
#   code/impl1/enum/stageA.sh OUT [JOBS] [CLASSES]      CLASSES: a subset of "0 1 2 3" (default all)
# The whole run took 72 minutes on 3 cores, most of it plantri at k = 0.
set -u
O=$(realpath -m "$1"); J=${2:-3}; K=${3:-"3 2 1 0"}
export T=$(realpath code/impl1/rust/target/release/tfilter) P=$(realpath data/params15ft.txt)
export E=$(realpath code/impl1/enum/bin/plantri_md5) O
mkdir -p "$O"
for k in $K; do
  case $k in 0) m=2000;; 1) m=40;; *) m=1;; esac
  for r in $(seq 0 $((m - 1))); do echo "$k $r $m"; done
done | xargs -P "$J" -L 1 bash -c '
  set -o pipefail
  k=$0; r=$1; m=$2; n=$((15 - k))
  [ -s $O/k${k}_$r.log ] && exit 0
  $E -p -f6 $n $r/$m 2>/dev/null | $T $P --no-face --no-cuts --iso $k -o $O/k${k}_$r.pc 2> $O/k${k}_$r.tmp \
    && mv $O/k${k}_$r.tmp $O/k${k}_$r.log
'
echo "done: $(ls "$O"/*.log | wc -l) parts"
