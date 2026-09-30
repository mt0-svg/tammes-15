#!/bin/bash
# The recorded lines of the plain pass of vkill for the graphs of the replay sample data/sample/ with
# k = 0 and 1, from records/second/l2/<file>.out of the records asset (ASSETS.md).
# Usage (from the repository root): code/impl2/sample_bulk.sh ASSETS > code/impl2/out/sample_bulk.txt
set -eu
L=$1/records/second/l2
echo "# The lines of the recorded plain pass of vkill (records/second/l2/<file>.out of the records asset, run with"
echo "# --nodes 30000 --maxsec 5) for the graphs of data/sample/: sample file, line in the sample, index in the level-2 input, then the recorded line."
for f in k0_0 k0_1 k0_2 k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8; do
  awk -v t=$f 'NR == FNR {pos[$1] = FNR - 1; next} ($1 in pos) {print t, pos[$1], $1, $0}' "data/sample/$f.idx" "$L/$f.out" | sort -k2,2n
done
