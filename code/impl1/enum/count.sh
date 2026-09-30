#!/bin/bash
# Counts of plantri -p -f6 -u N in M res/mod parts (Section 6.1), one line per part and the sum.
# PROG = plantri (no degree filter, check (c)) or plantri_md5 (maximum degree 5, check (a)).
# Usage (from the repository root, after build_plantri.sh): code/impl1/enum/count.sh PROG N [M] [JOBS]
set -eu
W=$(mktemp)
export B=$(realpath code/impl1/enum/bin/$1) N=$2 M=${3:-1}
seq 0 $((M - 1)) | xargs -P "${4:-1}" -I{} bash -c \
  'echo "$(basename $B) -p -f6 -u $N {}/$M: $($B -p -f6 -u $N {}/$M 2>&1 | sed -n "s/^\([0-9]*\) polytopes.*/\1/p")"' \
  | sort -t/ -k1,1 -V > "$W"
cat "$W"
echo "sum: $(awk '{s += $NF} END {print s}' "$W")"
rm -f "$W"
