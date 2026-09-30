#!/bin/bash
# Check of the face-size pruning and of the degree filter (Section 6.1): unrestricted plantri -p N,
# in M res/mod parts, piped into the standalone reader pcdeg, gives the number of 3-connected planar
# graphs on N vertices (OEIS A000944) and the number of those in the class (degrees 3..5, faces
# 3..6), which must equal plantri_md5 -p -f6 -u N. Prints one line per part, the totals, and the
# unsplit count of plantri_md5 (left out with MD5=0).
# Usage (from the repository root): code/impl1/enum/filtercheck.sh N [M] [JOBS]
set -eu
N=$1; M=${2:-1}; J=${3:-1}
W=$(mktemp)
export PL=$(realpath code/impl1/enum/bin/plantri) PC=$(realpath code/impl1/rust/target/release/pcdeg) N M
seq 0 $((M - 1)) | xargs -P "$J" -I{} bash -c 'echo "part {}/$M: $($PL -p $N {}/$M 2>/dev/null | $PC)"' \
  | sort -t/ -k1.6,1n > "$W"
cat "$W"
awk -v n=$N -v m=$M '{g += $4; d += $6; c += $NF} END {print "n=" n " unrestricted plantri -p | pcdeg, " m " parts: graphs " g " maxdeg<=5 " d " class " c}' "$W"
rm -f "$W"
[ "${MD5:-1}" = 0 ] ||
  echo "plantri_md5 -p -f6 -u $N: $(code/impl1/enum/bin/plantri_md5 -p -f6 -u $N 2>&1 | sed -n 's/^\([0-9]*\) polytopes.*/\1/p' | tail -1)"
