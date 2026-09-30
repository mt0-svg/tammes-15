#!/bin/sh
# Stage A checked by exact rational LP (Section 6.2): part R of M of plantri_md5 -p -f6 (15 - K), all
# survivors of stage A in SURVIVORS.pc and NSAMPLE graphs killed by stage A, drawn with SEED, go
# through stageA_exactlp.sage.
# Usage (from the repository root, after code/impl1/enum/build_plantri.sh):
#   sh code/sage/stageA_exactlp.sh K R M SURVIVORS.pc NSAMPLE SEED
set -eu
K=$1; R=$2; M=$3; S=$4; NS=$5; SEED=$6
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
code/impl1/enum/bin/plantri_md5 -p -f6 $((15 - K)) "$R/$M" > "$W/k${K}_${R}_plantri.pc" 2> /dev/null
sage code/sage/stageA_exactlp.sage "$W/k${K}_${R}_plantri.pc" "$S" "$K" "$NS" "$SEED"
