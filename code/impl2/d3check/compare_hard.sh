#!/bin/bash
# Hard-case probe (probe_hard.sh) against the recorded KILLED passes of the same cases
# (verify/cases/<pass>/<tag>.txt, all families, Edge on): verdicts, nodes, seconds, and the ratio of
# the relsys seconds to the recorded seconds over the cases relsys kills.
# Usage: ./compare_hard.sh   Output: hard_compare.out
cd "$(dirname "$0")"
D=${T15:?see README.md}/verify/d3check/l2
C=${T15:?see README.md}/verify/cases
{
  echo "# tag | relsys: verdict nodes seconds (limit) | recorded: pass verdict nodes seconds"
  for p in k1_5:fp_s8_30:120 k1_3:fp_s8_30:120 k1_69:fp3_30:120 k1_0:fp3_120:120 k1_14:fp3_120:240 k2_4:res_600:240 \
           k1_68_d1:res_d1/k1_68:240 k2_33:res_600:300 k3_0:res_600:300 k0_0_43064:hard_600:300 k1_1:k1_1_all:600; do
    IFS=: read t pass lim <<< "$p"
    case $pass in */*) rf=$C/$pass.txt; pass=${pass%%/*} ;; *) rf=$C/$pass/$t.txt ;; esac
    a=$(awk '{print $2, $4, $5}' $D/hard_${t}_relsys.out); b=$(head -n 1 $rf | awk '{print $2, $4, $5}')
    echo "$t | relsys: ${a:-no output} ($lim s) $(tail -n 1 $D/hard_${t}_relsys.time) | recorded: $pass $b"
  done
} > hard_compare.out
awk -F'|' 'NR > 1 { split($2, a, " "); split($3, b, " "); t = $1; gsub(/ /, "", t); if (a[2] == "KILLED") { r += a[4]; c += b[5]; n++ } else { u++; ul = ul " " t } }
  END { printf "== relsys kills %d of %d cases; not killed:%s\nratio %.3f (relsys %.1f s over recorded %.1f s on the killed cases)\n", n, n + u, ul, r / c, r, c }' hard_compare.out >> hard_compare.out
cat hard_compare.out
