#!/bin/bash
# The survivors of vlevel1 (the first level of the second implementation) form a subset of those of
# tfilter (Section 6.2), part by part and byte for byte:
#  - a part whose two recorded sha256 (code/impl1/out/stageA_parts.txt for tfilter,
#    code/impl2/out/vlevel1_parts.txt for vlevel1) are equal has the same survivor file in both;
#  - for every other part, the tfilter survivor file of the part (inputs/stageA_k<k>.pc of the release
#    assets cut into the recorded parts, each checked against its recorded sha256) without the graphs
#    listed in code/impl2/out/stageA_vlevel1_drop.txt (k, part, index in the part) has the sha256
#    recorded for vlevel1: the vlevel1 survivor file is that subsequence of the tfilter one.
# The stageA_* checks of CI regenerate both recorded sha256 of every part from plantri.
# Usage (from the repository root, after building code/impl1/rust):
#   code/impl2/stageA_compare.sh ASSETS          the check; output code/impl2/out/stageA_compare.txt
#       (DROP=FILE replaces the drop list: the negative control of code/impl2/out/stageA_compare_control.txt)
#   code/impl2/stageA_compare.sh ASSETS VDIR     writes the drop list to stdout, computed from the
#       survivor files VDIR/k<k>_<r>.pc of vlevel1 --out (each must match its recorded sha256 and be
#       a subsequence of the tfilter part)
# Exit status 0 when every check passes.
set -u
A=$(realpath "$1"); VD=${2:-}
H=code/impl1/rust/target/release/pcrec
PICK=code/impl1/rust/target/release/pcpick
D=${DROP:-code/impl2/out/stageA_vlevel1_drop.txt}
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
st=0
sha() { sha256sum < "$1" | cut -d" " -f1; }
say() { if [ -n "$VD" ]; then echo "$@" >&2; else echo "$@"; fi; }
for k in 0 1 2 3; do
  # part, size, sha256 of tfilter; part, size, sha256 of vlevel1
  sed -n "s#^k$k \([0-9]*\)/[0-9]* .* killed_lp [0-9]* survivors \([0-9]*\) (.* | \([0-9a-f]\{64\}\)\$#\1 \2 \3#p" \
    code/impl1/out/stageA_parts.txt | sort -n > "$W/t$k"
  sed -n "s#^k$k \([0-9]*\)/[0-9]* graphs [0-9]* survivors \([0-9]*\) \([0-9a-f]\{64\}\)\$#\1 \2 \3#p" \
    code/impl2/out/vlevel1_parts.txt | sort -n > "$W/v$k"
  m=$(wc -l < "$W/t$k")
  [ "$(cut -d' ' -f1 "$W/t$k")" = "$(cut -d' ' -f1 "$W/v$k")" ] || { say "FAIL: k = $k: the two records list different parts"; st=1; continue; }
  mkdir "$W/cut$k"; cut -d' ' -f2 "$W/t$k" > "$W/c$k"
  $H --cut "$W/c$k" "$W/cut$k" < "$A/inputs/stageA_k$k.pc" || { say "FAIL: k = $k: stageA_k$k.pc does not split into the recorded parts"; st=1; continue; }
  paste -d' ' "$W/t$k" "$W/v$k" > "$W/tv$k"
  same=0; fewer=0; nt=0; nv=0; bad=0; drops=0; tok=0
  while read -r r tn ts _ vn vs; do
    [ "$(sha "$W/cut$k/$r.pc")" = "$ts" ] || { say "FAIL: k$k part $r: the tfilter part differs from its recorded sha256"; bad=$((bad + 1)); continue; }
    tok=$((tok + 1))
    nt=$((nt + tn)); nv=$((nv + vn))
    if [ "$ts" = "$vs" ]; then same=$((same + 1)); continue; fi
    fewer=$((fewer + 1))
    if [ -n "$VD" ]; then
      [ "$(sha "$VD/k${k}_$r.pc")" = "$vs" ] || { say "FAIL: k$k part $r: $VD/k${k}_$r.pc differs from its recorded sha256"; bad=$((bad + 1)); continue; }
      $H "$W/cut$k/$r.pc" | cut -d' ' -f2,11 > "$W/a"
      $H "$VD/k${k}_$r.pc" | cut -d' ' -f11 > "$W/b"
      awk -v k=$k -v r=$r 'NR == FNR { v[++nb] = $1; next }
        { if (j < nb && $2 == v[j + 1]) j++; else print k, r, $1 }
        END { if (j != nb) { print "FAIL: k" k " part " r ": vlevel1 part not a subsequence" > "/dev/stderr"; exit 1 } }' "$W/b" "$W/a" || bad=$((bad + 1))
      continue
    fi
    # the tfilter part without the listed graphs
    awk -v k=$k -v r=$r '$1 == k && $2 == r {print $3}' "$D" > "$W/drop"
    nd=$(wc -l < "$W/drop"); drops=$((drops + nd))
    awk 'NR == FNR { d[$1] = 1; next } END { for (i = 0; i < n; i++) if (!(i in d)) print i }' n="$tn" "$W/drop" /dev/null > "$W/keep"
    $PICK "$W/keep" "$W/sub.pc" < "$W/cut$k/$r.pc" 2> /dev/null
    if [ "$(sha "$W/sub.pc")" = "$vs" ] && [ $((tn - nd)) = "$vn" ]; then :
    else echo "FAIL: k$k part $r: the tfilter part without the listed graphs is not the vlevel1 survivor file"; bad=$((bad + 1)); fi
  done < "$W/tv$k"
  rm -rf "$W/cut$k"
  [ $bad = 0 ] || st=1
  [ -n "$VD" ] && continue
  echo "k = $k: $m parts; tfilter parts equal to their recorded sha256: $tok; identical survivor files $same; vlevel1 file = tfilter file without the listed graphs, byte for byte, in $((fewer - bad)) of $fewer other parts ($drops graphs); survivors tfilter $nt, vlevel1 $nv"
done
[ -n "$VD" ] && exit $st
if [ $st = 0 ]; then echo "stage A compare: PASS (the vlevel1 survivors are a subset of the tfilter survivors in every part)"
else echo "stage A compare: FAIL"; fi
exit $st
