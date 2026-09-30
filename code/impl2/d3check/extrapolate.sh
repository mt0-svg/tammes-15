#!/bin/bash
# Projection of a full relsys run of the second program from the probes (a heuristic estimate from
# samples, not a measurement): each stage is the recorded cost of the same stage of the second
# program's own runs, scaled by the ratio measured on the probe samples (probe time over recorded
# time on the same parts, graphs or cases, so the ratio also absorbs the load of the machine).
# Usage: ./extrapolate.sh   Output: extrapolate.out
cd "$(dirname "$0")"
S=../stageA2/logs
R=${T15:?see README.md}/verify/l2
C=${T15:?see README.md}/verify/cases
D=${T15:?see README.md}/verify/d3check/l2
{
echo "# stage A (plantri_md5 | vlevel1 --relsys over the whole enumeration, 2042 parts)"
pt=$(awk '/cpu=/ {split($0, a, "cpu="); split(a[2], b, " "); s += b[1]} END {print s}' $S/*.plantri)
vt=$(awk '{for (i = 1; i <= NF; i++) if ($i == "time") s += $(i + 1)} END {print s}' $S/*.log)
echo "recorded: plantri cpu $pt s, vlevel1 (Girard rows on) $vt s"
awk -v S=$S '/^k[0-9] part/ && / relsys: / && !/default 134/ {
  k = substr($1, 2); split($3, b, "/"); r = b[1]
  for (i = 1; i <= NF; i++) { if ($i == "user/wall" && !pu) pu = $(i + 2); else if ($i == "user/wall" && pu && !ru) ru = $(i + 2) }
  f = S "/k" k "_" r ".plantri"; while ((getline l < f) > 0) if (l ~ /cpu=/) { split(l, c, "cpu="); split(c[2], d, " "); pc = d[1] }
  f = S "/k" k "_" r ".log"; while ((getline l < f) > 0) for (j = 1; j <= split(l, e, " "); j++) if (e[j] == "time") vc = e[j + 1]
  P += pu; PC += pc; V += ru; VC += vc; n++; pu = ru = 0
} END { printf "probe (%d parts): plantri user %.2f s against recorded %.2f s (ratio %.3f); vlevel1 --relsys user %.2f s against recorded default %.2f s (ratio %.3f)\n", n, P, PC, P / PC, V, VC, V / VC; print P / PC, V / VC > "/tmp/xa.'$$'" }' stageA_probe.out
read rp rv < /tmp/xa.$$
A=$(echo "$pt * $rp + $vt * $rv" | bc -l)
printf "projected stage A: %.0f core s\n" $A
echo "# vkill pass 1 (--nodes 30000 --maxsec 5) over the 462,703 stage-A survivors"
B=0
for p in "k0 k0_?" "k1 k1_?" "k2 k2" "k3 k3"; do
  set -- $p
  tot=$(cat $R/$2.out | awk '{s += $5} END {print s}')
  rel=$(awk '{s += $5} END {print s}' $D/p1_$1_relsys.out)
  rec=$(awk 'NR == FNR {k[$1] = 1; next} ($1 in k) {s += $5} END {print s}' $D/p1_$1_relsys.out $R/$( [ $1 = k0 ] && echo k0_0 || ([ $1 = k1 ] && echo k1_0 || echo $1)).out)
  e=$(echo "$tot * $rel / $rec" | bc -l); B=$(echo "$B + $e" | bc -l)
  printf "%s: recorded class total %.1f s; sample relsys %.2f s against recorded %.2f s on the same graphs; projected %.0f s\n" $1 $tot $rel $rec $e
done
printf "projected pass 1: %.0f core s\n" $B
echo "# vkill pass 2 (--shave 8 --incr --maxsec 60) on the graphs pass 1 leaves"
Cc=0
for p in "k0 435263 k0_?" "k1 26994 k1_?" "k2 441 k2" "k3 5 k3"; do
  set -- $p
  ns=$(wc -l < $D/p1_$1_relsys.out); ls=$(awk '$2 != "KILLED"' $D/p1_$1_relsys.out | wc -l)
  rtot=$(cat $R/${3}_s8_*.out 2>/dev/null | awk '{s += $5} END {print s + 0}'); rn=$(cat $R/${3}_s8_*.out 2>/dev/null | wc -l)
  p2=$(cat $D/p2_$1*_relsys.out 2>/dev/null | awk '{s += $5} END {print s + 0}'); n2=$(cat $D/p2_$1*_relsys.out 2>/dev/null | wc -l)
  if [ $n2 -gt 0 ]; then
    e=$(echo "$2 * $ls / $ns * $p2 / $n2" | bc -l)
    printf "%s: sample leaves %d of %d; relsys pass 2 mean %.1f s over %d graphs; projected %.0f graphs, %.0f s\n" $1 $ls $ns $(echo "$p2 / $n2" | bc -l) $n2 $(echo "$2 * $ls / $ns" | bc -l) $e
  else
    e=$rtot
    printf "%s: sample leaves %d of %d; no relsys pass-2 data, recorded default pass 2 taken: %d graphs, %.0f s\n" $1 $ls $ns $rn $e
  fi
  Cc=$(echo "$Cc + $e" | bc -l)
done
printf "projected pass 2: %.0f core s\n" $Cc
echo "# the graphs pass 2 leaves: per-case passes (hard_600, fp3_120, res_600, slices)"
awk '/^== / {print}' hard_compare.out 2>/dev/null
rres=$(awk -F'|' 'NR > 1 {split($7, a, " "); s += a[1]} END {print s}' ../out/residue_verdicts.txt)
hr=$(awk '/^ratio/ {print $2}' hard_compare.out 2>/dev/null)
echo "recorded killing passes of the 42 residue graphs: $rres s; hard-case ratio relsys over recorded: ${hr:-unknown}"
Dd=$(echo "$rres * ${hr:-1}" | bc -l)
printf "projected residue: %.0f core s (a lower bound: failed attempts and BUDGET cases are not counted)\n" $Dd
T=$(echo "$A + $B + $Cc + $Dd" | bc -l)
printf "# total projected %.0f core s = %.2f core h, %.2f h wall at 2 cores\n" $T $(echo "$T / 3600" | bc -l) $(echo "$T / 7200" | bc -l)
} > extrapolate.out
rm -f /tmp/xa.$$
cat extrapolate.out
