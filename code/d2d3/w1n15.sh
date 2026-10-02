#!/bin/bash
# The W1 class at n = 15 (class graphs with no vertex of the seven infeasible types of W1, Section 6.1 of the
# paper): the second enumerator fg (code/fg) against the plantri route, compared as sets of canonical codes.
#   generator:     fg gen 15 OUT <options>                      (W1 class only, one process)
#   plantri route: plantri_md5 -p -f6 15 r/M | fg ref 15 OUT_r   (every class graph read, the W1
#                  ones kept), r = 0..M-1, three parts at a time, the part lists merged (sort -m).
# Usage, from the repository root: LISTS=DIR code/d2d3/w1n15.sh RUN [FIRST LAST], RUN A or B. The two runs share no part and no generator tree:
#   run A: M = 256, generator --ring2 --caps --tight --rule 1;
#   run B: M = 243, generator --ring2 --caps --tight (rule 0).
# With FIRST LAST only those parts are made (a timing probe). A part whose two logs are complete is
# kept, so the script resumes after a crash. Writes out/w1n15/run<RUN>/: parts.tsv (per part: the
# plantri line, the fg ref lines, the sha256 of its code list), gen.txt, cmp.txt, codes.sha256;
# the code lists go to LISTS/w1n15/run<RUN>/.
# Env: FG (default code/fg/target/release/fg), PLANTRI_MD5 (default code/impl1/enum/bin/plantri_md5).
set -u
LISTS=$(realpath -m "${LISTS:?LISTS: a directory for the code lists}")
FG=$(realpath "${FG:-code/fg/target/release/fg}"); PLANTRI_MD5=$(realpath "${PLANTRI_MD5:-code/impl1/enum/bin/plantri_md5}")
cd "$(dirname "$0")"
RUN=$1
case $RUN in A) M=256; V="--ring2 --caps --tight --rule 1";; B) M=243; V="--ring2 --caps --tight";; *) exit 2;; esac
FIRST=${2:-0}; LAST=${3:-$((M - 1))}
O=out/w1n15/run$RUN
L=$LISTS/w1n15/run$RUN
P=$L/parts
mkdir -p "$O" "$P"
export LC_ALL=C FG PLANTRI_MD5 M P
part() {
  r=$1
  grep -q "polytopes written" "$P/r$r.plantri" 2> /dev/null && grep -q "^fg ref n 15 all" "$P/r$r.ref" 2> /dev/null && return 0
  s=$(date +%s%N)
  { "$PLANTRI_MD5" -p -f6 15 "$r/$M" 2> "$P/r$r.plantri" | "$FG" ref 15 "$P/r$r.codes" > "$P/r$r.ref.tmp"; } || return 1
  echo "wall_s $(awk -v a="$s" -v b="$(date +%s%N)" 'BEGIN {printf "%.2f", (b - a) / 1e9}')" >> "$P/r$r.plantri"
  mv "$P/r$r.ref.tmp" "$P/r$r.ref"
}
export -f part
seq "$FIRST" "$LAST" | xargs -P 3 -I{} bash -c 'part {}' || { echo "a part failed"; exit 1; }
n=$(ls "$P"/r*.ref 2> /dev/null | wc -l)
[ "$n" = "$M" ] || { echo "$n of $M parts done"; exit 0; }

# per-part record and totals
for r in $(seq 0 $((M - 1))); do
  pl=$(grep "polytopes written" "$P/r$r.plantri"); ws=$(sed -n 's/^wall_s //p' "$P/r$r.plantri")
  echo "part $r/$M plantri: $pl wall_s $ws"
  sed "s/^/part $r\/$M /" "$P/r$r.ref"
  echo "part $r/$M codes $(wc -l < "$P/r$r.codes") sha256 $(sha256sum < "$P/r$r.codes" | cut -d' ' -f1)"
done > "$O/parts.tsv"
sort -m -T "$L" "$P"/r*.codes > "$L/ref_w1_n15.codes"
( time "$FG" gen 15 "$L/gen_w1_n15.codes" $V ) > "$O/gen.txt" 2>&1
R=$L/ref_w1_n15.codes; G=$L/gen_w1_n15.codes
{
  echo "run $RUN: plantri parts M = $M; generator options $V"
  awk -v M=$M '/plantri: .* polytopes written/ {for (i = 1; i <= NF; i++) {if ($i == "polytopes") g += $(i-1); if ($i ~ /^cpu=/) {sub("cpu=", "", $i); c += $i}; if ($i == "wall_s") w += $(i+1)}}
    / all 0 sabotage 0 read / {for (i = 1; i <= NF; i++) {if ($i == "read") rd += $(i+1); if ($i == "class") cl += $(i+1); if ($i == "kept") k += $(i+1)}}
    END {printf "plantri route: %d parts, %d graphs written by plantri, fg ref read %d, class %d, kept (W1) %d; plantri cpu %.0f s, part wall sum %.0f s\n", M, g, rd, cl, k, c, w}' "$O/parts.tsv"
  for s in 3 4 5 6; do
    e=$(grep " fg ref n 15 s $s " "$O/parts.tsv" | sed 's/.* expected_ring \([0-9]*\).*/\1/' | awk '{t += $1} END {print t + 0}')
    c=$(grep " fg ref n 15 s $s " "$O/parts.tsv" | sed 's/.* classes \([0-9]*\) .*/\1/' | awk '{t += $1} END {print t + 0}')
    gc=$(sed -n "s/^fg gen n 15 s $s .* classes \([0-9]*\) .*/\1/p" "$O/gen.txt")
    g=$(sed -n "s/^fg gen n 15 s $s .* ok \([0-9]*\) .*/\1/p" "$O/gen.txt")
    echo "s $s plantri_route_classes $c generator_classes ${gc:-none} expected_ring $e generator_ok_leaves ${g:-none} $([ "$c" = "$gc" ] && [ "$e" = "$g" ] && echo equal || echo DIFFERENT)"
  done
  echo "reference: $(wc -l < "$R") codes, $(sort -c "$R" 2>&1 && echo sorted), $(uniq -d "$R" | wc -l) repeated"
  echo "generator: $(wc -l < "$G") codes, $(sort -c "$G" 2>&1 && echo sorted), $(uniq -d "$G" | wc -l) repeated"
  echo "only in reference: $(comm -23 "$R" "$G" | wc -l); only in generator: $(comm -13 "$R" "$G" | wc -l)"
  cmp -s "$R" "$G" && echo "verdict: sets equal" || echo "verdict: sets DIFFERENT"
} > "$O/cmp.txt"
( cd "$L" && sha256sum ref_w1_n15.codes gen_w1_n15.codes ) > "$O/codes.sha256"
cat "$O/cmp.txt" "$O/codes.sha256"
