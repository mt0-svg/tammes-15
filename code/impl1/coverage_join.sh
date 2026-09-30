#!/bin/bash
# Coverage join of the second level (Sections 6.3 and 6.4): every stage-A survivor has VERIFIED
# replays whose d ranges cover the d range of data/params15ft.txt. It checks, and prints:
#  1. inputs/stageA_k<k>.pc, cut into the parts of code/impl1/out/stageA_parts.txt in part order,
#     gives the recorded survivor file (sha256) of every part; the stageA_* checks of CI regenerate
#     these parts with plantri and tfilter;
#  2. the survivors: no repeated record or canonical code, degrees at most 5, faces of size 3 to 6,
#     at least k hexagons, so that tdeep builds every choice of H;
#  3. every record of the level-2 inputs (in_k0_*, in9_k1_*, b_k1.pc, b_k2.pc; stageA_k2.pc and
#     stageA_k3.pc are read directly) is a survivor of its class, by its bytes or else by its
#     canonical code; the order of in_k0_* and in9_k1_*; the graphs set aside from the first pass
#     (the skip lists of records/first/full);
#  4. every job of the job list of code/impl1/replay_all.sh (LIST=1): its log (the d range tdeep
#     used, the summary line, backend rig, no failure, every graph of the input read), that d range
#     against the --dlo and --dhi of the command line, every per-graph line (index, faces equal to
#     those of the record, verdict VERIFIED or NO_CERTIFICATE, counts equal to those of the log),
#     and for every VERIFIED line a tree in the certificate file of the job for each choice of H;
#  5. for every survivor, the union of the d ranges of its VERIFIED replays covers the d range;
#  6. counts per k, then "coverage join: PASS" or "coverage join: FAIL" (exit status 1).
# Usage (from the repository root, after building code/impl1/rust):
#   code/impl1/coverage_join.sh ASSETS [REPLAY]
# ASSETS: the unpacked release assets (inputs/, certificates/, records/); REPLAY: an output
# directory of replay_all.sh (default: ASSETS/records/replay-v1, the recorded full replay).
# JOBLIST=FILE replaces the job list (negative controls, code/impl1/coverage_join_test.sh);
# SELFTEST=1 runs only the known-answer tests of the cover test.
set -u
AWK=${AWK:-awk}
J=code/impl1/coverage_join.awk
if [ -n "${SELFTEST:-}" ]; then $AWK -v SELFTEST=1 -f $J; exit; fi
A=$(realpath "$1"); R=$(realpath "${2:-$A/records/replay-v1}")
H=code/impl1/rust/target/release/pcrec
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
st=0

echo "Coverage join, code/impl1/coverage_join.sh; replay records: $(basename "$R")"
echo
echo "== 1. The stage-A survivor files against the recorded parts (code/impl1/out/stageA_parts.txt)"
for k in 0 1 2 3; do
  sed -n "s#^k$k \([0-9]*\)/\([0-9]*\) .* killed_lp [0-9]* survivors \([0-9]*\) (.* | \([0-9a-f]\{64\}\)\$#\1 \2 \3 \4#p" \
    code/impl1/out/stageA_parts.txt | sort -n > "$W/parts$k"
  m=$(head -1 "$W/parts$k" | cut -d' ' -f2)
  if [ "$(cut -d' ' -f1 "$W/parts$k" | tr '\n' ' ')" != "$(seq 0 $((m - 1)) | tr '\n' ' ')" ]; then
    echo "FAIL: k = $k: the recorded parts are not 0 to $((m - 1))"; st=1; continue
  fi
  mkdir "$W/cut$k"; cut -d' ' -f3 "$W/parts$k" > "$W/counts$k"
  if ! $H --cut "$W/counts$k" "$W/cut$k" < "$A/inputs/stageA_k$k.pc" 2> "$W/cuterr"; then
    echo "FAIL: k = $k: stageA_k$k.pc does not split into the recorded part sizes ($(tail -1 "$W/cuterr"))"; st=1; continue
  fi
  bad=0
  while read -r r _ c s; do
    [ "$(sha256sum < "$W/cut$k/$r.pc" | cut -d' ' -f1)" = "$s" ] || { echo "FAIL: k = $k part $r: sha256 differs"; bad=$((bad + 1)); }
  done < "$W/parts$k"
  [ $bad = 0 ] || st=1
  echo "k = $k: stageA_k$k.pc ($(awk '{s += $3} END {print s}' "$W/parts$k") graphs) cut in part order into parts of the recorded sizes: sha256 equal to the recorded one in $((m - bad)) of $m parts"
  rm -rf "$W/cut$k"
done
echo

# records of the survivor files first, then of the other level-2 inputs
for f in "$A"/inputs/stageA_k[0-3].pc; do $H "$f"; done > "$W/recs"
for f in "$A"/inputs/*.pc; do case $(basename "$f") in stageA_*) ;; *) $H "$f" ;; esac; done >> "$W/recs"
mkdir "$W/skip"; cp "$A"/records/first/full/*.idx "$W/skip/"
# the job list, the certificate headers of every job, the logs present
if [ -n "${JOBLIST:-}" ]; then cp "$JOBLIST" "$W/jobs"; else LIST=1 code/impl1/replay_all.sh "$A" "$W/rl" > "$W/jobs"; fi
cut -d'|' -f2 "$W/jobs" | sort -u | while read -r c; do grep '^G ' "$c" | awk -v c="$c" '{print c, $2, $3}'; done > "$W/certg"
for l in "$R"/*.log; do basename "$l" .log; done > "$W/logs"
set -- $($H --drange data/params15ft.txt | sed 's/^d in \[\([^,]*\), \([^]]*\)\].*/\1 \2/')
echo "tdeep --replayfile (code/impl1/rust/src/bin/tdeep.rs, lines 296 to 408) prints VERIFIED for a graph only"
echo "when every choice of H (all C(h, k) sets of k of its h hexagons, one choice for k = 0) has a recorded"
echo "tree that replays; Prob::new drops a choice only for a degree above 5 or a face of another size, which"
echo "section 2 excludes. Section 4 also checks, for every VERIFIED line, a tree in the certificate file of"
echo "the job for each of its choices of H and at least one leaf per choice."
echo
$AWK -v W="$W" -v R="$R" -v TLO="$1" -v THI="$2" -v PREFAIL=$st -f $J || st=1
exit $st
