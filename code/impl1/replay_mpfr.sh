#!/bin/bash
# Replays samples of the trees of the first pass (Section 6.4) with the MPFR backend (--trig mpfr),
# with the options of the first pass (those of the full_* jobs of code/impl1/replay_all.sh).
# Usage (from the repository root, after building code/impl1/rust):
#   code/impl1/replay_mpfr.sh ASSETS OUT every20
#       the 5 % sample: in each level-2 input file, the graphs whose index is a multiple of 20
#       (tdeep --every 20), the graphs set aside from the first pass excepted (skip lists of
#       records/first/full); records/first/replay/k*.txt of the records asset hold its recorded run
#   code/impl1/replay_mpfr.sh ASSETS OUT SEED N0 N1 N2
#       a hash sample: N0, N1, N2 graphs of each certificate file of k = 0, 1, 2 and one of k = 3,
#       among the graphs with a tree, those of least SHA-256 of "SEED:JOB:INDEX" (code/impl1/sample_pick.pl);
#       the samples of 63 and 911 trees are SEED 777 with 10 3 5 and SEED 31337 with 200 30 40
#       (index lists code/impl1/out/mpfr_sample_777.txt, mpfr_sample_31337.txt)
#   code/impl1/replay_mpfr.sh ASSETS OUT samples
#       both hash samples, in OUT/777 and OUT/31337, and the total (recorded output
#       code/impl1/out/replay_mpfr_974.txt; exit 0 when all 974 replays are VERIFIED)
# Output: OUT/<job>.txt (per-graph lines), .log, .idx (the sampled indices), and one summary line per job
# on stdout.
set -u
A=$(realpath "$1"); O=$(realpath -m "$2"); S=$3
if [ "$S" = samples ]; then
  for s in "777 10 3 5" "31337 200 30 40"; do
    set -- $s; echo "## seed $1"; "$0" "$A" "$O/$1" "$@"
  done
  v=$(cat "$O"/777/*.txt "$O"/31337/*.txt | grep -c " VERIFIED ")
  n=$(cat "$O"/777/*.txt "$O"/31337/*.txt | wc -l)
  echo "MPFR samples: $v VERIFIED of $n replays"
  [ "$v" = 974 ] && [ "$n" = 974 ]; exit
fi
T=$(realpath code/impl1/rust/target/release/tdeep); PICK=$(realpath code/impl1/sample_pick.pl)
P=$(realpath data/params15ft.txt); L=$(realpath data/tie_targets.txt)
I=$A/inputs; C=$A/certificates/full; F=$A/records/first/full
mkdir -p "$O"
N0=(145088 145088 145087); N1=(3000 3000 3000 2999 2999 2999 2999 2999 2999)
jobs() { # name | input | certificate file | k | number of graphs | skip list of the graphs set aside | sample size
  for j in 0 1 2; do echo "full_k0_$j|$I/in_k0_$j.pc|$C/k0_$j.cert|0|${N0[$j]}||${4:-}"; done
  for j in 0 1 2 3 4 5 6 7 8; do echo "full_k1_$j|$I/in9_k1_$j.pc|$C/k1_$j.cert|1|${N1[$j]}|$F/b_k1_$j.idx|${5:-}"; done
  echo "full_k2|$I/stageA_k2.pc|$C/k2.cert|2|441|$F/skip_k2.idx|${6:-}"
  echo "full_k3|$I/stageA_k3.pc|$C/k3.cert|3|5|$F/skip_k3.idx|1"
}
jobs "$@" | while IFS='|' read -r name inp cert k n skip m; do
  if [ "$S" = every20 ]; then
    sel="--every 20"; [ -n "$skip" ] && sel="$sel --skip $skip"
  else
    grep '^G ' "$cert" | awk '{print $2}' | sort -un | "$PICK" "$S" "$name" "$m" > "$O/$name.idx"
    awk -v n="$n" 'NR == FNR {s[$1] = 1; next} END {for (i = 0; i < n; i++) if (!(i in s)) print i}' "$O/$name.idx" /dev/null > "$O/$name.skip"
    sel="--skip $O/$name.skip"
  fi
  $T "$P" --no-face --no-cuts --trig mpfr --iso "$k" --local "$L" --pair $sel --replayfile "$cert" < "$inp" 2> "$O/$name.log" \
    | sed 's/ [0-9a-f]\{40,\} / /' > "$O/$name.txt"
  echo "$name: $(grep -c ' VERIFIED ' "$O/$name.txt") VERIFIED of $(wc -l < "$O/$name.txt") replayed; $(grep -c -v ' VERIFIED ' "$O/$name.txt") other lines; $(tail -1 "$O/$name.log")"
done
