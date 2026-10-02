#!/bin/bash
# Replays every recorded level-2 tree of the release assets (Section 6.4) with the tdeep of this
# repository: the full rerun (every graph of the level-2 inputs on the whole range) and the
# per-case passes (the free-point cases and the second pass on their d ranges and options).
# Usage (from the repository root, after building code/impl1/rust):
#   code/impl1/replay_all.sh ASSETS OUT [NPAR]
# ASSETS holds the unpacked assets (inputs/, certificates/); results go to OUT, one .txt (one line
# per graph), .log (summary line "replay: verified V failed F missing certificates M") and .time
# per job. Resumable: a job whose .log holds its summary line is not rerun. Then
#   code/impl1/replay_summary.sh OUT
# prints the table of code/impl1/out/replay_summary.txt. With LIST=1 the script gathers the per-case
# trees into OUT/rf, prints the job list (name|certificate file|input|options) and runs nothing; the
# coverage join code/impl1/coverage_join.sh reads it. ONLY=NAME|NAME|... runs only those jobs, in that order (the
# replay jobs of ci.yml split the list this way).
set -u
A=$(realpath "$1"); O=$(realpath -m "$2"); NPAR=${3:-4}
T=$(realpath code/impl1/rust/target/release/tdeep)
P=$(realpath data/params15ft.txt); L=$(realpath data/tie_targets.txt)
I=$A/inputs; C=$A/certificates
mkdir -p "$O/rf"
B="$T $P --no-face --no-cuts --trig ${TRIG:-rig}"
LP="--local $L --pair"

# Per-case trees certificates/<pass>/<tag>/g<idx>_c<choice>.cert, gathered into one replay file per
# pass and class.
for p in p1 pw p3w p2 p3 p4a p4b p4c p5a p5b p5c pb; do
  for k in k0_0 k0_1 k0_2 k1 k2 k3; do
    out=$O/rf/${p}_$k.rf; : > "$out"
    for f in "$C/$p/${k}_"*/*.cert; do
      [ -e "$f" ] || continue
      g=$(basename "$f" .cert); gi=${g%_c*}; gi=${gi#g}; ci=${g##*_c}
      printf 'G %s %s\n' "$gi" "$ci" >> "$out"; cat "$f" >> "$out"; echo E >> "$out"
    done
    [ -s "$out" ] || rm "$out"
  done
done

# Job list: name | certificate file | input | options. The k = 0 full-rerun files are cut into
# quarters by graph index.
Q=36272
for q in 0 1 2; do seq $(((q + 1) * Q)) 145087 > "$O/rf/above_$q.idx"; done
jobs() {
  for j in 0 1 2; do
    for q in 0 1 2 3; do
      sel="--from $((q * Q))"
      [ $q -lt 3 ] && sel="$sel --skip $O/rf/above_$q.idx"
      echo "full_k0_${j}_q$q|$C/full/k0_$j.cert|$I/in_k0_$j.pc|--iso 0 $LP $sel"
    done
  done
  for j in 0 1 2 3 4 5 6 7 8; do echo "full_k1_$j|$C/full/k1_$j.cert|$I/in9_k1_$j.pc|--iso 1 $LP"; done
  echo "full_k2|$C/full/k2.cert|$I/stageA_k2.pc|--iso 2 $LP"
  echo "full_k3|$C/full/k3.cert|$I/stageA_k3.pc|--iso 3 $LP"
  R=$O/rf
  for j in 0 1 2; do echo "pb_k0_$j|$R/pb_k0_$j.rf|$I/in_k0_$j.pc|--iso 0 $LP"; done
  echo "pb_k2|$R/pb_k2.rf|$I/stageA_k2.pc|--iso 2 $LP"
  echo "p1_k1|$R/p1_k1.rf|$I/b_k1.pc|--iso 1 --dlo 53.6578502"
  echo "p1_k2|$R/p1_k2.rf|$I/b_k2.pc|--iso 2 --dlo 53.6578502"
  echo "p1_k3|$R/p1_k3.rf|$I/stageA_k3.pc|--iso 3 --dlo 53.6578502"
  echo "pw_k1|$R/pw_k1.rf|$I/b_k1.pc|--iso 1 --dhi 53.6578502 $LP"
  echo "pw_k2|$R/pw_k2.rf|$I/b_k2.pc|--iso 2 --dhi 53.6578502 $LP"
  echo "p3w_k1|$R/p3w_k1.rf|$I/b_k1.pc|--iso 1 --dhi 53.6578502 --shave 8 $LP"
  echo "p3w_k3|$R/p3w_k3.rf|$I/stageA_k3.pc|--iso 3 --dhi 53.6578502 --shave 8 $LP"
  echo "p2_k1|$R/p2_k1.rf|$I/b_k1.pc|--iso 1 $LP"
  echo "p2_k2|$R/p2_k2.rf|$I/b_k2.pc|--iso 2 $LP"
  echo "p3_k1|$R/p3_k1.rf|$I/b_k1.pc|--iso 1 --shave 8 $LP"
  echo "p3_k2|$R/p3_k2.rf|$I/b_k2.pc|--iso 2 --shave 8 $LP"
  echo "p3_k3|$R/p3_k3.rf|$I/stageA_k3.pc|--iso 3 --shave 8 $LP"
  echo "p4a_k1|$R/p4a_k1.rf|$I/b_k1.pc|--iso 1 --dhi 53.7 --shave 8 $LP"
  echo "p4b_k1|$R/p4b_k1.rf|$I/b_k1.pc|--iso 1 --dlo 53.7 --dhi 54.6 --shave 8 $LP"
  echo "p4c_k1|$R/p4c_k1.rf|$I/b_k1.pc|--iso 1 --dlo 54.6 --shave 8 $LP"
  echo "p5a_k1|$R/p5a_k1.rf|$I/b_k1.pc|--iso 1 --dhi 53.6578502 --shave 8 $LP"
  echo "p5b_k1|$R/p5b_k1.rf|$I/b_k1.pc|--iso 1 --dlo 53.6578502 --dhi 53.66 --shave 8 $LP"
  echo "p5c_k1|$R/p5c_k1.rf|$I/b_k1.pc|--iso 1 --dlo 53.66 --dhi 53.7 --shave 8 $LP"
}
[ -n "${LIST:-}" ] && { jobs; exit 0; }
run() {
  IFS='|' read -r name cert inp opts <<< "$1"
  [ -s "$O/$name.log" ] && grep -q '^replay:' "$O/$name.log" && return 0
  [ -e "$cert" ] || { echo "$name: no certificate file" > "$O/$name.log"; return 0; }
  /usr/bin/time -f "%e %U" -o "$O/$name.time" nice -n 10 $B $opts --replayfile "$cert" \
    < "$inp" 2> "$O/$name.log" | sed 's/ [0-9a-f]\{40,\} / /' > "$O/$name.txt"
}
export -f run; export O B
if [ -n "${ONLY:-}" ]; then
  jobs > "$O/rf/jobs.txt"
  tr '|' '\n' <<< "$ONLY" | while read -r n; do grep "^$n|" "$O/rf/jobs.txt"; done
else jobs; fi | xargs -P "$NPAR" -I{} bash -c 'run "$1"' _ {}
grep -H '^replay:' "$O"/*.log
