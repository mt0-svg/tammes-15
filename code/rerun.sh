#!/bin/bash
# Reruns checks of the paper by name and compares each output with the recorded one (code/README.md
# lists them, with the claim each one checks and its running time).
# Usage (from the repository root): code/rerun.sh NAME ...      code/rerun.sh --list prints the names.
# Needs gp (PARI/GP), sage, cargo and a C compiler on the PATH, as the check requires; build first with
# code/rerun.sh build_impl1 build_plantri.
# SAVE=dir (absolute) also writes the complete output of each check to dir/<group>/NAME.txt and a
# tab-separated result line (check, command, time, result, output file) to dir/results/<group>_NAME.tsv.
# Exit status 0 when every check passes.
set -u
cd "$(dirname "$0")/.."
GP="gp -q -D parisizemax=2000000000 -D nbthreads=1"
J=${JOBS:-$(nproc)}

# NAME -> group, directory, command, recorded output (empty: the command checks itself, by its exit
# status), normalisation of the output before the comparison.
spec() {
  case $1 in
    # PARI/GP, in code/gp
    paper_checks)       S=(gp code/gp "gp -q paper_checks.gp" code/gp/paper_checks.out gp) ;;
    rtrig_consts)       S=(gp code/gp "gp -q rtrig_consts.gp" code/gp/rtrig_consts.out gp) ;;
    params)             S=(gp . "sh code/gp/params.sh 5365785/100000 141679/2500" data/params15ft.txt gp) ;;
    bk15_c3_coords)     S=(gp code/gp "gp -q bk15_c3_coords.gp" code/gp/bk15_c3_coords.out gp "data/bk15_c1.txt data/bk15_c3.txt") ;;
    contact_graphs)     S=(gp code/gp "gp -q contact_graphs.gp" code/gp/contact_graphs.out gp) ;;
    # SageMath, from the repository root
    bk15_exact)         S=(sage . "sage code/sage/bk15_exact.sage" code/sage/bk15_exact.out gp data/bk15_exact.txt) ;;
    tie_targets)        S=(sage . "sage code/sage/tie_targets.sage" code/sage/tie_targets.out gp data/tie_targets.txt) ;;
    lean_data)          S=(sage . "code/lean-data/regen.sh" code/lean-data/regen.out regen "code/lean-data/d4_cut.out code/lean-data/d1_lp.out code/lean-data/d1_kernel.out code/lean-data/gen_close.out code/lean-data/witness.out code/lean-data/pi_witness.out code/lean-data/gen_seplt.out code/lean-data/tie_map.out") ;;
    # builds
    build_impl1)        S=(impl1 code/impl1/rust "cargo build --release" "" none) ;;
    build_plantri)      S=(impl1 . "sh code/impl1/enum/build_plantri.sh" "" none) ;;
    # the program (code/impl1): the enumeration and the first level
    stageA_k1)          S=(impl1 . "code/impl1/stageA_check.sh 1 0 39 $J" "" none) ;;
    stageA_k2)          S=(impl1 . "code/impl1/stageA_check.sh 2 0 0" "" none) ;;
    stageA_k3)          S=(impl1 . "code/impl1/stageA_check.sh 3 0 0" "" none) ;;
    stageA_k0_*)        local a=${1#stageA_k0_}; S=(impl1 . "code/impl1/stageA_check.sh 0 $a $((a + 199)) $J" "" none) ;;
    *) return 1 ;;
  esac
}

norm() {
  case $2 in
    gp) grep -v -e 'Warning: .*stack size' "$1" | sed 's/[[:space:]]*$//' ;;
    regen) sed -E '1d; s/^ran in [0-9]+ s/ran in N s/' "$1" ;;
    *) cat "$1" ;;
  esac
}

ALL="paper_checks rtrig_consts params bk15_c3_coords contact_graphs bk15_exact tie_targets lean_data
build_impl1 build_plantri stageA_k1 stageA_k2 stageA_k3 $(seq -f 'stageA_k0_%g' 0 200 1800 | tr '\n' ' ')"
[ "${1:-}" = --list ] && { echo $ALL | tr ' ' '\n'; exit 0; }

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
status=0
for n in "$@"; do
  spec "$n" || { echo "$n: unknown check"; status=1; continue; }
  grp=${S[0]} dir=${S[1]} c=${S[2]} rec=${S[3]} mode=${S[4]} files=${S[5]:-}
  for f in $files; do cp "$f" "$TMP/$(basename "$f").rec"; done
  start=$(date +%s)
  (cd "$dir" && eval "$c") < /dev/null > "$TMP/$n.out" 2>&1
  ex=$?
  secs=$(($(date +%s) - start))
  r=PASS
  if [ -n "$rec" ]; then
    norm "$rec" "$mode" > "$TMP/old"
    norm "$TMP/$n.out" "$mode" > "$TMP/new"
    cmp -s "$TMP/old" "$TMP/new" || { r=FAIL; diff "$TMP/old" "$TMP/new" | head -20; }
    [ $ex = 0 ] || r=FAIL
    for f in $files; do cmp -s "$f" "$TMP/$(basename "$f").rec" || { r=FAIL; echo "$f: regenerated file differs"; }; cp "$TMP/$(basename "$f").rec" "$f"; done
    if [ $r = PASS ]; then r="PASS, identical to $rec${files:+ (and $files)}"; else r="FAIL, different from $rec"; fi
  else
    [ $ex = 0 ] || r=FAIL
    [ $r = PASS ] && r="PASS, exit status 0" || { r="FAIL, exit status $ex"; tail -20 "$TMP/$n.out"; }
  fi
  echo "$n: $r ($secs s)"
  case $r in PASS*) ;; *) status=1 ;; esac
  if [ -n "${SAVE:-}" ]; then
    mkdir -p "$SAVE/$grp" "$SAVE/results"
    cp "$TMP/$n.out" "$SAVE/$grp/$n.txt"
    printf '%s %s\t%s\t%s s\t%s\t%s/%s.txt\n' "$grp" "$n" "$c$([ "$dir" = . ] || echo " (in $dir)")" "$secs" "$r" "$grp" "$n" > "$SAVE/results/${grp}_$n.tsv"
  fi
done
exit $status
