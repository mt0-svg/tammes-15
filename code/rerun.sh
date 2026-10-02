#!/bin/bash
# Reruns checks of the paper by name and compares each output with the recorded one (code/README.md
# lists them, with the claim each one checks and its running time).
# Usage (from the repository root): code/rerun.sh NAME ...      code/rerun.sh --list prints the names.
# Needs gp (PARI/GP), sage, cargo and a C compiler on the PATH, as the check requires; build first with
# code/rerun.sh build_impl1 build_impl2 build_plantri.
# SAVE=dir (absolute) also writes the complete output of each check to dir/<group>/NAME.txt and a
# tab-separated result line (check, command, time, result, output file) to dir/results/<group>_NAME.tsv.
# The checks of the group assets read the unpacked release assets (ASSETS.md) from the absolute path
# ASSETS=dir (code/impl1/fetch_assets.sh dir).
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
    consts_check)       S=(gp code/impl2 "gp -q consts_check.gp" code/impl2/consts_check.out gp) ;;
    # SageMath, from the repository root
    bk15_exact)         S=(sage . "sage code/sage/bk15_exact.sage" code/sage/bk15_exact.out gp data/bk15_exact.txt) ;;
    params_check)       S=(sage . "sage code/sage/params_check.sage" code/sage/params_check.out gp) ;;
    tie_targets)        S=(sage . "sage code/sage/tie_targets.sage" code/sage/tie_targets.out gp data/tie_targets.txt) ;;
    lean_data)          S=(sage . "code/lean-data/regen.sh" code/lean-data/regen.out regen "code/lean-data/d4_cut.out code/lean-data/d1_lp.out code/lean-data/d1_kernel.out code/lean-data/gen_close.out code/lean-data/gen34.out code/lean-data/witness.out code/lean-data/pi_witness.out code/lean-data/gen_seplt.out code/lean-data/tie_map.out") ;;
    exactlp_k3)         S=(sage . "sh code/sage/stageA_exactlp.sh 3 0 1 data/stageA/stageA_k3.pc 3000 13" code/sage/exactlp_k3.out gp) ;;
    exactlp_k2)         S=(sage . "sh code/sage/stageA_exactlp.sh 2 0 1 data/stageA/stageA_k2.pc 2000 22" code/sage/exactlp_k2.out gp) ;;
    exactlp_k1_15)      S=(sage . "sh code/sage/stageA_exactlp.sh 1 15 40 data/stageA/k1_15.pc 2000 21" code/sage/exactlp_k1_15.out gp) ;;
    exactlp_k0_135)     S=(sage . "sh code/sage/stageA_exactlp.sh 0 135 2000 data/stageA/k0_135.pc 3000 11" code/sage/exactlp_k0_135.out gp) ;;
    exactlp_k0_1848)    S=(sage . "sh code/sage/stageA_exactlp.sh 0 1848 2000 data/stageA/k0_1848.pc 3000 12" code/sage/exactlp_k0_1848.out gp) ;;
    # builds
    build_impl1)        S=(impl1 code/impl1/rust "cargo build --release" "" none) ;;
    build_impl2)        S=(impl2 code/impl2 "cargo build --release" "" none) ;;
    build_plantri)      S=(impl1 . "sh code/impl1/enum/build_plantri.sh" "" none) ;;
    # the first implementation (code/impl1): unit tests, replays, enumeration, stage A
    test_impl1)         S=(impl1 code/impl1/rust "cargo test --release" "" none) ;;
    replay_sample)      S=(impl1 . "code/impl1/replay_sample.sh" code/impl1/out/replay_sample.txt tdeep) ;;
    replay_corrupt)     S=(impl1 . "code/impl1/replay_corrupt.sh" "" none) ;;
    localtest)          S=(impl1 . "sh -c 'cd code/impl1/localtest && cargo build --release -q && target/release/localtest ../../..'" code/impl1/out/localtest.txt none) ;;
    filtercheck_n4_13)  S=(impl1 . "sh -c 'for n in 4 5 6 7 8 9 10 11 12 13; do code/impl1/enum/filtercheck.sh \$n 4 $J; done'" code/impl1/out/filtercheck_n4_13.txt none) ;;
    unfiltered_n13)     S=(impl1 . "code/impl1/enum/count.sh plantri 13 1" code/impl1/out/unfiltered_n13.txt none) ;;
    unfiltered_n14)     S=(impl1 . "code/impl1/enum/count.sh plantri 14 4 $J" code/impl1/out/unfiltered_n14.txt none) ;;
    split_n14)          S=(impl1 . "code/impl1/enum/count.sh plantri_md5 14 1" code/impl1/out/split_n14.txt none) ;;
    stageA_k1)          S=(impl1 . "env VLEVEL1=1 code/impl1/stageA_check.sh 1 0 39 $J" "" none) ;;
    stageA_k2)          S=(impl1 . "env VLEVEL1=1 code/impl1/stageA_check.sh 2 0 0" "" none) ;;
    stageA_k3)          S=(impl1 . "env VLEVEL1=1 code/impl1/stageA_check.sh 3 0 0" "" none) ;;
    stageA_k0_*)        local a=${1#stageA_k0_}; S=(impl1 . "env VLEVEL1=1 code/impl1/stageA_check.sh 0 $a $((a + 199)) $J" "" none) ;;
    # the second implementation (code/impl2)
    test_impl2)         S=(impl2 code/impl2 "cargo test --release" "" none) ;;
    sample_kill)        S=(impl2 . "code/impl2/sample_kill.sh" code/impl2/out/sample_kill.txt vkill) ;;
    residue_*)          local g=${1#residue_}; S=(impl2 . "env JOBS=$J code/impl2/residue_rerun.sh $(residue_group "$g")" "" none) ;;
    # on the release assets (ASSETS=dir)
    coverage_join)      S=(assets . "code/impl1/coverage_join.sh \"\${ASSETS:?}\"" code/impl1/out/coverage_join.txt none) ;;
    coverage_join_test) S=(assets . "code/impl1/coverage_join_test.sh \"\${ASSETS:?}\"" code/impl1/out/coverage_join_test.txt none) ;;
    stageA_compare)     S=(assets . "code/impl2/stageA_compare.sh \"\${ASSETS:?}\"" code/impl2/out/stageA_compare.txt none) ;;
    mpfr_samples)       S=(assets . "code/impl1/mpfr_sample_check.sh \"\${ASSETS:?}\"" code/impl1/out/mpfr_sample_check.txt none) ;;
    mpfr_974)           S=(assets . "sh -c 'd=\$(mktemp -d); code/impl1/replay_mpfr.sh \"\${ASSETS:?}\" \"\$d\" samples; s=\$?; rm -rf \"\$d\"; exit \$s'" code/impl1/out/replay_mpfr_974.txt tdeep) ;;
    *) return 1 ;;
  esac
}

# The runs of code/impl2/residue_cases.txt in five groups of about 2000 s of work on one core each.
residue_group() {
  case $1 in
    a) echo k1_1 k1_50 k1_55_res_d2 k2_1 k2_3 k2_30 k2_13 k2_26 k2_41 k3_2 ;;
    b) echo k0_0_121092 k0_2_35779 k1_36 k1_56 k1_68_r68_a_w k1_68_r68_s3w k1_76 k1_77_res_d0 k1_104 k3_0 ;;
    c) echo k1_8 k1_51 k1_68_res_d2 k1_68_res_d1 k1_68_r68_s1w k1_68_r68_s4w k1_83 k2_0 k2_4 k2_33 k2_15 ;;
    d) echo k0_0_7421 k1_9 k1_15 k1_28 k1_44 k1_55_res_d0 k1_95 k2_11 k2_35 k3_1 ;;
    e) echo k0_0_43064 k1_53 k1_55_res_d1 k1_68_r68_s2w k1_68_r68_s5 k1_68_r68_s6 k1_77_res_d2 k1_77_res_d1 k1_89 k1_102 k2_31 k2_34 k3_4 ;;
  esac
}

norm() {
  case $2 in
    gp) grep -v -e 'Warning: .*stack size' "$1" | sed 's/[[:space:]]*$//' ;;
    tdeep) sed -E 's/ t=[0-9.]+$//; s/ time [0-9.]+s \([0-9.]+ s\/graph\)//' "$1" ;;
    regen) sed -E '1d; s/^ran in [0-9]+ s/ran in N s/' "$1" ;;
    vkill) sed -E 's/^([0-9]+ [A-Z]+ [0-9]+ [0-9]+) [0-9.]+ /\1 /; s/ time [0-9.]+ s$//' "$1" ;;
    *) cat "$1" ;;
  esac
}

ALL="paper_checks rtrig_consts params bk15_c3_coords contact_graphs consts_check bk15_exact params_check tie_targets lean_data
exactlp_k3 exactlp_k2 exactlp_k1_15 exactlp_k0_135 exactlp_k0_1848 build_impl1 build_impl2 build_plantri
test_impl1 replay_sample replay_corrupt localtest filtercheck_n4_13 unfiltered_n13 unfiltered_n14 split_n14
stageA_k1 stageA_k2 stageA_k3 $(seq -f 'stageA_k0_%g' 0 200 1800 | tr '\n' ' ') test_impl2 sample_kill
residue_a residue_b residue_c residue_d residue_e
coverage_join coverage_join_test stageA_compare mpfr_samples mpfr_974"
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
