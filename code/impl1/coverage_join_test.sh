#!/bin/bash
# Known-answer tests and negative controls of the coverage join (code/impl1/coverage_join.sh):
#  1. the cover test on sets of intervals with known answers (SELFTEST=1);
#  2. the recorded replay with the VERIFIED line of graph 1 removed from full_k1_3.txt and the count
#     of the log lowered by one: FAIL, with survivor k1 #12 (in9_k1_3.pc #1 = stageA_k1.pc #9*1+3)
#     reported without a replay on the whole d range;
#  3. the same line removed, the log as recorded: FAIL on the count of the log;
#  4. the slice [53.6578502, 53.66] of p5b_k1 shrunk to [53.6578502, 53.6599] in its log (the d range
#     line printed by tdeep with --dhi 53.6599) and in the job list: FAIL, with survivor k1 #12507
#     (b_k1.pc #68) reported without a replay on [53.6599, 53.66] deg;
#  5. the recorded replay itself: PASS.
# Each run must also give the exit status of its final line. Usage (from the repository root, after
# building code/impl1/rust): code/impl1/coverage_join_test.sh ASSETS
set -u
A=$(realpath "$1"); R=$A/records/replay-v1
T=code/impl1/rust/target/release/tdeep
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
ok=0; n=0
copy() { # a copy of the recorded replay: links to every file, then real copies of the files to change
  rm -rf "$W/rep"; mkdir "$W/rep"
  for f in "$R"/*; do ln -s "$f" "$W/rep/"; done
  for f in "$@"; do rm "$W/rep/$f"; cp "$R/$f" "$W/rep/$f"; done
}
check() { # name, expected exit status, expected final line, expected lines (grep -F patterns)
  local name=$1 want=$2 last=$3 ex; shift 3
  code/impl1/coverage_join.sh "$A" "$W/rep" > "$W/out" 2>&1; ex=$?
  n=$((n + 1))
  echo "-- $name"
  grep -e '^FAIL' "$W/out"
  tail -1 "$W/out"
  local good=1
  [ $ex = "$want" ] || good=0
  [ "$(tail -1 "$W/out")" = "$last" ] || good=0
  for p in "$@"; do grep -qF -- "$p" "$W/out" || { good=0; echo "missing: $p"; }; done
  if [ $good = 1 ]; then echo "$name: exit status $ex and the expected lines, as expected"; ok=$((ok + 1))
  else echo "$name: NOT as expected (exit status $ex)"; fi
}

echo "== 1. known answers of the cover test"
SELFTEST=1 code/impl1/coverage_join.sh; ex=$?; n=$((n + 1)); [ $ex = 0 ] && ok=$((ok + 1))

echo "== 2. one VERIFIED line removed, log count adjusted"
copy full_k1_3.txt full_k1_3.log
sed -i '/^1 faces=.* VERIFIED /d' "$W/rep/full_k1_3.txt"
sed -i 's/^replay: verified 2992 /replay: verified 2991 /' "$W/rep/full_k1_3.log"
check "line removed" 1 "coverage join: FAIL" \
  "FAIL: survivor k1 #12 (stageA_k1.pc#12 in9_k1_3.pc#1): no VERIFIED replay on [9.36506152041239215e-1, 9.89106012373218602e-1] rad = [53.6578500000, 56.6716000000] deg"

echo "== 3. one VERIFIED line removed, log as recorded"
copy full_k1_3.txt
sed -i '/^1 faces=.* VERIFIED /d' "$W/rep/full_k1_3.txt"
check "line removed, log unchanged" 1 "coverage join: FAIL" \
  "FAIL: full_k1_3: 2991 VERIFIED and 7 NO_CERTIFICATE lines, the log says 2992 and 7"

echo "== 4. the slice of p5b_k1 shrunk"
copy p5b_k1.log
new=$(printf '' | $T data/params15ft.txt --dlo 53.6578502 --dhi 53.6599 2>&1 >/dev/null | sed 's/ deg; .*/ deg;/')
echo "d range printed by tdeep for --dlo 53.6578502 --dhi 53.6599: $new"
sed -i "s|^d in .* deg;|$new|" "$W/rep/p5b_k1.log"
LIST=1 code/impl1/replay_all.sh "$A" "$W/rl" | sed '/^p5b_k1|/s/--dhi 53.66 /--dhi 53.6599 /' > "$W/jobs"
export JOBLIST=$W/jobs; check "slice shrunk" 1 "coverage join: FAIL" \
  "FAIL: survivor k1 #12507 (stageA_k1.pc#12507 b_k1.pc#68 in9_k1_6.pc#1389): no VERIFIED replay on [9.36541931290905461e-1, 9.36543676620156917e-1] rad = [53.6599000000, 53.6600000000] deg"

unset JOBLIST
echo "== 5. the recorded replay"
copy
check "recorded replay" 0 "coverage join: PASS"

echo "coverage join tests: $ok of $n as expected"
[ $ok = $n ]
