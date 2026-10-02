#!/bin/bash
# The replay of every tree by the program of this repository, whose deep.rs carries the two guards of
# code/impl1/deep-guards.patch (Sections 5.5, 6.4 and 10.4 of the paper), against the recorded replay of the program
# as first published (code/impl1/out/replay_summary.txt, code/impl1/out/coverage_join.txt). code/impl1/out/guarded/
# holds the outputs of the 45 jobs of code/impl1/replay_all.sh (jobs/), their table (replay_summary.txt, by
# code/impl1/replay_summary.sh on jobs/), their coverage join (coverage_join.txt, by code/impl1/coverage_join.sh on
# jobs/) and the sha256 of the binaries (tdeep.sha256). 37 jobs ran on a workstation; the other 8 were run again later
# by the same program from this repository (code/README.md). Checks:
#  1. the 45 job outputs of jobs/ give the 45 lines of the table (replay_summary.sh on jobs/);
#  2. the table has the 45 jobs of the record, with the same verified, failed and missing counts (the times differ);
#  3. the coverage join is the recorded one, but for its first line, which names the directory of the records.
# Usage, from the repository root: bash code/impl1/guarded_compare.sh > code/impl1/out/guarded/compare.out
set -u
G=code/impl1/out/guarded; R=code/impl1/out
fail=0
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
mkdir "$t/jobs"
for f in "$G"/jobs/*.log; do n=$(basename "$f" .log); cp "$f" "$G/jobs/$n.time" "$t/jobs/"; done
sh code/impl1/replay_summary.sh "$t/jobs" | sed '1d;$d' > "$t/sub"
nj=$(wc -l < "$t/sub")
if grep -vxF -f "$G/replay_summary.txt" "$t/sub" > "$t/bad"; then
  echo "1. FAIL: $(wc -l < "$t/bad") of the $nj job lines differ from the table:"; cat "$t/bad"; fail=1
else echo "1. PASS: the $nj job outputs of jobs/ give their $nj lines of the table"; fi
cols() { sed '1d;$d' "$1" | awk '{print $1, $2, $3, $4}'; }
tot() { tail -1 "$1" | awk '{print $2, $3}'; }
njobs=$(sed '1d;$d' "$G/replay_summary.txt" | wc -l)
if [ "$(cols "$G/replay_summary.txt")" = "$(cols "$R/replay_summary.txt")" ] && [ "$(tot "$G/replay_summary.txt")" = "$(tot "$R/replay_summary.txt")" ]; then
  echo "2. PASS: $njobs jobs, the same verified, failed and missing counts as the record in every job; total verified $(tot "$G/replay_summary.txt" | cut -d' ' -f1), failed $(tot "$G/replay_summary.txt" | cut -d' ' -f2)"
else echo "2. FAIL: the counts differ from the record:"; diff <(cols "$R/replay_summary.txt") <(cols "$G/replay_summary.txt"); fail=1; fi
if [ "$(sed 1d "$G/coverage_join.txt")" = "$(sed 1d "$R/coverage_join.txt")" ]; then
  echo "3. PASS: the coverage join equals the recorded one in its $(($(wc -l < "$R/coverage_join.txt") - 1)) lines after the first"
  echo "   first line here:   $(head -1 "$G/coverage_join.txt")"
  echo "   first line record: $(head -1 "$R/coverage_join.txt")"
  echo "   last line: $(tail -1 "$G/coverage_join.txt")"
else echo "3. FAIL: the coverage join differs from the record"; fail=1; fi
echo "binaries:"; sed "s/^/   /" "$G/tdeep.sha256"; echo "patch: $(sha256sum code/impl1/deep-guards.patch)"
[ $fail = 0 ] && echo "GUARDED REPLAY: PASS" || echo "GUARDED REPLAY: FAIL"
exit $fail
