#!/bin/sh
# The realised cases of C1 and C3 (Section 6.6: data/truth/, written by code/impl1/truth.sh: the contact
# graphs with up to 6 edges removed, and with one point turned into a rattler and up to 4 more edges
# removed) searched by vkill without Local (Pair and Edge on, at most 3000 nodes or 5 seconds per
# case). Since each has a genuine realisation at d = psi*, none may be KILLED; the other verdicts
# (UNRESOLVED, BUDGET) depend on the time limit.
# Usage (from the repository root, after building code/impl2): code/impl2/nolocal.sh
# Prints the verdict line of every case and the summary per file. Exit 0 when no case is KILLED.
set -eu
V=code/impl2/target/release/vkill
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
for f in c1_real c3_real c1_realv c3_realv4; do
  case $f in *realv*) iso=1 ;; *) iso=0 ;; esac
  $V data/truth/$f.pc --iso $iso --nodes 3000 --maxsec 5 --pair --edge > "$W/$f.out" 2> "$W/$f.err" &
done
wait
bad=0
for f in c1_real c3_real c1_realv c3_realv4; do
  echo "== $f"; cat "$W/$f.out"; tail -n 1 "$W/$f.err"
  tail -n 1 "$W/$f.err" | grep -q ' killed 0 ' || bad=1
done
[ $bad = 0 ] && echo "no realised case KILLED: PASS" || { echo "a realised case was KILLED: FAIL"; exit 1; }
