#!/bin/bash
# The build of this directory against the recorded runs: builds fg here, reruns kat.sh in a temporary copy, and
# compares its comparison files, its log and the sha256 of its code lists with out/ (the recorded runs used builds
# made in the development repository, whose sha256 differ from that of this build; README of code/).
# Usage, from the repository root: bash code/fg/rebuild_check.sh > code/fg/out/rebuild_check.txt (one core, minutes)
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
( cd "$here" && CARGO_TARGET_DIR="$t/target" cargo build --release --offline -j 1 -q --bin fg ) || exit 1
echo "build: $(sha256sum < "$t/target/release/fg" | cut -d' ' -f1)  fg ($(rustc --version))"
mkdir -p "$t/run/out" && cp "$here/run.sh" "$here/kat.sh" "$t/run/"
( cd "$t/run" && FG="$t/target/release/fg" PLANTRI_MD5="$root/code/impl1/enum/bin/plantri_md5" bash kat.sh > kat.log 2>&1 )
n=0; d=0
for f in "$t"/run/out/cmp_*.txt; do n=$((n + 1)); cmp -s "$f" "$here/out/$(basename "$f")" || { d=$((d + 1)); echo "differs: $(basename "$f")"; }; done
echo "comparison files: $n, of them different from out/: $d"
k=$(wc -l < "$t/run/kat.log")
head -n "$k" "$here/out/kat.log" | cmp -s - "$t/run/kat.log" && s=identical || s=DIFFERENT
echo "kat.log: $k lines, $s to the first $k lines of out/kat.log (which goes on with the runs of n14.sh)"
( cd "$t/run/out" && sha256sum *.codes ) | sort -k2 > "$t/new.sha256"
m=$(join -1 2 -2 2 "$t/new.sha256" <(sort -k2 "$here/out/codes.sha256") | awk '$2 != $3 {d++} END {print NR " code lists in both, " d + 0 " with a different sha256"}')
echo "code lists: $m"
[ "$d" = 0 ] && [ "$s" = identical ] && echo "REBUILD CHECK: PASS" || echo "REBUILD CHECK: FAIL"
