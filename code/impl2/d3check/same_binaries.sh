#!/bin/bash
# The binaries of the recorded runs were built from sources that differ from code/impl2 in comments
# and in the default path of the targets file of vkill and vtest (every run passes --targets). This
# script builds code/impl2 with that default path put back and compares the sha256 of the three
# binaries with those of the recorded runs.
# Usage: ./same_binaries.sh   Output: same_binaries.out
set -eu
cd "$(dirname "$0")"
S=$(cd .. && pwd)
F=$(mktemp -d); trap 'rm -rf "$F"' EXIT
declare -A rec=([vkill]=a518bbb9af0f183f48fef8907e9136bbc68a530c60d8d1178a3bb6da61d309a5
  [vlevel1]=080b6d6dbca7a878c4a8047f56368e62e4641470a7b8848cd80883be8127ed9b
  [vtest]=3130163e74819a0aae6e263d4a7f69156c16b25902af0f11f7f7be6d77bfd12a)
{
  (cd "$S" && tar -c src Cargo.toml Cargo.lock build.rs) | tar -x -C "$F"
  for f in src/bin/vkill.rs src/bin/vtest.rs; do
    n=$(grep -c 'String::from("../../data/tie_targets.txt")' "$F/$f")
    sed -i 's|String::from("../../data/tie_targets.txt")|String::from("../../local/impl1/tie_targets.txt")|' "$F/$f"
    echo "$f: $n default path put back"
  done
  (cd "$F" && cargo build --release --target-dir "$F/target" 2>&1 | tail -n 1)
  ok=1
  for b in vkill vlevel1 vtest; do
    x=$(sha256sum < "$F/target/release/$b" | cut -c1-64)
    echo "$b $x recorded ${rec[$b]} $([ "$x" = "${rec[$b]}" ] && echo SAME || echo DIFFERENT)"
    [ "$x" = "${rec[$b]}" ] || ok=0
  done
  [ $ok = 1 ] && echo "SAME BINARIES" || echo "DIFFERENT BINARIES"
} > same_binaries.out 2>&1
cat same_binaries.out
