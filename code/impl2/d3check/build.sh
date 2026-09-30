#!/bin/bash
# The binaries of the d3check runs: vkill, vlevel1 and vtest of code/impl2, built twice (cargo build
# --release) from two copies of the source with two target directories, sha256 compared, the first
# build copied to D3BIN (default $T15/verify/bin_d3).
# Usage: ./build.sh   Output: build.out
set -eu
cd "$(dirname "$0")"
OUT=$(pwd)/build.out
S=$(cd .. && pwd)
B=${D3BIN:-${T15:?see README.md}/verify/bin_d3}
F=$(mktemp -d); trap 'rm -rf "$F"' EXIT
{
  echo "source: code/impl2/{src,Cargo.toml,Cargo.lock,build.rs}, sha256 $(cd "$S" && find src Cargo.toml Cargo.lock build.rs -type f | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-16)"
  cargo --version; rustc --version
  for s in a b; do
    mkdir -p "$F/src_$s"
    (cd "$S" && tar -c src Cargo.toml Cargo.lock build.rs) | tar -x -C "$F/src_$s"
    (cd "$F/src_$s" && cargo build --release --target-dir "$F/target_$s" 2>&1 | tail -n 1)
  done
  ok=1
  for b in vkill vlevel1 vtest; do
    x=$(sha256sum < "$F/target_a/release/$b" | cut -c1-64); y=$(sha256sum < "$F/target_b/release/$b" | cut -c1-64)
    echo "$b build a $x build b $y $([ "$x" = "$y" ] && echo EQUAL || echo DIFFERENT)"
    [ "$x" = "$y" ] || ok=0
  done
  [ $ok = 1 ]
  mkdir -p "$B"
  for b in vkill vlevel1 vtest; do cp "$F/target_a/release/$b" "$B/$b"; done
  (cd "$B" && sha256sum vkill vlevel1 vtest)
} > "$OUT" 2>&1
cat "$OUT"
