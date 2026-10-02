#!/bin/bash
# The programs of the runs of this directory, and their sha256 (out/build.txt): the first program (tdeep) at commit
# 1617e65 of this repository, built from `git archive` of that commit (code/impl1/rust, data/) in WORK, outside the
# checkout, which stays untouched; the second enumerator fg (code/fg) and plantri_md5 (code/impl1/enum).
# Usage, from the repository root: WORK=DIR [FG=...] [PLANTRI_MD5=...] code/d2d3/build.sh (3 cores; the build is
# skipped when the binary exists). Writes code/d2d3/out/build.txt.
set -eu
C=1617e65bf4430c758378ae7d2cb568aa2bca412d
S=${WORK:?WORK: a directory outside the repository}
FG=${FG:-code/fg/target/release/fg}; PLANTRI_MD5=${PLANTRI_MD5:-code/impl1/enum/bin/plantri_md5}
O=code/d2d3/out/build.txt
if [ ! -x "$S/target/release/tdeep" ]; then
  rm -rf "$S/src" "$S/target"; mkdir -p "$S/src"
  git archive "$C" code/impl1/rust data | tar -x -C "$S/src"
  ( cd "$S/src/code/impl1/rust" && CARGO_TARGET_DIR="$S/target" cargo build --release --offline -j 3 -q --bin tdeep )
fi
{
  echo "release commit $C (git archive of code/impl1/rust and data/ into WORK/src)"
  echo "cargo $(cargo --version | cut -d' ' -f2), rustc $(rustc --version | cut -d' ' -f2)"
  ( cd "$S" && sha256sum target/release/tdeep src/data/params15ft.txt src/data/truth/*.pc )
  echo "$(sha256sum < "$FG" | cut -d' ' -f1)  fg"
  echo "$(sha256sum < "$PLANTRI_MD5" | cut -d' ' -f1)  plantri_md5 (PLANTRI_MD5)"
} > "$O"
cat "$O"
