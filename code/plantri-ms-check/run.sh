#!/bin/sh
# One part of the run: BIN -p -G -u n res/mod (BIN = build/plantri_ms unless set), output in
# OUT (default out/n<n>/part_<res>of<mod>.txt): the command, the binary's sha256, the plugin's
# cells, plantri's count line and the times, with trailing blanks removed (plantri ends the echo of
# its command line with a blank). A failed part leaves OUT.raw and OUT.tmp, never OUT.
# Usage: sh run.sh n res mod     (FLAGS overrides -pGu, for the negative control without -G)
set -eu
D=$(cd "$(dirname "$0")" && pwd)
n=$1; r=$2; m=$3
BIN=${BIN:-$D/build/plantri_ms}; FLAGS=${FLAGS:--pGu}
OUT=${OUT:-$D/out/n$n/part_${r}of$m.txt}
mkdir -p "$(dirname "$OUT")"
rm -f "$OUT" "$OUT.tmp" "$OUT.raw"
{
  echo "command: $(basename "$BIN") $FLAGS $n $r/$m"
  echo "binary sha256: $(sha256sum "$BIN" | cut -d' ' -f1)"
  echo "start: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$OUT.tmp"
# run from the binary's directory, so that plantri echoes its command line without a home path
( cd "$(dirname "$BIN")" && /usr/bin/time -f "time: wall %e s, user %U s, sys %S s, max rss %M KB" "./$(basename "$BIN")" $FLAGS "$n" "$r/$m" ) > "$OUT.raw" 2>&1
sed 's/[[:space:]]*$//' "$OUT.raw" >> "$OUT.tmp"
rm "$OUT.raw"
echo "end: $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$OUT.tmp"
mv "$OUT.tmp" "$OUT"
