#!/usr/bin/env bash
# The exact check of the logged arithmetic against Rnd.Sound (Section 9.3 of the paper).
#
#   sound.sh N [TAG]   N cases per primitive, the same stream as run.sh N; TAG names a rerun
#
# Output: out/sound-NTAG.txt (a FAIL or UNCHECKED line per instance, then the counts per field of
# Rnd.Sound) and out/sound-NTAG.sha256 (the hash of the stream read, equal to out/rust-N.sha256).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
N=${1:?usage: sound.sh N [TAG]}
tag=${2:-}
out=$here/out
mkdir -p "$out"
rust=$here/build/target/release/difftest
check=$here/lean/.lake/build/bin/soundcheck
export LEAN_NUM_THREADS=1
fifo=$(mktemp -u /tmp/difftest-fifo.XXXXXX)
mkfifo "$fifo"
trap 'rm -f "$fifo"' EXIT
sha256sum < "$fifo" | sed 's/-$/rust stream/' > "$out/sound-$N$tag.sha256" &
hpid=$!
"$rust" "$N" 2> /dev/null | tee "$fifo" | "$check" > "$out/sound-$N$tag.txt"
wait "$hpid"
grep -E '^(FAILS|NOTCHECKED)' "$out/sound-$N$tag.txt"
