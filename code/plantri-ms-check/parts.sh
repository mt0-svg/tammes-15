#!/bin/sh
# Runs the parts 0..mod-1 of plantri_ms -p -G -u n that are not yet in out/n<n>/, JOBS at a time,
# one core each. Resumable: a finished part is not rerun.
# Usage: sh parts.sh n mod [JOBS]
set -eu
D=$(cd "$(dirname "$0")" && pwd)
export D
n=$1; m=$2; J=${3:-2}
seq 0 $((m - 1)) | xargs -P "$J" -I{} sh -c '[ -s "$D/out/n'"$n"'/part_{}of'"$m"'.txt" ] || sh "$D/run.sh" '"$n"' {} '"$m"
