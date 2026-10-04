#!/bin/bash
# measure.sh NAME LOG CMD...: run CMD in a transient systemd user scope, its output to LOG, and append one line to
# $MEASURE_TSV (default measure.tsv): NAME, exit status, wall s, user and system CPU s of CMD and its children,
# the largest resident set of one process (KB), the peak memory charge of the scope (all its processes, bytes), and
# the peak of MemTotal - MemAvailable of the machine sampled every 2 s (bytes). Exits with CMD's status.
set -u
name=$1; log=$2; shift 2
tsv=${MEASURE_TSV:-measure.tsv}
t=$(mktemp -d)
( m=0; while :; do
    u=$(awk '/^MemTotal:/ {a = $2} /^MemAvailable:/ {b = $2} END {print (a - b) * 1024}' /proc/meminfo)
    [ "$u" -gt "$m" ] && m=$u && echo "$m" > "$t/sys"; sleep 2; done ) &
sp=$!
rc=0
systemd-run --user --scope --quiet --expand-environment=no -p MemoryAccounting=yes -- \
  /usr/bin/time -o "$t/time" -f '%e %U %S %M' bash "$(dirname "$0")/measure-inner.sh" "$t/peak" "$@" > "$log" 2>&1 || rc=$?
kill "$sp" 2> /dev/null; wait "$sp" 2> /dev/null
read -r wall user sys rss < <(tail -n 1 "$t/time" 2> /dev/null) || { wall=NA; user=NA; sys=NA; rss=NA; }
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$rc" "$wall" "$user" "$sys" "$rss" \
  "$(cat "$t/peak" 2> /dev/null || echo NA)" "$(cat "$t/sys" 2> /dev/null || echo NA)" >> "$tsv"
rm -rf "$t"
exit "$rc"
