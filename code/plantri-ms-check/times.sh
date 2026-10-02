#!/bin/sh
# Times of the recorded parts: per n, the number of parts, the core time (user + sys summed over
# the parts), the longest part, and the span from the first start to the last end. Writes out/times.txt.
set -eu
cd "$(dirname "$0")"
for d in out/n[0-9]*/; do
  n=$(basename "$d" | tr -d n)
  awk -v n="$n" '
    /^start:/ { s = $2; if (first == "" || s < first) first = s }
    /^end:/ { e = $2; if (e > last) last = e }
    /^time:/ { w = $3; u = $6; y = $9; core += u + y; np++; if (w + 0 > maxw) maxw = w + 0 }
    END { printf "n = %s: %d parts, core %.1f s, longest part %.1f s wall, %s to %s\n", n, np, core, maxw, first, last }' "$d"part_*.txt
done | sort -t' ' -k3,3n > out/times.txt
cat out/times.txt
