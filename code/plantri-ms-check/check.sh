#!/bin/sh
# Compares the parts of out/n<n>/ (or the files given) with the formula; writes out/check_n<n>.out
# unless OUT is set. Expected totals: A000944(n), and the class counts of the enumeration
# (code/impl1/out/filtercheck_n4_13.txt, filtercheck_n14.txt, filtercheck_n15.txt, n = 8..15).
# Usage: sh check.sh n [files...]
set -eu
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
n=$1; shift
if [ $# -gt 0 ]; then FILES="$*"; else FILES=$(ls out/n$n/part_*.txt); fi
OUT=${OUT:-out/check_n$n.out}
G=$(echo "4 1|5 2|6 7|7 34|8 257|9 2606|10 32300|11 440564|12 6384634|13 96262938|14 1496225352|15 23833988129" | tr '|' '\n' | awk -v n=$n '$1 == n {print $2}')
C=$(echo "8 151|9 1006|10 8150|11 68728|12 606838|13 5447863|14 49661857|15 457548213" | tr '|' '\n' | awk -v n=$n '$1 == n {print $2}')
rm -f "$OUT"
MS_N=$n MS_FILES=$(echo $FILES) MS_GRAPHS=$G MS_CLASS=$C \
  gp -f -q -D parisizemax=1000000000 -D nbthreads=1 check.gp < /dev/null > "$OUT" 2>&1 || true
if grep -q "\*\*\*" "$OUT" || ! grep -q "^END$" "$OUT"; then echo "CHECK FAIL: gp error or check.gp did not reach its end" >> "$OUT"; fi
cat "$OUT"
