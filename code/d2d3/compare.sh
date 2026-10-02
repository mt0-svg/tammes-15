#!/bin/bash
# Agreement of the two runs of each item of this directory.
# Usage, from the repository root: code/d2d3/compare.sh fullclass | w1n15. Times, node counts of the generator (its two runs use
# different step rules) and option lines are removed; every other line must be identical.
# Writes out/<item>/compare.txt and exits 1 on any difference.
set -u
cd "$(dirname "$0")"
I=$1
case $I in fullclass) A=1; B=2;; w1n15) A=A; B=B;; *) exit 2;; esac
X=out/$I/run$A; Y=out/$I/run$B
st=0
same() { # label, two streams as files
  if cmp -s "$2" "$3"; then echo "$1: identical ($(wc -l < "$2") lines)"; else echo "$1: DIFFERENT"; diff "$2" "$3" | head -20; st=1; fi
}
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
{
  case $I in
  fullclass)
    same "sha256 of the four code lists" "$X/codes.sha256" "$Y/codes.sha256"
    for N in 12 13; do
      sed 's/ secs [0-9.]*//' "$X/ref_all_n$N.txt" > "$t/a"; sed 's/ secs [0-9.]*//' "$Y/ref_all_n$N.txt" > "$t/b"
      same "n $N plantri route (fg ref lines, times removed)" "$t/a" "$t/b"
      sed 's/cpu=[0-9.]* sec//' "$X/ref_all_n$N.plantri" > "$t/a"; sed 's/cpu=[0-9.]* sec//' "$Y/ref_all_n$N.plantri" > "$t/b"
      same "n $N plantri count" "$t/a" "$t/b"
      grep -v "^generator options\|^plantri:" "$X/cmp_all_n$N.txt" > "$t/a"; grep -v "^generator options\|^plantri:" "$Y/cmp_all_n$N.txt" > "$t/b"
      same "n $N comparison (counts, leaf counts per seed size, verdict)" "$t/a" "$t/b"
      for R in $A $B; do echo "n $N run $R generator: $(grep '^fg gen n [0-9]* all' "out/$I/run$R/gen_all_n$N.txt" | sed 's/.* nodes \([0-9]*\) .* secs \([0-9.]*\)/nodes \1 secs \2/')"; done
    done ;;
  w1n15)
    same "sha256 of the merged plantri-route list and the generator list" "$X/codes.sha256" "$Y/codes.sha256"
    sed -n '2,$p' "$X/cmp.txt" | sed 's/; plantri cpu .*//; s/: [0-9]* parts,/:/' > "$t/a"
    sed -n '2,$p' "$Y/cmp.txt" | sed 's/; plantri cpu .*//; s/: [0-9]* parts,/:/' > "$t/b"
    same "totals, classes and leaf counts per seed size, verdict" "$t/a" "$t/b"
    for R in $A $B; do echo "run $R: $(sed -n 2p "out/$I/run$R/cmp.txt" | sed 's/.*; plantri cpu/plantri cpu/'); generator $(grep '^fg gen n 15 all' "out/$I/run$R/gen.txt" | sed 's/.* nodes \([0-9]*\) .* secs \([0-9.]*\)/nodes \1 secs \2/')"; done ;;
  esac
  [ $st = 0 ] && echo "runs $A and $B agree" || echo "runs $A and $B DISAGREE"
} > "out/$I/compare.txt"
cat "out/$I/compare.txt"
exit $st
