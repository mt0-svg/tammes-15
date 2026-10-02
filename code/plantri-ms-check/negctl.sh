#!/bin/sh
# Negative controls of check.gp on edited copies of out/n12/part_0of1.txt, each edit kept consistent
# with the part's totals and plantri's count line, so only the cell comparison or a total can catch it:
#   missing: one graph with trivial group removed from F = 15;
#   repeated: one graph with group of order 2 added at F = 13;
#   cancel: at F = 14 two graphs of group order 2 removed and one of trivial group added
#     (-2 * 4E/2 + 4E/1 = 0), an error that cancels inside its cell: the cells stay equal and only
#     the graph total against A000944 catches it;
#   part missing: part 0 of a modulus 2 split alone.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
S=out/n12/part_0of1.txt
ed() { # ed out F a delta [F a delta] ...; total delta = sum of deltas
  o=$1; shift
  awk -v spec="$*" 'BEGIN { n = split(spec, s, " "); for (i = 1; i <= n; i += 3) { d[s[i] " " s[i+1]] = s[i+2]; t += s[i+2] } }
    $1 == "cell" && (($3 " " $4) in d) { $5 += d[$3 " " $4] }
    $1 == "total" { $5 += t }
    $2 == "polytopes" && $3 == "generated;" { $1 += t }
    { print }' "$S" > "$o"
}
ed out/negctl/missing_n12.txt 15 1 -1
ed out/negctl/repeated_n12.txt 13 2 1
ed out/negctl/cancel_n12.txt 14 2 -2 14 1 1
for c in missing repeated cancel; do
  echo "== $c: diff against the real part"; diff "$S" out/negctl/${c}_n12.txt || true
  OUT=out/negctl/check_${c}_n12.out sh check.sh 12 out/negctl/${c}_n12.txt | grep -E ' NO |^cells|^graphs|^class|^CHECK|^END|error'
done
echo "== part missing: part 0 of 2 alone"
OUT=$D/out/negctl/part_0of2_n12.txt sh run.sh 12 0 2
OUT=out/negctl/check_partmissing_n12.out sh check.sh 12 out/negctl/part_0of2_n12.txt | grep -E 'part|error|CHECK|did not'
