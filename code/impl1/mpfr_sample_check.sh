#!/bin/bash
# The samples of the MPFR replays of Section 6.4 (code/impl1/replay_mpfr.sh):
#  - the recorded 5 % run (records/first/replay/k*.txt and .log of the records asset) replayed, in each
#    level-2 input file, exactly the graphs whose index is a multiple of 20 outside the skip list of the
#    graphs set aside (records/first/full), with backend mpfr on the whole d range; its verdicts;
#  - the two random samples (code/impl1/out/mpfr_sample_777.txt, mpfr_sample_31337.txt) are drawn
#    again from the certificate files with the seeds and sizes of replay_mpfr.sh.
# Usage (from the repository root): code/impl1/mpfr_sample_check.sh ASSETS    Exit 0 when all agree.
set -u
A=$(realpath "$1"); R=$A/records/first/replay; F=$A/records/first/full; C=$A/certificates/full
st=0
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
echo "== the 5 % sample: job, graphs of the input, set aside, expected sample, replayed lines equal to it, VERIFIED, other verdicts, d range and backend of the log"
tv=0; to=0
for j in k0_0 k0_1 k0_2 k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k2 k3; do
  case $j in k1_*) s=$F/b_${j}.idx ;; k2) s=$F/skip_k2.idx ;; k3) s=$F/skip_k3.idx ;; *) s=/dev/null ;; esac
  n=$(sed -n 's/.* total \([0-9]*\) .*/\1/p' "$R/$j.log")
  awk -v n="$n" 'NR == FNR {s[$1] = 1; next} END {for (i = 0; i < n; i += 20) if (!(i in s)) print i}' "$s" /dev/null > $W/want
  cut -d' ' -f1 "$R/$j.txt" > $W/got
  if cmp -s $W/want $W/got; then eq=yes; else eq=NO; st=1; fi
  v=$(grep -c ' VERIFIED ' "$R/$j.txt"); o=$(grep -vc ' VERIFIED ' "$R/$j.txt")
  tv=$((tv + v)); to=$((to + o))
  d=$(sed -n 's/^d in \(\[.*\] deg\);.* trig \([a-z]*\)$/\1 \2/p' "$R/$j.log")
  grep -q "^replay: verified $v failed 0 " "$R/$j.log" || { echo "FAIL: $j: the log does not say $v verified and none failed"; st=1; }
  echo "$j $n $(grep -c . "$s") $(wc -l < $W/want) $eq $v $o $d"
done
echo "total: $tv VERIFIED, $to other lines ($(grep -hv ' VERIFIED ' "$R"/k*.txt | awk '{print $6}' | sort | uniq -c | tr -s ' ' | tr '\n' ' '))"
# the random source of shuf: the first 1000000 bytes of `yes SEED`, written to a file (a pipe would
# print "Broken pipe" where SIGPIPE is ignored, since shuf stops reading early)
rnd() { awk -v s="$1" 'BEGIN {l = s "\n"; for (n = 1000000; n >= length(l); n -= length(l)) printf "%s", l; printf "%s", substr(l, 1, n)}'; }
for spec in "777 10 3 5" "31337 200 30 40"; do
  set -- $spec
  rnd "$1" > $W/rnd
  for j in full_k0_0 full_k0_1 full_k0_2 full_k1_0 full_k1_1 full_k1_2 full_k1_3 full_k1_4 full_k1_5 full_k1_6 full_k1_7 full_k1_8 full_k2 full_k3; do
    case $j in full_k0_*) m=$2 ;; full_k1_*) m=$3 ;; full_k2) m=$4 ;; *) m=1 ;; esac
    grep '^G ' "$C/${j#full_}.cert" | awk '{print $2}' | sort -un | shuf -n "$m" --random-source=$W/rnd | sort -n | awk -v j=$j '{print j, $1}'
  done > $W/s
  if grep -v '^#' "code/impl1/out/mpfr_sample_$1.txt" | cmp -s - $W/s; then
    echo "seed $1: the $(wc -l < $W/s) graphs of code/impl1/out/mpfr_sample_$1.txt drawn again, identical"
  else echo "FAIL: seed $1: the sample drawn again differs from code/impl1/out/mpfr_sample_$1.txt"; st=1; fi
done
echo "shuf: $(shuf --version | head -1)"
[ $st = 0 ] && echo "MPFR samples: PASS" || echo "MPFR samples: FAIL"
exit $st
