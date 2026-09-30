#!/bin/bash
# Stage A probe: for each sampled plantri part, one plantri run (plantri_md5 -p -f6 n r/m, kept in a
# temporary file) fed to the frozen vlevel1 twice: with --relsys (rows implied by RelSys) and with
# the default rows (Girard rows on). The --relsys survivors are compared byte for byte with the
# first program's stage-A survivors ($T15/n15full), the default survivors
# with the recorded run of the second program ($T15/stageA2).
# Usage: ./stageA_probe.sh "k:r:m ..."   Output: stageA_probe.out
set -u
cd "$(dirname "$0")"
V=${D3BIN:-${T15:?see README.md}/verify/bin_d3}/vlevel1
W=${T15:?see README.md}/verify/d3check/stageA
N=${T15:?see README.md}/n15full
S=${T15:?see README.md}/stageA2
mkdir -p $W
OUT=stageA_probe.out
echo "# vlevel1 $(sha256sum < $V | cut -c1-16), $(date -u +%FT%TZ), load $(cut -d' ' -f1-3 /proc/loadavg)" >> $OUT
for spec in $1; do
  IFS=: read k r m <<< "$spec"
  n=$((15 - k)); t=$W/k${k}_$r
  /usr/bin/time -f "%U %e" -o $t.ptime plantri_md5 -p -f6 $n $r/$m > $t.raw 2> $t.plantri
  pst=$?
  /usr/bin/time -f "%U %e" -o $t.rtime $V --relsys --iso $k --out $t.rel.pc < $t.raw 2> $t.rel.log
  rst=$?
  /usr/bin/time -f "%U %e" -o $t.dtime $V --iso $k --out $t.def.pc < $t.raw 2> $t.def.log
  dst=$?
  rm -f $t.raw
  cmp -s $t.rel.pc $N/k${k}_$r.pc && a=IDENTICAL || a=DIFFERENT
  cmp -s $t.def.pc $S/k${k}_$r.pc && b=IDENTICAL || b=DIFFERENT
  cnt=$(grep -o "^[0-9]* polytopes" $t.plantri | cut -d' ' -f1)
  echo "k$k part $r/$m: exit plantri $pst relsys $rst default $dst; plantri $cnt graphs, user/wall s $(cat $t.ptime) | relsys: $(tail -n 1 $t.rel.log), user/wall s $(cat $t.rtime), vs first program: $a | default: $(tail -n 1 $t.def.log | cut -d" " -f1-9), user/wall s $(cat $t.dtime), vs recorded: $b" >> $OUT
done
tail -n $(( $(echo $1 | wc -w) + 1 )) $OUT
