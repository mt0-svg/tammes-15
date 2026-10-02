#!/usr/bin/env bash
# High-precision check of the logged transcendental calls (cos, sin, acos, asin, atan, tan) and of the
# constants of iv.rs against Rnd.Sound (Section 9.3 of the paper), with sound-trans.gp in
# PARI/GP. A numerical check, not a proof: PARI's transcendental functions are accurate, not
# certified.
#
#   sound-trans.sh extract N     regenerates the stream of run.sh N (its hash in out/sound-trans-N.sha256,
#                                equal to out/rust-N.sha256), keeps its transcendental calls (lines O 4 to
#                                O 9) and its line P, distinct, with their multiplicities, in
#                                build/trans-N/calls.txt; out/sound-trans-N.extract.txt: the counts
#   sound-trans.sh rate N M      checks a systematic sample of M distinct calls (the lines
#                                floor(iL/M), i = 1 to M, of calls.txt, L its length): out/sound-trans-N.rate-M.txt and its time
#   sound-trans.sh control N M   negative control: the same sample with the lower end of each result
#                                replaced by its upper end (most calls must come out violated)
#   sound-trans.sh check N I K   checks part I of K (lines (I-1)L/K + 1 to IL/K of calls.txt):
#                                out/sound-trans-N.part-I-of-K.txt and its time (.time)
#   sound-trans.sh sum N K       out/sound-trans-N.txt: the sums of the K parts
#
# Each step uses one core. build/ is not committed.
set -euo pipefail
export LC_ALL=C
here=$(cd "$(dirname "$0")" && pwd)
step=${1:?usage: sound-trans.sh extract|rate|check|sum N ...}
N=${2:?N}
out=$here/out
work=$here/build/trans-$N
rust=$here/build/target/release/difftest
gpcheck=$here/sound-trans.gp
calls=$work/calls.txt
mkdir -p "$out" "$work"

# A slice of calls.txt (lines from stdin) as GP input, in chunk files of 10^5 lines under dir $1;
# then the GP commands that read them, and the report, on stdout.
togp() {
  local d=$1
  rm -rf "$d"; mkdir -p "$d"
  sed -E -e 's/^ *([0-9]+) ([4-9]) ([0-9a-f]{16}) ([0-9a-f]{16}) ([0-9a-f]{16}) ([0-9a-f]{16})$/k(\2,0x\3,0x\4,0x\5,0x\6,\1);/' \
    -e 's/^ *1 P ([0-9a-f]{16}) ([0-9a-f]{16}) ([0-9a-f]{16}) ([0-9a-f]{16})$/p(0x\1,0x\2,0x\3,0x\4);/' |
    split -l 100000 -a 4 - "$d/c."
  local bad
  bad=$(cat "$d"/c.* | grep -cvE '^(k|p)\(' || true)
  [ "$bad" = 0 ] || { echo "malformed lines: $bad" >&2; exit 1; }
  for f in "$d"/c.*; do printf 'run("%s");\n' "$f"; done
  printf 'report();\n'
}

runpart() { # name: reads the GP commands on stdin, writes out/sound-trans-N.name.txt and .time
  local name=$1 cmds=$work/$1.cmds
  cat > "$cmds"
  /usr/bin/time -v -o "$out/sound-trans-$N.$name.time" \
    gp -q -D parisizemax=1G "$gpcheck" < "$cmds" > "$out/sound-trans-$N.$name.txt"
  tail -n 9 "$out/sound-trans-$N.$name.txt"
  grep -E 'Elapsed|Maximum resident' "$out/sound-trans-$N.$name.time"
}

case $step in
extract)
  fifo=$(mktemp -u /tmp/difftest-fifo.XXXXXX)
  mkfifo "$fifo"
  trap 'rm -f "$fifo"' EXIT
  sha256sum < "$fifo" | sed 's/-$/rust stream/' > "$out/sound-trans-$N.sha256" &
  hpid=$!
  mkdir -p "$work/tmp"
  "$rust" "$N" 2> /dev/null | tee "$fifo" | grep -E '^(P |O [4-9] )' |
    sed -E 's/^O ([4-9]) ([0-9a-f]{16}) ([0-9a-f]{16}) 0{16} 0{16} ([0-9a-f]{16}) ([0-9a-f]{16})$/\1 \2 \3 \4 \5/' |
    sort -S 1G --parallel=1 -T "$work/tmp" | uniq -c > "$calls"
  wait "$hpid"
  rm -rf "$work/tmp"
  {
    echo "stream $(cut -d' ' -f1 "$out/sound-trans-$N.sha256") (rust-$N.sha256: $(cut -d' ' -f1 "$out/rust-$N.sha256"))"
    echo "distinct lines $(wc -l < "$calls")"
    echo "malformed lines (an O line of op 4 to 9 with a second argument) $(grep -c ' O ' "$calls" || true)"
    awk '$2 != "P" { c[$2] += $1; d[$2]++; t += $1; u++ } $2 == "P" { p++ }
      END { split("cos sin acos asin atan tan", nm, " ");
            for (i = 4; i <= 9; i++) printf "op %s calls %d distinct %d\n", nm[i - 3], c[i], d[i];
            printf "transcendental calls %d distinct %d; P lines %d\n", t, u, p }' "$calls"
  } > "$out/sound-trans-$N.extract.txt"
  cat "$out/sound-trans-$N.extract.txt"
  ;;
rate)
  M=${3:?M}
  L=$(wc -l < "$calls")
  awk -v L="$L" -v M="$M" 'BEGIN { i = 1; nx = int(L / M) } NR == nx && $2 != "P" { print } NR == nx { i++; nx = int(i * L / M) }' "$calls" |
    togp "$work/rate-$M" | runpart "rate-$M"
  ;;
control)
  M=${3:?M}
  L=$(wc -l < "$calls")
  awk -v L="$L" -v M="$M" 'BEGIN { i = 1; nx = int(L / M) } NR == nx && $2 != "P" { $5 = $6; print } NR == nx { i++; nx = int(i * L / M) }' "$calls" |
    togp "$work/control-$M" | runpart "control-$M"
  ;;
check)
  I=${3:?I}; K=${4:?K}
  L=$(wc -l < "$calls")
  from=$(( (I - 1) * L / K + 1 )); to=$(( I * L / K ))
  echo "part $I of $K: lines $from to $to of $L"
  sed -n "${from},${to}p" "$calls" | togp "$work/part-$I" | runpart "part-$I-of-$K"
  rm -rf "$work/part-$I"
  ;;
sum)
  K=${3:?K}
  {
    echo "# the sums of out/sound-trans-$N.part-I-of-$K.txt, I = 1 to $K"
    echo "# op calls contained vacuous violated undecided | distinct contained vacuous violated undecided"
    for i in $(seq 1 "$K"); do cat "$out/sound-trans-$N.part-$i-of-$K.txt"; done |
      awk '$1 == "T" { for (j = 3; j <= 13; j++) if (j != 8) s[$2, j] += $j; ops[$2] = 1 }
        $1 == "NEAR" { nc += $3; nd += $5 }
        $1 == "CONST" { print }
        $1 == "VIOLATED" || $1 == "UNDECIDED" { print }
        END { split("cos sin acos asin atan tan", nm, " ");
              for (i = 1; i <= 6; i++) { o = nm[i]; printf "T %s", o;
                for (j = 3; j <= 13; j++) if (j == 8) printf " |"; else printf " %d", s[o, j]; printf "\n";
                for (j = 3; j <= 7; j++) tt[j] += s[o, j] }
              printf "NEAR calls %d distinct %d\n", nc, nd;
              printf "TOTAL calls %d contained %d vacuous %d violated %d undecided %d\n", tt[3], tt[4], tt[5], tt[6], tt[7] }'
  } > "$out/sound-trans-$N.txt"
  cat "$out/sound-trans-$N.txt"
  ;;
*) echo "unknown step $step" >&2; exit 2 ;;
esac
