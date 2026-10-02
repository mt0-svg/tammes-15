#!/bin/bash
# Face-growth generator runs (src/bin/fg.rs) and their known-answer tests against the plantri route.
# Usage: run.sh N MODE [extra fg gen options]
#   MODE all: every class graph (fg ... --all); w1: the class graphs passing W1;
#        sabotage: w1 with the extra forbidden type (negative control, compared with the w1 reference).
# Writes out/{ref,gen}_{MODE}_n{N}.{txt,codes} and out/cmp_{MODE}_n{N}.txt; a reference that
# exists (ends with its summary line) is reused. One core.
# Env: FG (default target/release/fg, built by cargo build --release in this directory), PLANTRI_MD5 (default
# ../impl1/enum/bin/plantri_md5, built by code/impl1/enum/build_plantri.sh).
set -u
cd "$(dirname "$0")"
N=$1; MODE=$2; shift 2
FG=${FG:-target/release/fg}; PLANTRI_MD5=${PLANTRI_MD5:-../impl1/enum/bin/plantri_md5}
D=out
mkdir -p "$D"
case $MODE in all) OPT=--all; RM=all;; w1) OPT=; RM=w1;; sabotage) OPT=--sabotage; RM=w1;; *) exit 2;; esac
R=$D/ref_${RM}_n$N
if ! grep -q "^fg ref n $N all" "$R.txt" 2>/dev/null; then
  rm -f "$R.txt" "$R.codes"
  { "$PLANTRI_MD5" -p -f6 "$N" 2> "$R.plantri.tmp" | "$FG" ref "$N" "$R.codes" ${OPT/--sabotage/}; } > "$R.txt" || exit 1
  sed 's/[ \t]*$//' "$R.plantri.tmp" > "$R.plantri" && rm "$R.plantri.tmp"
fi
G=$D/gen_${MODE}_n$N${1:+_$(echo "$*" | tr -d ' -')}
rm -f "$G.txt" "$G.codes"
( time "$FG" gen "$N" "$G.codes" $OPT "$@" ) > "$G.txt" 2>&1 || exit 1
C=$D/cmp_${MODE}_n$N${1:+_$(echo "$*" | tr -d ' -')}.txt
{ echo "reference $R.codes: $(wc -l < "$R.codes") codes; generator $G.codes: $(wc -l < "$G.codes") codes"
  echo "only in reference: $(comm -23 "$R.codes" "$G.codes" | wc -l); only in generator: $(comm -13 "$R.codes" "$G.codes" | wc -l)"
  for s in 3 4 5 6; do
    case " $* " in *" --ring "*|*" --ring2 "*) K=expected_ring;; *) K=expected_leaves;; esac
    e=$(grep "^fg ref n $N s $s " "$R.txt" | sed "s/.*$K \([0-9]*\).*/\1/")
    o=$(grep "^fg gen n $N s $s " "$G.txt" | sed 's/.* ok \([0-9]*\) .*/\1/')
    echo "s $s $K ${e:-none} generator_ok_leaves ${o:-none} $([ "$e" = "$o" ] && echo equal || echo DIFFERENT)"
  done
  cmp -s "$R.codes" "$G.codes" && echo "verdict: sets equal" || echo "verdict: sets DIFFERENT"; } > "$C"
cat "$C"
