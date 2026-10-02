#!/bin/bash
# The whole class (3-connected plane graphs, degrees 3 to 5, faces of 3 to 6 edges) at n = 12 and 13 (Section 6.1 of
# the paper): the second enumerator fg (code/fg, `fg gen N OUT --all ...`) against the plantri route
# (`plantri_md5 -p -f6 N | fg ref N OUT --all`), compared as sets of canonical codes.
# Usage, from the repository root: LISTS=DIR code/d2d3/fullclass.sh RUN, RUN 1 or 2. The two runs differ in the step
# rule of the generator: run 1: --all --ring2 --caps --tight --rule 1; run 2: --all --ring2 --caps --tight (rule 0).
# The plantri route is the same in both runs. One process per side, the two sides in parallel.
# Writes code/d2d3/out/fullclass/run<RUN>/{ref,gen,cmp}_all_n<N>.txt, ref_all_n<N>.plantri and codes.sha256; the
# code lists (sorted, one hex code per line) go to LISTS/fullclass/run<RUN>/.
# Env: FG (default code/fg/target/release/fg), PLANTRI_MD5 (default code/impl1/enum/bin/plantri_md5).
set -u
LISTS=$(realpath -m "${LISTS:?LISTS: a directory for the code lists}")
FG=$(realpath "${FG:-code/fg/target/release/fg}"); PLANTRI_MD5=$(realpath "${PLANTRI_MD5:-code/impl1/enum/bin/plantri_md5}")
cd "$(dirname "$0")"
RUN=$1
case $RUN in 1) V="--ring2 --caps --tight --rule 1";; 2) V="--ring2 --caps --tight";; *) exit 2;; esac
O=out/fullclass/run$RUN
L=$LISTS/fullclass/run$RUN
rm -rf "$O" "$L"; mkdir -p "$O" "$L"
export LC_ALL=C
for N in 12 13; do
  { "$PLANTRI_MD5" -p -f6 "$N" 2> "$O/ref_all_n$N.plantri" | "$FG" ref "$N" "$L/ref_all_n$N.codes" --all; } > "$O/ref_all_n$N.txt" &
  "$FG" gen "$N" "$L/gen_all_n$N.codes" --all $V > "$O/gen_all_n$N.txt" &
  wait
  sed -i 's/[ \t]*$//' "$O/ref_all_n$N.plantri"
  R=$L/ref_all_n$N.codes; G=$L/gen_all_n$N.codes
  {
    echo "generator options: --all $V"
    echo "plantri: $(tail -1 "$O/ref_all_n$N.plantri")"
    echo "reference: $(wc -l < "$R") codes, $(sort -c "$R" 2>&1 && echo sorted), $(uniq -d "$R" | wc -l) repeated"
    echo "generator: $(wc -l < "$G") codes, $(sort -c "$G" 2>&1 && echo sorted), $(uniq -d "$G" | wc -l) repeated"
    echo "only in reference: $(comm -23 "$R" "$G" | wc -l); only in generator: $(comm -13 "$R" "$G" | wc -l)"
    for s in 3 4 5 6; do
      e=$(sed -n "s/^fg ref n $N s $s .* expected_ring \([0-9]*\).*/\1/p" "$O/ref_all_n$N.txt")
      g=$(sed -n "s/^fg gen n $N s $s .* ok \([0-9]*\) .*/\1/p" "$O/gen_all_n$N.txt")
      echo "s $s expected_ring ${e:-none} generator_ok_leaves ${g:-none} $([ -n "$e" ] && [ "$e" = "$g" ] && echo equal || echo DIFFERENT)"
    done
    cmp -s "$R" "$G" && echo "verdict n $N: sets equal" || echo "verdict n $N: sets DIFFERENT"
  } > "$O/cmp_all_n$N.txt"
  cat "$O/cmp_all_n$N.txt"
done
( cd "$L" && sha256sum ref_all_n12.codes gen_all_n12.codes ref_all_n13.codes gen_all_n13.codes ) > "$O/codes.sha256"
cat "$O/codes.sha256"
