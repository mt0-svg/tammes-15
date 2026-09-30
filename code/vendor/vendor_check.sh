#!/bin/bash
# Compare every vendored file Tammes15/Vendor/EM8/<M>.lean with its source
# LeanCode/LargeS/Lean_Code/<M>.lean at commit 50d14bc, undoing each step of vendor.sh in reverse:
# `Fin nPts` back to `Fin 8` (the source has no `nPts`), the hand changes of
# code/vendor/handfix.tsv (handfix.pl undo: each marker line with its new lines back to
# the old line), the three header lines, the import renaming Tammes15.Vendor.EM8 -> Lean_Code and
# the namespace renaming (the lines `namespace` and `end` of
# Tammes15.Vendor.EM8.SquareAntiprismVerification back to SquareAntiprismVerification); then diff.
# Prints each file with a difference and the differing lines; the expected output is the two marked
# option lines of THIRD_PARTY.md in SolidAngleDerivative and CycleSeparationValue, nothing else.
# Run: EM8_SRC=<clone>/LeanCode/LargeS/Lean_Code bash code/vendor/vendor_check.sh > code/vendor/vendor_check.out
set -u
SRC=${EM8_SRC:?set EM8_SRC to LeanCode/LargeS/Lean_Code of a clone of the source}
HERE=$(cd "$(dirname "$0")" && pwd)
DST=${VENDOR_DST:-$HERE/../../Tammes15/Vendor/EM8}
FC=$HERE; FIX=$FC/handfix.tsv
REV=50d14bc06bd41f61573eb6a36eedb8d00759af8f
[ "$(git -C "$SRC" rev-parse HEAD)" = "$REV" ] || { echo "source is not at $REV"; exit 1; }
echo "# source: LeanCode/LargeS/Lean_Code at commit $REV"
n=0; nd=0; nns=0; ngen=0; nfin=0; nfix=0
if grep -l 'nPts' "$SRC"/*.lean > /dev/null 2>&1; then echo "the source mentions nPts: the check does not apply"; exit 1; fi
for m in $(cat "$HERE/vendor_order.txt"); do
  n=$((n+1))
  nns=$((nns + $(grep -cE '^(namespace|end) Tammes15\.Vendor\.EM8\.SquareAntiprismVerification$' "$DST/$m.lean")))
  k=$(tail -n +4 "$DST/$m.lean" | grep -o '\bFin nPts\b' | wc -l); [ "$k" -gt 0 ] && ngen=$((ngen+1)); nfin=$((nfin+k))
  back=$(mktemp); sed 's/\bFin nPts\b/Fin 8/g' "$DST/$m.lean" > "$back"
  if awk -F'\t' -v m="$m" '$1 == m { f = 1 } END { exit !f }' "$FIX"; then
    nfix=$((nfix + $(awk -F'\t' -v m="$m" '$1 == m' "$FIX" | wc -l)))
    if perl "$FC/handfix.pl" undo "$back" "$m" "$FIX" > "$back.u" 2> "$back.e"; then mv "$back.u" "$back"
    else echo "== $m: hand changes do not undo: $(cat "$back.e")"; nd=$((nd+1)); rm -f "$back.u"; fi
    rm -f "$back.e"; fi
  out=$(diff <(sed -E '1,3d; s/^import Tammes15\.Vendor\.EM8\./import Lean_Code./; s/^(namespace|end) Tammes15\.Vendor\.EM8\.SquareAntiprismVerification$/\1 SquareAntiprismVerification/' "$back") "$SRC/$m.lean")
  rm -f "$back"
  if [ -n "$out" ]; then nd=$((nd+1)); echo "== $m"; echo "$out"; fi
done
extra=$(ls "$DST" | sed 's/\.lean$//' | sort | comm -23 - <(sort "$HERE/vendor_order.txt"))
echo "files compared: $n; with differences: $nd; namespace and end lines renamed: $nns; files in Vendor/EM8 not in the order list: ${extra:-none}"
echo "generalized files: $ngen, \`Fin nPts\` occurrences: $nfin; hand changes undone: $nfix (rows of handfix.tsv)"
