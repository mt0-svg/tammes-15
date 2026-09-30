#!/bin/bash
# Vendor the eight-point Lean code (github.com/lukasliehr/Energy-Minimization-8-Points, commit
# 50d14bc06bd41f61573eb6a36eedb8d00759af8f, directory LeanCode/LargeS/Lean_Code; Kryvonos, Liehr,
# Taylor, arXiv 2609.22077) into Tammes15/Vendor/EM8 as the library VendorEM8:
# the modules reachable from BestPacking, module prefix Lean_Code renamed Tammes15.Vendor.EM8, the
# namespace SquareAntiprismVerification moved under Tammes15.Vendor.EM8 (its `namespace` and `end`
# lines), a credit header on every file, and the port changes below, each marked in its file by a
# line starting with "-- tammes-15 port change".
# Regenerates Tammes15/Vendor/EM8 from a clone of the source (or the directory VENDOR_DST, for a
# comparison); the list of files and changes is THIRD_PARTY.md.
# Run: EM8_SRC=<clone>/LeanCode/LargeS/Lean_Code bash code/vendor/vendor.sh   (no Lean process)
set -eu
SRC=${EM8_SRC:?set EM8_SRC to LeanCode/LargeS/Lean_Code of a clone of the source}
HERE=$(cd "$(dirname "$0")" && pwd)
DST=${VENDOR_DST:-$(cd "$HERE/../.." && pwd)/Tammes15/Vendor/EM8}
FC=$HERE; FIX=$FC/handfix.tsv; KEEP=${VENDOR_KEEP:-$FC/keep8.tsv}
REV=50d14bc06bd41f61573eb6a36eedb8d00759af8f
[ "$(git -C "$SRC" rev-parse HEAD)" = "$REV" ] || { echo "source is not at $REV"; exit 1; }
declare -A seen; pairs=$(mktemp)
visit() { local m=$1; [ -n "${seen[$m]:-}" ] && return; seen[$m]=1
  for d in $(grep -E '^import Lean_Code\.' "$SRC/$m.lean" | sed 's/^import Lean_Code\.//'); do
    echo "$d $m" >> "$pairs"; visit "$d"; done
  echo "$m $m" >> "$pairs"; }
visit BestPacking
order=$(tsort "$pairs"); rm -f "$pairs"
rm -rf "$DST"; mkdir -p "$DST"
# Port changes, by module: the text of the marker line and the option it adds before the first
# `noncomputable section`. Both are the instance search for `ContinuousSMul ℝ ℝ³`, which times out
# at the default synthInstance.maxHeartbeats (20000) on Lean v4.34.1 with Mathlib d13f23b7.
declare -A change
change[SolidAngleDerivative]="instance search for ContinuousSMul ℝ ℝ³ times out at the default limit on Lean v4.34.1"
change[CycleSeparationValue]="instance search for ContinuousSMul ℝ ℝ³ times out at the default limit on Lean v4.34.1 (l.28, l.51 of the source)"
n=0
for m in $order; do
  n=$((n+1)); out="$DST/$m.lean"
  extra=""; [ -n "${change[$m]:-}" ] && extra=" and one option raised (marked below)"
  {
    echo "-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit $REV,"
    echo "-- file LeanCode/LargeS/Lean_Code/$m.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077)."
    echo "-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8$extra; see THIRD_PARTY.md."
    if [ -n "${change[$m]:-}" ]; then
      awk -v msg="${change[$m]}" '
        /^import Lean_Code\./ { sub(/^import Lean_Code\./, "import Tammes15.Vendor.EM8."); print; next }
        /^(namespace|end) SquareAntiprismVerification$/ { sub(/ /, " Tammes15.Vendor.EM8."); print; next }
        !done && /^noncomputable section/ {
          print "-- tammes-15 port change: " msg "."
          print "set_option synthInstance.maxHeartbeats 200000"; done = 1 }
        { print }
        END { if (!done) exit 1 }' "$SRC/$m.lean"
    else
      sed -E 's/^import Lean_Code\./import Tammes15.Vendor.EM8./; s/^(namespace|end) SquareAntiprismVerification$/\1 Tammes15.Vendor.EM8.SquareAntiprismVerification/' "$SRC/$m.lean"
    fi
  } > "$out"
  # THIRD_PARTY.md changes 6 and 7: the listed hand changes (code/vendor/handfix.tsv, each
  # marked in the file), then `Fin 8` generalized to `Fin nPts` outside the declarations listed in
  # code/vendor/keep8.tsv (probe_mix.pl apply); the credit line says which of the two.
  what=""
  if awk -F"\t" -v m="$m" '$1 == m { f = 1 } END { exit !f }' "$FIX"; then
    perl "$FC/handfix.pl" apply "$out" "$m" "$SRC/$m.lean" "$FIX" > "$out.tmp"; mv "$out.tmp" "$out"
    what=", hand changes marked below"; fi
  if [ -z "${VENDOR_NOSUB:-}" ] && grep -q "Fin 8" "$out"; then
    perl "$FC/probe_mix.pl" apply "$out" "$m" "$KEEP" > "$out.tmp"
    cmp -s "$out.tmp" "$out" || what="$what, \`Fin 8\` generalized to \`Fin nPts\` (auto-bound)"
    mv "$out.tmp" "$out"; fi
  if [ -n "$what" ]; then
    sed -i "3s|; see THIRD_PARTY.md.\$|$what; see THIRD_PARTY.md.|" "$out"; fi
done
[ -n "${VENDOR_DST:-}" ] || echo "$order" > "$HERE/vendor_order.txt"
echo "vendored $n modules into $DST (order in code/vendor/vendor_order.txt)"
