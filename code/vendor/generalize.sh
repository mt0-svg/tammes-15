#!/bin/bash
# The keep list of the generalization of the vendored eight-point code (code/vendor/keep8.tsv):
# the declarations that stay at `Fin 8` when code/vendor/vendor.sh turns every other `Fin 8` into
# `Fin nPts`. On all 140 modules, in a copy outside the package (directory GEN_DIR, default a new
# temporary directory), made by vendor.sh (renaming, the two option lines, the
# hand changes of handfix.tsv) before the generalization, each module in import order is built
# with the `Fin nPts` form of every declaration except the ones kept so far; a declaration with
# an error is kept (and, when only kept declarations fail, the declarations of the module their
# errors name), and the module is rebuilt, until it compiles. The kept set starts from INIT (a
# keep list; default the previous keep8.tsv when it exists), so a rerun after a change of the hand
# changes only revisits what changed.
# Outputs: code/vendor/keep8.tsv (module, kind, name, occurrence, reason: the first
# error, or the list the declaration came from) and generalize.out (one line per module: status,
# `Fin 8` occurrences, kept declarations, rounds, seconds; totals). A module that does not
# converge in 12 rounds is kept whole (all its declarations listed, status ORIGINAL).
# Run (about 20 minutes, 2 GB): EM8_SRC=<clone>/LeanCode/LargeS/Lean_Code bash code/vendor/generalize.sh
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
PKG=$(cd "$HERE/../.." && pwd)
PD=${GEN_DIR:-$(mktemp -d)}
MIX="perl $HERE/probe_mix.pl"
OUT=$HERE/generalize.out; KEEP=$HERE/keep8.tsv
INIT=${INIT:-$KEEP}
say() { echo "[$(date -Is)] $*"; }
mkdir -p "$PD/Tammes15/Vendor" "$PD/logs" "$PD/rev"
cp "$PKG/lean-toolchain" "$PD/"
PKGS=$(realpath --relative-to="$PD" "$(realpath "$PKG/.lake/packages")")
sed "s|\"packagesDir\": \"[^\"]*\"|\"packagesDir\": \"$PKGS\"|; s|\"name\": \"tammes-15\"|\"name\": \"generalize\"|" \
  "$PKG/lake-manifest.json" > "$PD/lake-manifest.json"
cat > "$PD/lakefile.toml" <<TOML
name = "generalize"
packagesDir = "$PKGS"
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.34.1"
[[lean_lib]]
name = "VendorEM8"
globs = ["Tammes15.Vendor.EM8.+"]
leanOptions = { autoImplicit = true, relaxedAutoImplicit = true }
TOML
# the vendored files before the generalization
rm -rf "$PD/stage"; VENDOR_DST=$PD/stage VENDOR_NOSUB=1 bash "$HERE/vendor.sh" > /dev/null || exit 1
order=$(cat "$HERE/vendor_order.txt")
rm -rf "$PD/Tammes15/Vendor/EM8"; mkdir -p "$PD/Tammes15/Vendor/EM8"
init=$(mktemp)
if [ -f "$INIT" ]; then cp "$INIT" "$init"; fi
new=$(mktemp); printf "module\tkind\tname\toccurrence\treason\n" > "$new"
cd "$PD" || exit 1
export LEAN_NUM_THREADS=2 PROBE_PATH=Tammes15/Vendor/EM8/
n=$(echo $order | wc -w)
say "modules: $n; initial keep list: $(($(grep -vc '^module' "$init") )) rows"
: > "$OUT"
memwait() { local t=0
  while [ "$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)" -lt 12 ] && [ $t -lt 1800 ]; do
    sleep 30; t=$((t+30)); done
  [ $t -gt 0 ] && say "waited $t s for MemAvailable >= 12 GB"; }
build() { memwait; lake build "+Tammes15.Vendor.EM8.$1" > "$2" 2>&1; }
t0=$(date +%s); i=0
for m in $order; do
  i=$((i+1)); ts=$(date +%s); f="stage/$m.lean"; dst="Tammes15/Vendor/EM8/$m.lean"
  $MIX keys "$f" > "rev/$m.keys"
  f8=$(grep -c 'Fin 8' "$f")
  # ids of the initially kept chunks, with the reason recorded for them
  awk -F'\t' -v m="$m" 'NR == FNR { if ($1 == m) r[$2 "\t" $3 "\t" $4] = $5; next }
    ($2 "\t" $3 "\t" $4) in r { print $1 "\t" r[$2 "\t" $3 "\t" $4] }' "$init" "rev/$m.keys" > "rev/$m.why"
  cut -f1 "rev/$m.why" > "rev/$m.txt"
  round=0; st=""
  while :; do
    round=$((round+1))
    $MIX mix "$f" "rev/$m.txt" > "$dst"
    log="logs/$m.r$round.log"
    if build "$m" "$log"; then
      if [ "$f8" -eq 0 ]; then st=UNCHANGED; elif [ -s "rev/$m.txt" ]; then st=MIXED; else st=GENERIC; fi
      break; fi
    add=$($MIX next "$f" "$m" "$log" "rev/$m.txt")
    if [ -z "$add" ] || [ $round -ge 12 ] || [ "$f8" -eq 0 ]; then
      cp "$f" "$dst"
      if build "$m" "logs/$m.orig.log"; then st=ORIGINAL
        awk -F'\t' '$1 != "" { print $1 "\tnot converged: kept whole" }' "rev/$m.keys" > "rev/$m.why"
        cut -f1 "rev/$m.why" > "rev/$m.txt"
      else st=BLOCKED; grep -E '^error' "$log" | head -5 | cut -c1-240 | sed 's/^/    /' >> "$OUT"; fi
      break; fi
    printf "%s\n" "$add" >> "rev/$m.why"; cut -f1 <<< "$add" >> "rev/$m.txt"
  done
  # kept chunks that mention Fin 8, as keys
  $MIX chunks "$f" | awk -F'\t' '$6 > 0 { print $1 }' > "rev/$m.f8"
  awk -F'\t' -v m="$m" 'FILENAME == ARGV[1] { f8[$1] = 1; next } FILENAME == ARGV[2] { if (!($1 in w)) w[$1] = $2; next }
    ($1 in w) && ($1 in f8) { print m "\t" $2 "\t" $3 "\t" $4 "\t" w[$1] }' "rev/$m.f8" "rev/$m.why" "rev/$m.keys" >> "$new"
  printf "%-9s %d/%d %s: Fin8=%d kept=%d rounds=%d %ds\n" "$st" "$i" "$n" "$m" "$f8" \
    "$(awk -F'\t' -v m="$m" '$1 == m' "$new" | wc -l)" "$round" "$(( $(date +%s) - ts ))" | tee -a "$OUT"
  [ "$st" = BLOCKED ] && { say "stopped at $m"; break; }
done
cp "$new" "$KEEP"; rm -f "$new" "$init"
{ echo "totals:"; for s in UNCHANGED GENERIC MIXED ORIGINAL BLOCKED; do
    echo "  $s $(grep -c "^$s " "$OUT")"; done
  echo "  kept declarations: $(( $(wc -l < "$KEEP") - 1 ))"
  cg=$(sed -n 's/^0:://p' /proc/self/cgroup)
  echo "  wall $(( $(date +%s) - t0 )) s; cgroup memory.peak $(cat "/sys/fs/cgroup$cg/memory.peak" 2>/dev/null || echo unknown) bytes"
} | tee -a "$OUT"
