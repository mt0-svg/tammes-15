#!/bin/bash
# The checks of the Lean package, from a clone of this repository (Section 8.5 of the paper):
#  1. `lake build` of every library of lakefile.toml; the only `sorry` warnings allowed are the two of
#     Tammes15/Challenge.lean, the statements Comparator checks (the complete build log goes to BUILD_LOG);
#  2. `lake build --no-build` of the same libraries: every target is up to date (its output is appended to BUILD_LOG);
#  3. the source scan code/lean/scan.sh of Tammes15/ and lakefile.toml; allowed: those `sorry`, and the local
#     notations of the vendored library Tammes15/Vendor/EM8;
#  4. `#print axioms` of the theorems of code/lean/axioms.lean: only propext, Classical.choice and Quot.sound;
#  5. code/lean/types.lean: each interface has the type of the theorem that proves it;
#  6. the environment audit code/lean/EnvAudit.lean of every constant of every module of the package except the
#     challenge, which follows every constant to the constants it uses and lists the axioms reached.
# Usage, from the root of the repository: code/lean/check.sh > code/lean/check.out 2>&1
# Env: BUILD_LOG (default code/lean/build.out), LEAN_NUM_THREADS (default 3: Lake then runs about four Lean
# processes, which fit in 8 GB). Exit status 0 when every step passes.
set -u
export LC_ALL=C.UTF-8
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-3}
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
log=${BUILD_LOG:-code/lean/build.out}
fail=0
res() { printf '%s: %s\n' "$1" "$2"; [ "$2" = PASS ] || fail=1; }
if git rev-parse --git-dir > /dev/null 2>&1; then
  commit="commit $(git rev-parse --short HEAD), uncommitted changes to the sources it hashes: $(git status --porcelain -- Tammes15 lakefile.toml lake-manifest.json lean-toolchain code/lean/{check.sh,scan.sh,axioms.lean,types.lean,EnvAudit.lean} | wc -l)"
else commit="not a git checkout"; fi
echo "# code/lean/check.sh, $(date -u '+%F %H:%M UTC'), $commit"
echo "# $(lake env lean --version 2>/dev/null | head -1); $(lake --version | head -1)"
echo "# Mathlib: manifest $(jq -r '.packages[] | select(.name == "mathlib") | .rev' lake-manifest.json), checkout $(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null)"
srchash=$({ find Tammes15 -type f; printf '%s\n' lakefile.toml lake-manifest.json lean-toolchain code/lean/{check.sh,scan.sh,axioms.lean,types.lean,EnvAudit.lean}; } | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-16)
echo "# sources: sha256 $srchash of the list of sha256 sums of the files of Tammes15/, lakefile.toml, lake-manifest.json, lean-toolchain and the five files of code/lean/ that this script reads (code/lean/sources.sh prints it)"
echo "# LEAN_NUM_THREADS $LEAN_NUM_THREADS; $(nproc) processors visible"

libs=$(awk '/^\[\[lean_lib\]\]/ {l = 1} l && /^name = / {gsub(/"/, "", $3); print $3; l = 0}' lakefile.toml)
echo "== 1. lake build" $libs
t0=$(date +%s)
lake build $libs > "$log" 2>&1; rc=$?
t1=$(date +%s)
nb=$(grep -cE '^[^ ]+ \[[0-9]+/[0-9]+\] Built Tammes15\.' "$log" || true)
nr=$(grep -cE '^[^ ]+ \[[0-9]+/[0-9]+\] (Replayed|Built) Tammes15\.' "$log" || true)
sorrys=$(grep -E "declaration uses [\`']sorry[\`']" "$log" | grep -c . || true)
sorry_ok=$(grep -E "^warning: Tammes15/Challenge\.lean:[0-9]+:[0-9]+: declaration uses [\`']sorry[\`']" "$log" | grep -c . || true)
echo "exit $rc, $((t1 - t0)) s wall; modules of the package built: $nb (built or replayed: $nr); sorry warnings: $sorrys, of them in Tammes15/Challenge.lean: $sorry_ok"
tail -1 "$log"
[ $rc = 0 ] && [ "$sorrys" = "$sorry_ok" ] && [ "$sorry_ok" = 2 ] && res build PASS || res build FAIL

echo "== 2. every target up to date (lake build --no-build)"
{ echo; echo "== lake build --no-build $libs"; } >> "$log"
lake build --no-build $libs >> "$log" 2>&1; rc=$?
echo "exit $rc; $(tail -1 "$log")"
[ $rc = 0 ] && res up-to-date PASS || res up-to-date FAIL

echo "== 3. source scan (code/lean/scan.sh Tammes15 lakefile.toml)"
scan=$(bash code/lean/scan.sh Tammes15 lakefile.toml); echo "$scan"
other=$(printf '%s\n' "$scan" | grep -E '^[^ ]+:[0-9]+: ' \
  | grep -vE '^Tammes15/Challenge\.lean:[0-9]+: sorry \| ' | grep -vE '^Tammes15/Vendor/EM8/[A-Za-z]+\.lean:[0-9]+: notation \| local notation ' || true)
if [ -z "$other" ]; then res scan PASS; else echo "not allowed:"; echo "$other"; res scan FAIL; fi

echo "== 4. #print axioms (code/lean/axioms.lean)"
ax=$(lake env lean code/lean/axioms.lean 2>&1); rc=$?; echo "$ax"
n=$(printf '%s\n' "$ax" | grep -c "depends on axioms" || true)
want=$(grep -c '^#print axioms' code/lean/axioms.lean)
bad=$(printf '%s\n' "$ax" | sed -n "s/^'[^']*' depends on axioms: \[\(.*\)\]$/\1/p" | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u | tr '\n' ' ' || true)
echo "exit $rc; $n of $want theorems printed; axioms outside propext, Classical.choice, Quot.sound: ${bad:-none}"
[ $rc = 0 ] && [ "$n" = "$want" ] && [ -z "$bad" ] && res axioms PASS || res axioms FAIL

echo "== 5. types of the interfaces (code/lean/types.lean)"
ty=$(lake env lean code/lean/types.lean 2>&1); rc=$?; echo "${ty:-(no message)}"
echo "exit $rc; examples: $(grep -c '^example' code/lean/types.lean)"
[ $rc = 0 ] && [ -z "$ty" ] && res types PASS || res types FAIL

echo "== 6. environment audit (code/lean/EnvAudit.lean), every module of the package except Tammes15.Challenge*"
mods=$(find Tammes15 -name '*.lean' ! -path 'Tammes15/Challenge/*' ! -name Challenge.lean | sed 's|\.lean$||; s|/|.|g' | LC_ALL=C sort)
t=$(mktemp --suffix=.lean); trap 'rm -f "$t"' EXIT
{ echo "import Lean"; printf 'import %s\n' $mods; grep -v '^import ' code/lean/EnvAudit.lean; echo; echo "#env_audit \"M:Tammes15\""; } > "$t"
au=$(lake env lean "$t" 2>&1); rc=$?
printf '%s\n' "$au" | sed -E "s#^$t:[0-9]+:[0-9]+: (info|warning|error): ##"
echo "exit $rc; modules audited: $(echo $mods | wc -w)"
printf '%s\n' "$au" | grep -q 'AXIOMS OK' && printf '%s\n' "$au" | grep -q 'FLAGS: 0 ' && ! printf '%s\n' "$au" | grep -q ': error' \
  && res audit PASS || res audit FAIL

[ $fail = 0 ] && echo "CHECK PASS" || echo "CHECK FAIL"
exit $fail
