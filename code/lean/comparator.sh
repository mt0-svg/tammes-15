#!/bin/bash
# Comparator (Section 9.3 of the paper) on this package, after its build by code/lean/check.sh, with the steps of the
# job comparator of .github/workflows/ci.yml: the build outputs of the challenge modules are deleted, so that
# Comparator builds the challenge from its source in its sandbox, and `lake env comparator config.json` runs in a
# systemd unit where landrun cannot reach the user's session bus (no AF_UNIX sockets). The solution is the build that
# check.sh made. With config.json as it is, the fifteen theorems it names (`Tammes15.reduction`,
# `Tammes15.fejesToth_bound`, `Tammes15.conjecture_of_enum_killed`, `Tammes15.nonunique_of_enum_killed`, eight of
# `Tammes15.PaperSteps`, `Tammes15.Contractors.killed_of_progTreesDom`, `Tammes15.conjecture_of_enum_progTreesDom`
# and `Tammes15.nonunique_of_enum_progTreesDom`) of `Tammes15.Solution` must have exactly the statements of
# `Tammes15.Challenge`, every constant these statements reach must be identical in the two, only propext, Quot.sound
# and Classical.choice may be used, and the kernels must accept the export of the proofs. Expected: PASS. When
# lean4export crashes (exit 139) during the export, before any kernel runs (code/lean/export_crash.awk), Comparator
# runs once more and that run decides, as in ci.yml. Comparator exports the challenge and the solution, compares
# the statements and the constants they reach, then runs nanoda (4 threads) and, unless config.json sets lean_kernel
# to false (a patch of this repository on Comparator, .github/comparator-lean-kernel.patch), the Lean kernel (one
# thread) after it. code/lean/comparator.out records a pass.
# Usage, from the root of the repository:
#   code/lean/comparator.sh pass
# Env: COMPARATOR (the comparator binary), COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA (paths, built
# at the commits of the job comparator of ci.yml); CMP_MEM (default 12G), CMP_TIME (default 2h), CMP_CPUS (default: no
# limit), the limits of the run.
# Exit status 0 when the result is the expected one.
set -u
export LC_ALL=C.UTF-8
mode=${1:?usage: comparator.sh pass}
root=$(cd "$(dirname "$0")/../.." && pwd)
nanoda=$(jq -r '.enable_nanoda // false' "$root/config.json")
case $mode in
  pass) pkg=$root; expect='Your solution is okay!' ;;
  *) echo "usage: comparator.sh pass" >&2; exit 2 ;;
esac
for v in COMPARATOR COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA; do
  [ -x "${!v:-}" ] || { echo "$v is not an executable: ${!v:-unset}" >&2; exit 2; }
done
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
jq ".enable_nanoda = $nanoda" "$root/config.json" > "$tmp/config.json"
echo "config: $(jq -c . "$tmp/config.json")"
echo "comparator $("$COMPARATOR" --version 2>/dev/null | head -1)"
rm -rf "$pkg"/.lake/build/lib/lean/Tammes15/Challenge "$pkg"/.lake/build/lib/lean/Tammes15/Challenge.* \
  "$pkg"/.lake/build/ir/Tammes15/Challenge "$pkg"/.lake/build/ir/Tammes15/Challenge.*
# Comparator's README: run it where landrun cannot reach the user's session bus (no AF_UNIX sockets).
run() { # $1: the log file; the exit status is Comparator's
  systemd-run --user --pipe --wait --collect -q -p RestrictAddressFamilies=~AF_UNIX \
    -p MemoryMax="${CMP_MEM:-12G}" -p MemorySwapMax=0 -p RuntimeMaxSec="${CMP_TIME:-2h}" \
    ${CMP_CPUS:+-p CPUQuota=$((CMP_CPUS * 100))%} \
    -E PATH="$PATH" -E HOME="$HOME" -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
    -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" -E COMPARATOR_NANODA="$COMPARATOR_NANODA" \
    --working-directory "$pkg" -- bash -c '
      lake env "$0" "$1"; rc=$?
      echo "memory.peak $(cat "/sys/fs/cgroup$(sed -n "s/^0:://p" /proc/self/cgroup)/memory.peak" 2>/dev/null)"
      exit $rc' "$COMPARATOR" "$tmp/config.json" 2>&1 | sed "s|$pkg/||g; s|$tmp/||g" | tee "$1"
  return "${PIPESTATUS[0]}"
}
s0=$(date +%s)
log=$tmp/log
run "$log"; rc=$?
# One more run when lean4export crashed during the export, before any kernel (code/lean/export_crash.awk),
# as the job comparator of ci.yml does; any other failure, or a second crash, is final.
retry=no
if [ "$rc" != 0 ] && awk -f "$root/code/lean/export_crash.awk" "$log"; then
  retry=yes
  echo "RETRY: lean4export exited with 139 during the export, before any kernel; Comparator runs once more"
  log=$tmp/log-retry
  run "$log"; rc=$?
fi
secs=$(($(date +%s) - s0))
peak=$(sed -n 's/^memory\.peak //p' "$log")
if [ "$rc" = 0 ] && grep -q "Your solution is okay!" "$log"; then r=PASS; elif [ "$rc" != 0 ]; then r=FAIL; else r=UNFINISHED; fi
echo "COMPARATOR $r (nanoda $([ $nanoda = true ] && echo on || echo off)): $secs s wall, memory peak $([ -n "$peak" ] && echo $((peak >> 20)) || echo '?') MiB, exit $rc, retry $retry"
if grep -qF "$expect" "$log" && [ "$r" = PASS ]; then
  echo "RESULT $mode: as expected ($expect)"; exit 0
fi
echo "RESULT $mode: NOT as expected"; exit 1
