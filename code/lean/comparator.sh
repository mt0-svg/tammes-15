#!/bin/bash
# Comparator (Section 8.5 of the paper) on this package, after its build by code/lean/check.sh, with the steps of the
# job comparator of .github/workflows/ci.yml: the build outputs of the challenge modules are deleted, so that
# Comparator builds the challenge from its source in its sandbox, and `lake env comparator config.json` runs in a
# systemd unit where landrun cannot reach the user's session bus (no AF_UNIX sockets). The solution is the build that
# check.sh made. Modes:
#   pass       config.json as it is: `Tammes15.reduction` and `Tammes15.fejesToth_bound` of `Tammes15.Solution` must
#              have exactly the statements of `Tammes15.Challenge`, every constant these statements reach must be
#              identical in the two, only propext, Quot.sound and Classical.choice may be used, and the Lean kernel
#              and nanoda must accept the export of the proofs. Expected: PASS. When lean4export crashes (exit 139)
#              during the export, before any kernel runs (code/lean/export_crash.awk), Comparator runs once more and
#              that run decides, as in ci.yml.
#   fejestoth  on a copy of the package, `FejesTothBound` changed to `d ≤ dhi + 1` in Tammes15/Challenge/Hyps/Computations.lean
#              only. Expected: FAIL on `Tammes15.FejesTothBound`.
#   oldstatement  on a copy of the package, the statement of `Tammes15.reduction` in Tammes15/Challenge.lean given the
#              hypothesis `(h0 : Tammes15.FejesTothBound)` again, as in version 1.0.0. Expected: FAIL on the statement
#              of `Tammes15.reduction`.
# The controls run with the Lean kernel only.
# Usage, from the root of the repository: code/lean/comparator.sh pass|fejestoth|oldstatement
# Env: COMPARATOR (the comparator binary), COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA (paths, built
# at the commits of the job comparator of ci.yml); CMP_MEM (default 12G), CMP_TIME (default 2h), CMP_CPUS (default: no
# limit), the limits of the run.
# Exit status 0 when the result is the expected one.
set -u
export LC_ALL=C.UTF-8
mode=${1:?usage: comparator.sh pass|fejestoth|oldstatement}
root=$(cd "$(dirname "$0")/../.." && pwd)
case $mode in
  pass) pkg=$root; nanoda=true; expect='Your solution is okay!' ;;
  fejestoth) nanoda=false; expect="Const does not match between challenge and target 'Tammes15.FejesTothBound'"
       file=Tammes15/Challenge/Hyps/Computations.lean
       old='  ∀ d : ℝ, Nonempty (Config 15 d) → d ≤ dhi'; new='  ∀ d : ℝ, Nonempty (Config 15 d) → d ≤ dhi + 1' ;;
  oldstatement) nanoda=false; expect="Challenge and solution theorem statement do not match: 'Tammes15.reduction'"
       file=Tammes15/Challenge.lean
       old='    (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)'
       new='    (h0 : Tammes15.FejesTothBound) (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)' ;;
  *) echo "usage: comparator.sh pass|fejestoth|oldstatement" >&2; exit 2 ;;
esac
for v in COMPARATOR COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA; do
  [ -x "${!v:-}" ] || { echo "$v is not an executable: ${!v:-unset}" >&2; exit 2; }
done
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
if [ "$mode" != pass ]; then
  pkg=$tmp/pkg; mkdir -p "$pkg"
  cp -a "$root/Tammes15" "$root/lakefile.toml" "$root/lake-manifest.json" "$root/lean-toolchain" "$pkg/"
  cp -a "$root/.lake" "$pkg/.lake"
  n=$(grep -cxF "${old//\\/}" "$pkg/$file" || true)
  [ "$n" = 1 ] || { echo "control $mode: the line to change is found $n times in $file" >&2; exit 2; }
  sed -i "s|^${old}\$|${new}|" "$pkg/$file"
  echo "control $mode: in $file only, the line"; echo "  ${old//\\/}"; echo "is changed to"; echo "  $new"
  echo "lines that differ from the original in the copy of Tammes15/: $(diff -r "$root/Tammes15" "$pkg/Tammes15" | grep -c '^[<>]')"
fi
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
# Mode pass: one more run when lean4export crashed during the export, before any kernel (code/lean/export_crash.awk),
# as the job comparator of ci.yml does; any other failure, or a second crash, is final.
retry=no
if [ "$mode" = pass ] && [ "$rc" != 0 ] && awk -f "$root/code/lean/export_crash.awk" "$log"; then
  retry=yes
  echo "RETRY: lean4export exited with 139 during the export, before any kernel; Comparator runs once more"
  log=$tmp/log-retry
  run "$log"; rc=$?
fi
secs=$(($(date +%s) - s0))
peak=$(sed -n 's/^memory\.peak //p' "$log")
if [ "$rc" = 0 ] && grep -q "Your solution is okay!" "$log"; then r=PASS; elif [ "$rc" != 0 ]; then r=FAIL; else r=UNFINISHED; fi
echo "COMPARATOR $r (nanoda $([ $nanoda = true ] && echo on || echo off)): $secs s wall, memory peak $([ -n "$peak" ] && echo $((peak >> 20)) || echo '?') MiB, exit $rc, retry $retry"
want=FAIL; [ "$mode" = pass ] && want=PASS
if grep -qF "$expect" "$log" && [ "$r" = "$want" ]; then
  echo "RESULT $mode: as expected ($expect)"; exit 0
fi
echo "RESULT $mode: NOT as expected"; exit 1
