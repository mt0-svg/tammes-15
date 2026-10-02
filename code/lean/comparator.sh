#!/bin/bash
# Comparator (Section 10.5 of the paper) on this package, after its build by code/lean/check.sh, with the steps of the
# job comparator of .github/workflows/ci.yml: the build outputs of the challenge modules are deleted, so that
# Comparator builds the challenge from its source in its sandbox, and `lake env comparator config.json` runs in a
# systemd unit where landrun cannot reach the user's session bus (no AF_UNIX sockets). The solution is the build that
# check.sh made. Modes:
#   pass       config.json as it is: the fifteen theorems it names (`Tammes15.reduction`, `Tammes15.fejesToth_bound`,
#              `Tammes15.conjecture_of_enum_killed`, `Tammes15.nonunique_of_enum_killed`, eight of
#              `Tammes15.PaperSteps`, `Tammes15.Contractors.killed_of_progTreesDom`,
#              `Tammes15.conjecture_of_enum_progTreesDom` and `Tammes15.nonunique_of_enum_progTreesDom`) of
#              `Tammes15.Solution` must have exactly the statements of
#              `Tammes15.Challenge`, every constant these statements reach must be identical in the two, only
#              propext, Quot.sound and Classical.choice may be used, and the Lean kernel and nanoda must accept the
#              export of the proofs. Expected: PASS. When lean4export crashes (exit 139)
#              during the export, before any kernel runs (code/lean/export_crash.awk), Comparator runs once more and
#              that run decides, as in ci.yml.
#   fejestoth  on a copy of the package, `FejesTothBound` changed to `d ≤ dhi + 1` in Tammes15/Challenge/Hyps/Computations.lean
#              only. Expected: FAIL on `Tammes15.FejesTothBound`.
#   oldstatement  on a copy of the package, the statement of `Tammes15.reduction` in Tammes15/Challenge.lean given the
#              hypothesis `(h0 : Tammes15.FejesTothBound)` again, as in version 1.0.0. Expected: FAIL on the statement
#              of `Tammes15.reduction`.
#   frames     on a copy of the package, the frame C1 of the challenge given the point 11 of the 18 in place of the
#              point 10 (`keepC1` in Tammes15/Challenge/Attained/Data.lean only). Expected: FAIL on
#              `Tammes15.Attained.keepC1`.
#   nonunique  on a copy of the package, the statement of `Tammes15.nonunique_of_enum_killed` in Tammes15/Challenge.lean
#              asks for isomorphic contact graphs (`Nonempty` in place of `IsEmpty`). Expected: FAIL on the statement of
#              `Tammes15.nonunique_of_enum_killed`.
#   progtrees  on a copy of the package, `ProgTrees` no longer asks the root box of each tree to hold the solutions
#              (`RootOK lo hi B₀ ∧` removed in Tammes15/Challenge/PaperSteps/SearchDefs.lean only). Expected: FAIL on
#              `Tammes15.PaperSteps.ProgTrees`.
#   domok      on a copy of the package, the domain of the contractors of the program widened (the upper end of the
#              edge length 1.5 in place of 1 in `DomOK`, Tammes15/Challenge/Contractors/Defs.lean only). Expected: FAIL on
#              `Tammes15.Contractors.DomOK`.
#   progframes on a copy of the package, the statement of `Tammes15.Contractors.killed_of_progTreesDom` in
#              Tammes15/Challenge.lean kills the cases with the frame C1 only (`frameC3` removed). Expected: FAIL on the
#              statement of `Tammes15.Contractors.killed_of_progTreesDom`.
# Every mode runs with config.json as it is, nanoda on. Comparator exports the challenge and the solution, compares
# the statements and the constants they reach, then runs nanoda (4 threads) and, unless config.json sets lean_kernel
# to false (a patch of this repository on Comparator, .github/comparator-lean-kernel.patch), the Lean kernel (one
# thread) after it. code/lean/comparator.out records a pass with config.json as it is,
# code/lean/comparator-progtrees.out the control progtrees. A control fails at the comparison, before any kernel runs.
# Usage, from the root of the repository:
#   code/lean/comparator.sh pass|fejestoth|oldstatement|frames|nonunique|progtrees|domok|progframes
# Env: COMPARATOR (the comparator binary), COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA (paths, built
# at the commits of the job comparator of ci.yml); CMP_MEM (default 12G), CMP_TIME (default 2h), CMP_CPUS (default: no
# limit), the limits of the run.
# Exit status 0 when the result is the expected one.
set -u
export LC_ALL=C.UTF-8
mode=${1:?usage: comparator.sh pass|fejestoth|oldstatement|frames|nonunique|progtrees|domok|progframes}
root=$(cd "$(dirname "$0")/../.." && pwd)
nanoda=$(jq -r '.enable_nanoda // false' "$root/config.json")
case $mode in
  pass) pkg=$root; expect='Your solution is okay!' ;;
  fejestoth) expect="Const does not match between challenge and target 'Tammes15.FejesTothBound'"
       file=Tammes15/Challenge/Hyps/Computations.lean
       old='  ∀ d : ℝ, Nonempty (Config 15 d) → d ≤ dhi'; new='  ∀ d : ℝ, Nonempty (Config 15 d) → d ≤ dhi + 1' ;;
  oldstatement) expect="Challenge and solution theorem statement do not match: 'Tammes15.reduction'"
       file=Tammes15/Challenge.lean
       old='    (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)'
       new='    (h0 : Tammes15.FejesTothBound) (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)' ;;
  frames) expect="Const does not match between challenge and target 'Tammes15.Attained.keepC1'"
       file=Tammes15/Challenge/Attained/Data.lean
       old='def keepC1 : Fin 15 → Fin 18 := !\[0, 1, 2, 3, 4, 5, 6, 7, 10, 12, 13, 14, 15, 16, 17\]'
       new='def keepC1 : Fin 15 → Fin 18 := ![0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17]' ;;
  nonunique) expect="Challenge and solution theorem statement do not match: 'Tammes15.nonunique_of_enum_killed'"
       file=Tammes15/Challenge.lean
       old='        IsEmpty (Tammes15.Nonunique.contactGraph X (Real.cos d) ≃g'
       new='        Nonempty (Tammes15.Nonunique.contactGraph X (Real.cos d) ≃g' ;;
  progtrees) expect="Const does not match between challenge and target 'Tammes15.PaperSteps.ProgTrees'"
       file=Tammes15/Challenge/PaperSteps/SearchDefs.lean
       old='        RootOK lo hi B₀ ∧ t.OK (N.narrow P k H₀ m) (LeafKill N P H₀) B₀'
       new='        t.OK (N.narrow P k H₀ m) (LeafKill N P H₀) B₀' ;;
  domok) expect="Const does not match between challenge and target 'Tammes15.Contractors.DomOK'"
       file=Tammes15/Challenge/Contractors/Defs.lean
       old='  (1.1 ≤ B.lo .a ∧ B.hi .a ≤ 1.3) ∧ (0.9 ≤ B.lo .d ∧ B.hi .d ≤ 1) ∧'
       new='  (1.1 ≤ B.lo .a ∧ B.hi .a ≤ 1.3) ∧ (0.9 ≤ B.lo .d ∧ B.hi .d ≤ 1.5) ∧' ;;
  progframes) expect="Challenge and solution theorem statement do not match: 'Tammes15.Contractors.killed_of_progTreesDom'"
       file=Tammes15/Challenge.lean
       old='    (hN : Tammes15.Contractors.Impl N) : Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3} := sorry'
       new='    (hN : Tammes15.Contractors.Impl N) : Tammes15.Killed L {Tammes15.Attained.frameC1} := sorry' ;;
  *) echo "usage: comparator.sh pass|fejestoth|oldstatement|frames|nonunique|progtrees|domok|progframes" >&2; exit 2 ;;
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
