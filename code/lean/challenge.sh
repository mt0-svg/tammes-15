#!/bin/bash
# code/lean/challenge.sh: write the definition modules of the Comparator challenge (Section 10.5 of the paper),
# from the root of the repository. The modules Tammes15/Challenge/** are copies, whole, of the Tammes15 import closure of the modules
# that hold the definitions the fifteen statements of Tammes15/Challenge.lean reach: Tammes15.Hyps.Computations
# (D1 to D4, EnumComplete with its class D2Regions.PlaneClass), Tammes15.Attained.Data (the frames), Tammes15.Nonunique.Defs
# (contactGraph), Tammes15.PaperSteps.SearchDefs (ProgKilled, Procs, ProgTrees), Tammes15.PaperSteps.FrameDefs and
# Tammes15.Contractors.Defs (Impl, ProgTreesDom, with the arithmetic and the primitive steps of Arith and Prims). Only
# the imports are renamed (Tammes15.X to Tammes15.Challenge.X). Tammes15/Challenge.lean itself, the statements, is
# written by hand. Prints the closure, one module per line, and checks that each copy differs from its source in its
# Tammes15 imports only.
# With --closure ROOT..., prints the closure of the given modules and its size, and writes nothing:
#   code/lean/challenge.sh --closure Tammes15.Hyps.Computations Tammes15.Attained.Data Tammes15.Nonunique.Defs
# gives the modules that the first four statements of config.json reach. Record: code/lean/challenge.out.
set -eu
cd "$(dirname "$0")/../.."
roots="Tammes15.Hyps.Computations Tammes15.Attained.Data Tammes15.Nonunique.Defs Tammes15.PaperSteps.SearchDefs Tammes15.PaperSteps.FrameDefs Tammes15.Contractors.Defs"
only=""
if [ "${1:-}" = --closure ]; then shift; roots="$*"; only=1; fi
declare -A seen=(); q=($roots)
while [ ${#q[@]} -gt 0 ]; do
  m=${q[0]}; q=("${q[@]:1}")
  [ -n "${seen[$m]:-}" ] && continue
  seen[$m]=1
  f=$(echo "$m" | tr . /).lean
  [ -f "$f" ] || { echo "missing $f" >&2; exit 1; }
  for i in $(sed -n -E 's/^import (Tammes15\.[A-Za-z0-9_.]+)[[:space:]]*$/\1/p' "$f"); do q+=("$i"); done
done
closure=$(printf '%s\n' "${!seen[@]}" | LC_ALL=C sort)
if [ -n "$only" ]; then
  printf "%s\n" $closure
  echo "modules: $(echo $closure | wc -w), lines: $(for m in $closure; do cat "$(echo "$m" | tr . /).lean"; done | wc -l)"
  exit 0
fi
rm -rf Tammes15/Challenge
for m in $closure; do
  src=$(echo "$m" | tr . /).lean; dst=Tammes15/Challenge/${src#Tammes15/}
  mkdir -p "$(dirname "$dst")"
  sed -E 's/^import Tammes15\./import Tammes15.Challenge./' "$src" > "$dst"
  other=$(diff "$src" "$dst" | grep '^[<>]' | grep -vE '^[<>] import Tammes15\.' | wc -l || true)
  [ "$other" = 0 ] || { echo "copy $dst: $other changed lines outside the imports" >&2; exit 1; }
done
printf '%s\n' $closure
echo "modules: $(echo $closure | wc -w), lines: $(cd Tammes15/Challenge && find . -name '*.lean' | xargs cat | wc -l)" >&2
