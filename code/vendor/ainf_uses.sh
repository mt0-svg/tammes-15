#!/bin/bash
# aInf_uses.out: aInf_uses.pl on the source files of the import closure of BoundaryFaceSupport (the
# face chain), in sorted order.
# Run: EM8_SRC=<clone>/LeanCode/LargeS/Lean_Code bash code/vendor/ainf_uses.sh > code/vendor/aInf_uses.out
set -eu
SRC=${EM8_SRC:?set EM8_SRC to LeanCode/LargeS/Lean_Code of a clone of the source}
HERE=$(cd "$(dirname "$0")" && pwd)
declare -A seen
visit() { local m=$1; [ -n "${seen[$m]:-}" ] && return; seen[$m]=1
  for d in $(grep -E '^import Lean_Code\.' "$SRC/$m.lean" | sed 's/^import Lean_Code\.//'); do visit "$d"; done; }
visit BoundaryFaceSupport
perl "$HERE/aInf_uses.pl" $(for m in "${!seen[@]}"; do echo "$SRC/$m.lean"; done | LC_ALL=C sort)
