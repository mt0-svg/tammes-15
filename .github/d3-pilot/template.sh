#!/bin/bash
# template.sh OUT: the trusted template of the D3 pilot, written from .github/d3-pilot/jobs.tsv (one line per chunk
# job: its name, then the names of its loader definitions, constants of Tammes15.D3Pilot.Jobs): OUT/Challenge.lean,
# the chunk statements with `sorry`, and OUT/configs/<name>.json, the Comparator config of each job (its one theorem,
# the three standard axioms, nanoda alone). A job checks that the challenge module and its config are byte-equal to
# this template before it runs Comparator, and the join checks it again for every job.
set -eu
out=$1; root=$(git rev-parse --show-toplevel); jobs=$root/.github/d3-pilot/jobs.tsv
stmt="Tammes15.D3Data.ChunkG Tammes15.D3Data.QXR"
mkdir -p "$out/configs"
{
  echo "import Tammes15.D3Data.ChunkX"
  echo "import Tammes15.D3Data.LinR"
  echo "import Tammes15.D3Pilot.Jobs"
  echo
  echo "namespace Tammes15.D3Pilot"
  while read -r name _; do
    case $name in '#'* | '') continue ;; esac
    echo
    echo "theorem chunk_$name : $stmt job_$name := by sorry"
  done < "$jobs"
  echo
  echo "end Tammes15.D3Pilot"
} > "$out/Challenge.lean"
while read -r name _; do
  case $name in '#'* | '') continue ;; esac
  printf '{\n  "challenge_module": "Tammes15.D3Pilot.Challenge",\n  "solution_module": "Tammes15.D3Pilot.%s.Solution",\n  "theorem_names": ["Tammes15.D3Pilot.chunk_%s"],\n  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],\n  "enable_nanoda": true,\n  "lean_kernel": false\n}\n' "$name" "$name" > "$out/configs/$name.json"
done < "$jobs"
