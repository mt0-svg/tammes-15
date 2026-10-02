#!/bin/bash
# The second enumerator at n = 14 on the class graphs that pass W1, each variant of kat.sh compared with the plantri
# route (run.sh). One core.
cd "$(dirname "$0")"
V=("" "--ring" "--ring2" "--ring2 --caps" "--ring2 --caps --tight" "--ring2 --caps --tight --rule 1")
for v in "${V[@]}"; do ./run.sh 14 w1 $v; done
