#!/bin/bash
# Known-answer tests of the second enumerator (run.sh): the class at n = 6..11 and the W1 sets
# at n = 12, 13, for each variant (no isomorph rejection, --ring, --ring2, --ring2 with the sharper
# look-ahead --caps, with --tight, with step rule 1), and the negative control at n = 12. One core.
cd "$(dirname "$0")"
V=("" "--ring" "--ring2" "--ring2 --caps" "--ring2 --caps --tight" "--ring2 --caps --tight --rule 1")
for n in 6 7 8 9 10 11; do for v in "${V[@]}"; do ./run.sh $n all $v; done; done
for n in 12 13; do for v in "${V[@]}"; do ./run.sh $n w1 $v; done; done
./run.sh 12 sabotage
./run.sh 12 sabotage --ring2 --caps --tight --rule 1
