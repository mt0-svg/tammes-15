#!/bin/sh
# Negative control of the replay: the tree of data/sample/k3 with one leaf replaced by a split whose
# halves are refuted without reason must be rejected.
# Usage (from the repository root, after building code/impl1/rust): code/impl1/replay_corrupt.sh
set -u
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp data/sample/k3.idx data/sample/k3.pc "$d"/
awk '/^K /{n++; if (n == 5) {print "S 20 3ff0000000000000"; print "K hex 0 0"; next}} {print}' data/sample/k3.cert > "$d"/k3.cert
if code/impl1/replay_sample.sh "$d"; then echo "corrupted tree accepted"; exit 1; fi
echo "corrupted tree rejected: PASS"
