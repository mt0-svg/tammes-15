#!/bin/bash
# Counts the Edge refutations (field E= of each case record) in every recorded vkill output:
# the bulk sweep (verify/l2) and the per-graph passes (verify/cases). Output: edge_count.out.
cd "$(dirname "$0")"
V=${T15:?see README.md}/verify
{
  echo "# E= values over the case records of $V/l2/*.out"
  cat $V/l2/*.out | grep -o " E=[0-9]*" | sort | uniq -c
  echo "# E= values over the case records of $V/cases/*/*.txt"
  cat $V/cases/*/*.txt | grep -o " E=[0-9]*" | sort | uniq -c
} > edge_count.out
cat edge_count.out
