#!/bin/bash
# Reruns vkill on the graphs left by its two bulk passes (Section 6.5), with the options and d ranges of
# code/impl2/residue_cases.txt, and compares verdict and node count with the recorded ones (the search is
# deterministic, so a rerun gives the recorded node count).
# Usage (from the repository root, after building code/impl2): code/impl2/residue_rerun.sh [TAG ...]
#   (default: every run of residue_cases.txt); JOBS runs in parallel (default 1).
# Prints, per run, the verdict line and the summary line of vkill, then the comparison. Exit status 0
# when every run gives KILLED with the recorded node count.
set -u
V=code/impl2/target/release/vkill
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
[ $# -eq 0 ] && set -- $(grep -v '^#' code/impl2/residue_cases.txt | cut -d' ' -f1)
export V W
printf '%s\n' "$@" | xargs -P "${JOBS:-1}" -I{} bash -c '
  set -- $(grep "^{} " code/impl2/residue_cases.txt)
  tag=$1 f=$2 idx=$3 iso=$4 lo=$5 hi=$6 nodes=$7; shift 7
  r=(); [ "$lo" != dlo ] && r+=(--dlo "$lo"); [ "$hi" != dhi ] && r+=(--dhi "$hi")
  $V "$f" --iso "$iso" --only "$idx" --targets data/tie_targets.txt --local --pair --edge \
    --nodes 100000000 --maxsec 5000 "${r[@]}" "$@" > "$W/$tag.out" 2> "$W/$tag.err"
  { echo "== $tag: $V $f --iso $iso --only $idx --local --pair --edge ${r[*]} $*"
    cat "$W/$tag.out"; tail -n 1 "$W/$tag.err"
    got=$(awk "NR == 1 {print \$2, \$4}" "$W/$tag.out")
    if [ "$got" = "KILLED $nodes" ]; then echo "$tag: KILLED, $nodes nodes as recorded"; else echo "$tag: DIFFERENT: $got, recorded KILLED $nodes"; fi
  } > "$W/$tag.txt"'
bad=0
for t in "$@"; do cat "$W/$t.txt"; grep -q "^$t: KILLED, .* as recorded$" "$W/$t.txt" || bad=1; done
[ $bad = 0 ] && echo "residue reruns ($#): PASS" || { echo "residue reruns: FAIL"; exit 1; }
