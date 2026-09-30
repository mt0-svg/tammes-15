#!/bin/bash
# Compares the pass-1 probe outputs (verify/d3check/l2) with the recorded bulk pass 1 (verify/l2):
# 1. default mode against the recorded lines of the same graphs, every field but the seconds and the
#    LP counter (printed from bin_v4 on, always 0 without --lp)
#    (field 5); a line that differs is listed; a planted change (negative control) must be found;
# 2. relsys against default, graph by graph: verdicts, nodes, seconds.
# Usage: ./compare_pass1.sh   Output: compare_pass1.out
cd "$(dirname "$0")"
D=${T15:?see README.md}/verify/d3check/l2
R=${T15:?see README.md}/verify/l2
# same(A, B): lines of A whose graph has a line in B that differs outside field 5
same() { awk 'NR == FNR { gsub(/ LP=[0-9]+/, ""); k = $1; $5 = ""; rec[k] = $0; next } { gsub(/ LP=[0-9]+/, ""); k = $1; $5 = ""; if (!(k in rec)) print "missing " k; else if (rec[k] != $0) print "differs " k }' "$2" "$1"; }
{
  for p in "p1_k0 k0_0" "p1_k1 k1_0" "p1_k2 k2" "p1_k3 k3"; do
    set -- $p; name=$1; rec=$R/$2.out
    def=$D/${name}_default.out; rel=$D/${name}_relsys.out
    [ -s $def ] && [ -s $rel ] || { echo "$name: outputs missing"; continue; }
    echo "== $name: default $(cat $D/${name}_default.time | paste -sd' '), relsys $(cat $D/${name}_relsys.time | paste -sd' ')"
    echo "default rerun against the recorded run ($rec):"
    same $def $rec > /tmp/d3cmp.$$
    echo "  graphs $(wc -l < $def), lines differing or missing $(wc -l < /tmp/d3cmp.$$)"
    while read -r what k; do
      echo "  $what $k: rerun: $(awk -v k=$k '$1 == k' $def | cut -c1-200)"
      echo "  $what $k: recorded: $(awk -v k=$k '$1 == k' $rec | cut -c1-200)"
    done < /tmp/d3cmp.$$
    nb=0
    while read -r what k; do
      a=$(awk -v k=$k '$1 == k {print $2}' $def); b=$(awk -v k=$k '$1 == k {print $2}' $rec)
      [ "$a" != BUDGET ] && [ "$b" != BUDGET ] && nb=$((nb + 1))
    done < /tmp/d3cmp.$$
    echo "  differing lines with no BUDGET verdict on either side (the 5 s limit is wall clock): $nb"
    # negative control: change the node count of the first line, the comparison must see it
    awk 'NR == 1 { $4 = $4 + 1 } { print }' $def > /tmp/d3plant.$$
    k0=$(head -n 1 $def | cut -d" " -f1)
    echo "  negative control (node count of graph $k0 changed by 1 in a copy): graph $k0 reported $(same /tmp/d3plant.$$ $rec | grep -c "^differs $k0\$") time(s)"
    echo "verdicts default: $(awk '{print $2}' $def | sort | uniq -c | paste -sd' ')"
    echo "verdicts relsys: $(awk '{print $2}' $rel | sort | uniq -c | paste -sd' ')"
    echo "seconds (sum of field 5) default $(awk '{s += $5} END {printf "%.2f", s}' $def) relsys $(awk '{s += $5} END {printf "%.2f", s}' $rel); nodes default $(awk '{s += $4} END {print s}' $def) relsys $(awk '{s += $4} END {print s}' $rel)"
    echo "graphs KILLED by default and not by relsys (index, relsys line):"
    awk 'NR == FNR { v[$1] = $2; next } v[$1] == "KILLED" && $2 != "KILLED" { print "  " substr($0, 1, 240) }' $def $rel
    x=$(awk 'NR == FNR { v[$1] = $2; next } v[$1] != "KILLED" && $2 == "KILLED" { print $1 }' $def $rel | paste -sd" ")
    echo "graphs KILLED by relsys and not by default: ${x:-none}"
  done
  rm -f /tmp/d3cmp.$$ /tmp/d3plant.$$
} > compare_pass1.out
cat compare_pass1.out
