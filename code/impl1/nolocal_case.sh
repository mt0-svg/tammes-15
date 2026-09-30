#!/bin/sh
# Negative control of the first implementation (Section 6.6): four realised cases searched without Local,
# with the options of the recorded no-Local runs (code/impl1/out/nolocal_*.txt): the contact graphs of C1
# and C3 (case 0 of data/truth/c1_real.pc and c3_real.pc) and two cases with a rattler (case 4 of
# c1_realv.pc, case 0 of c3_realv4.pc), on d from d_lo to 53.6578502 deg. Each has a genuine realisation
# at d = psi*, so none may be KILLED; each line must also equal the line of the recorded run.
# Usage (from the repository root, after building code/impl1/rust): code/impl1/nolocal_case.sh
# Prints the verdict lines (times removed) and exits 0 when no case is KILLED and every line is the
# recorded one.
set -u
T=code/impl1/rust/target/release/tdeep
st=0
for spec in "c1_real 0 0 nolocal_c1_real_part" "c3_real 0 0 nolocal_c3_real" "c1_realv 1 4 nolocal_c1_realv" "c3_realv4 1 0 nolocal_c3_realv4"; do
  set -- $spec
  l=$($T data/params15ft.txt --no-face --no-cuts --dhi 53.6578502 --shave 8 --pair --stopunres 1 --nodes 3000 \
    --iso "$2" --only "$3" < "data/truth/$1.pc" 2> /dev/null | sed 's/ t=[0-9.]*//')
  echo "$1 case $3: $l"
  case $l in *" KILLED "*) echo "$1 case $3: KILLED"; st=1 ;; esac
  r=$(grep "^$3 " "code/impl1/out/$4.txt" | sed 's/ t=[0-9.]*//')
  [ "$l" = "$r" ] || { echo "$1 case $3: differs from code/impl1/out/$4.txt"; st=1; }
done
[ $st = 0 ] && echo "no realised case KILLED without Local, every line as recorded: PASS" || { echo "FAIL"; exit 1; }
