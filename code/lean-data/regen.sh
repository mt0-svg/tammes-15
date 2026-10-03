#!/bin/bash
# regen.sh: regenerates the Lean data of D1 and D4 from data/bk15_exact.txt, the witnesses of Tammes15/Params,
# the separations of Tammes15/Nonunique and the generated modules of Tammes15/PaperSteps, and compares them with the
# Lean package.
# Usage, from the repository root: code/lean-data/regen.sh > code/lean-data/regen.out
# The output of each generator is written next to it (d4_cut.out, d1_lp.out, d1_kernel.out, gen_close.out,
# witness.out, pi_witness.out, gen_seplt.out, tie_map.out); the generated files go to a temporary
# directory, and their sha256 are printed.
#  1. d4_cut.sage: every declaration of the generated D4CutProofs.lean (the definitions aN to bh and
#     the lemmas nm_k, ct_k1_k2, sp_k1_k2 and the four sign lemmas) appears exactly once in
#     Tammes15/Attained/*.lean with the same code, and the definitions keepC1, frameC1, keepC3, frameC3
#     of Tammes15/Attained/Data.lean are those of the generated D4Cut.lean. A declaration is compared
#     from its line `[noncomputable ]def|theorem NAME` to the next blank line; the docstrings above it
#     are not compared, since the Lean package words its comments for the repository.
#  2. d1_lp.sage: the linear program is solved again, in floating point (cvxopt); its certificates are
#     compared byte for byte with the committed code/lean-data/d1_lp_cert_C1.txt and C3.txt, which the
#     next step reads. A floating-point solver need not give the same digits on another machine, so a
#     difference here is reported and does not stop the script: the certificate is checked in Lean.
#  3. d1_kernel.sage: from the committed certificates and the frame of data/bk15_exact.txt rounded to
#     2^-100, the integer data Pn, Sn, Lamn, Mun, Vn, Wn, Mkn, RCn, Bn are computed exactly; each line
#     is identical to the one of Tammes15/Kappa/C1.lean and C3.lean.
#  4. gen_frames.sh: the case lists of frameC1_sep, frameC3_sep and frameC3_contact are the proof
#     bodies of these theorems in Tammes15/Attained/Frames.lean.
#  5. gen_close.sh: the rounded frames of Tammes15/Kappa/C1.lean and C3.lean against the enclosures of
#     Tammes15/Kappa/Close.lean (distance at most 2e-20).
#  6. witness.gp, pi_witness.gp (PARI/GP, exact rational arithmetic): each of the eight witnesses that
#     witness.gp prints appears in Tammes15/Params/Checks.lean; the list that pi_witness.gp prints is the one
#     of Tammes15/Params/Pi.lean.
#  7. gen_seplt.sh: Tammes15/Nonunique/SepLt.lean is the file it writes, byte for byte.
#  8. gen_tiedata.sh, tie_map.gp (PARI/GP) and gen_roots2.sh, from data/tie_targets.txt: TieData.lean, TieMap.lean
#     and Roots2.lean of Tammes15/PaperSteps are the files they write, byte for byte (gen_roots2.sh reads the
#     TieMap.lean that tie_map.gp writes); tie_map.gp matches each of the 8 configurations to a frame.
set -u
export LC_ALL=C.UTF-8
D=code/lean-data
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
bad=0
say() { echo "$@"; }
sha() { sha256sum "$1" | cut -c1-16; }
code_block() { # FILE NAME: the lines of the declaration NAME, from its first line to the next blank line
  awk -v n="$2" '
    { s = $0; sub(/^noncomputable /, "", s); split(s, w, " ") }
    !on && (w[1] == "def" || w[1] == "theorem") && w[2] == n { on = 1 }
    on && /^[[:space:]]*$/ { exit }
    on { print }' "$1"
}
say "# code/lean-data/regen.sh, $(date -u '+%Y-%m-%d %H:%M UTC'); SageMath $(sage --version | head -1); PARI/GP $(echo 'print(version())' | gp -q)"
say "# inputs: data/bk15_exact.txt $(sha data/bk15_exact.txt), $D/d1_lp_cert_C1.txt $(sha $D/d1_lp_cert_C1.txt), $D/d1_lp_cert_C3.txt $(sha $D/d1_lp_cert_C3.txt) (sha256, first 16 hex digits)"

say "== 1. d4_cut.sage"
s=$SECONDS; OUT=$T sage $D/d4_cut.sage > $D/d4_cut.out 2>&1 || { say "d4_cut.sage FAILED"; bad=$((bad + 1)); }
say "ran in $((SECONDS - s)) s; generated D4Cut.lean $(sha $T/D4Cut.lean), D4CutProofs.lean $(sha $T/D4CutProofs.lean)"
A=Tammes15/Attained
names=$(grep -E '^(noncomputable )?(def|theorem) ' $T/D4CutProofs.lean | sed -E 's/^noncomputable //' | awk '{print $2}')
ok=0
for n in $names; do
  c=$(grep -hcE "^(noncomputable )?(def|theorem) $n( |$)" $A/*.lean | paste -sd+ | bc)
  if [ "$c" != 1 ]; then say "MISSING or duplicated ($c): $n"; bad=$((bad + 1)); continue; fi
  f=$(grep -lE "^(noncomputable )?(def|theorem) $n( |$)" $A/*.lean)
  if cmp -s <(code_block $T/D4CutProofs.lean "$n") <(code_block "$f" "$n"); then ok=$((ok + 1)); else say "DIFFERS: $n ($f)"; bad=$((bad + 1)); fi
done
say "declarations of D4CutProofs.lean: $(echo "$names" | wc -l); identical in $A: $ok"
for n in keepC1 frameC1 keepC3 frameC3; do
  cmp -s <(code_block $T/D4Cut.lean "$n") <(code_block $A/Data.lean "$n") && say "same as D4Cut.lean: $n" || { say "DIFFERS from D4Cut.lean: $n"; bad=$((bad + 1)); }
done
for f in $A/Data.lean $A/Ident.lean $A/Sep.lean $A/Roots.lean; do say "compared: $f $(sha $f)"; done
# the enclosures [ul, uh] and [bl, bh] of Data.lean contain the 600-bit balls of u and of b (the second
# coordinate of V1) of data/bk15_exact.txt, compared as exact rationals in PARI/GP
enc() { grep "^def $1 " $A/Data.lean | sed 's/.*:= //'; }
ball() { awk -v k="$1" -v f="$2" '$1 == k {print $f}' data/bk15_exact.txt; }
dec() { echo "$1" | awk '{ split($1, p, "."); printf "%s/10^%d", p[1] p[2], length(p[2]) }'; }
sci() { echo "$1" | awk '{ split($1, p, "e"); m = p[1]; split(m, q, "."); printf "(%s/10^%d)*10^(%d)", q[1] q[2], length(q[2]), p[2] }'; }
res=$(echo "u = $(dec $(ball u 2)); ru = $(sci $(ball u 3)); b = $(dec $(ball V1 4)); rb = $(sci $(ball V1 5));
  print([$(dec $(enc ul)) < u - ru, u + ru < $(dec $(enc uh)), $(dec $(enc bl)) < b - rb, b + rb < $(dec $(enc bh))])" | gp -q)
say "balls of u and b of data/bk15_exact.txt inside [ul, uh] and [bl, bh] of Data.lean: $res"
[ "$res" = "[1, 1, 1, 1]" ] || bad=$((bad + 1))

say "== 2. d1_lp.sage"
s=$SECONDS; OUT=$T sage $D/d1_lp.sage > $D/d1_lp.out 2>&1 || { say "d1_lp.sage FAILED"; bad=$((bad + 1)); }
say "ran in $((SECONDS - s)) s"
for c in C1 C3; do
  if cmp -s $T/d1_lp_cert_$c.txt $D/d1_lp_cert_$c.txt; then say "d1_lp_cert_$c.txt: identical to the committed certificate ($(sha $T/d1_lp_cert_$c.txt))"
  else say "d1_lp_cert_$c.txt: DIFFERS from the committed certificate (new $(sha $T/d1_lp_cert_$c.txt)); the next step uses the committed one"
    paste <(grep -v '^#' $T/d1_lp_cert_$c.txt) <(grep -v '^#' $D/d1_lp_cert_$c.txt) |
      awk '{d = $1 - $2; if (d < 0) d = -d; if (d > m) m = d} END {printf "  largest difference of an entry: %.3e\n", m}'
  fi
done

say "== 3. d1_kernel.sage"
s=$SECONDS; OUT=$T sage $D/d1_kernel.sage > $D/d1_kernel.out 2>&1 || { say "d1_kernel.sage FAILED"; bad=$((bad + 1)); }
say "ran in $((SECONDS - s)) s"
for c in C1 C3; do
  n=0
  for v in Pn Sn Lamn Mun Vn Wn Mkn RCn Bn; do
    if cmp -s <(grep -E "^def $v " $T/D1Kernel_$c.lean) <(grep -E "^def $v " Tammes15/Kappa/$c.lean); then n=$((n + 1)); else say "DIFFERS: $v of $c"; bad=$((bad + 1)); fi
  done
  say "$c: generated D1Kernel_$c.lean $(sha $T/D1Kernel_$c.lean); data definitions identical to Tammes15/Kappa/$c.lean ($(sha Tammes15/Kappa/$c.lean)): $n of 9"
done

say "== 4. gen_frames.sh"
for spec in "sep C1" "sep C3" "contact C3"; do
  set -- $spec
  th=frame$2_$1
  if cmp -s <(bash $D/gen_frames.sh $1 $2) <(code_block $A/Frames.lean $th | awk 'p {print} /:= by$/ && !p {p = 1}'); then say "$th: proof body identical to the generated case list"
  else say "$th: DIFFERS from the generated case list"; bad=$((bad + 1)); fi
done
say "compared: $A/Frames.lean $(sha $A/Frames.lean)"

say "== 5. gen_close.sh"
bash $D/gen_close.sh > $D/gen_close.out 2>&1 || { say "gen_close.sh FAILED"; bad=$((bad + 1)); }
grep -q '^layout check .*: OK$' $D/gen_close.out && say "layout of the rounded frames: OK" || { say "layout of the rounded frames: FAIL"; bad=$((bad + 1)); }
grep '^worst' $D/gen_close.out
say "compared: Tammes15/Kappa/Close.lean $(sha Tammes15/Kappa/Close.lean)"

say "== 6. witness.gp, pi_witness.gp"
P=Tammes15/Params
gp -q $D/witness.gp > $D/witness.out 2>&1 || { say "witness.gp FAILED"; bad=$((bad + 1)); }
say "witness.gp: $(grep -cE '^P[0-9a-z]+: OK$' $D/witness.out) checks OK, $(grep -cE ': FAIL$' $D/witness.out) failed"
grep -qE ': FAIL$' $D/witness.out && bad=$((bad + 1))
flat=$(tr -d ' ()' < $P/Checks.lean | sed 's/:ℝ//g')
# the eight rational witnesses; the point b of P7 is 536578502/10^7 degrees in Checks.lean, which P7c checks
n=0; m=0
for v in cU cL cL5 Cu Sl cU7 SU cU8; do
  m=$((m + 1))
  w=$(grep -oE "(^| )$v = [0-9]+/[0-9]+" $D/witness.out | sed 's/.* = //')
  if [ -n "$w" ] && printf '%s\n' "$flat" | grep -qF "$w"; then n=$((n + 1)); else say "witness $v = $w: NOT in $P/Checks.lean"; bad=$((bad + 1)); fi
done
say "witnesses printed by witness.gp found in $P/Checks.lean: $n of $m ($(sha $P/Checks.lean))"
gp -q $D/pi_witness.gp > $D/pi_witness.out 2>&1 || { say "pi_witness.gp FAILED"; bad=$((bad + 1)); }
say "pi_witness.gp: $(grep -c ': OK' $D/pi_witness.out) checks OK, $(grep -c 'FAIL' $D/pi_witness.out) failed"
grep -q FAIL $D/pi_witness.out && bad=$((bad + 1))
if [ "$(sed -n '/^LIST$/{n;p;}' $D/pi_witness.out)" = "$(sed -n 's/^  pi_upper_bound \[\(.*\)\]$/\1/p' $P/Pi.lean)" ]; then
  say "$P/Pi.lean: the list of pi_upper_bound is the one pi_witness.gp prints ($(sha $P/Pi.lean))"
else say "$P/Pi.lean: the list of pi_upper_bound DIFFERS from the one pi_witness.gp prints"; bad=$((bad + 1)); fi

say "== 7. gen_seplt.sh"
sh $D/gen_seplt.sh $T/SepLt.lean > $D/gen_seplt.out 2>&1 || { say "gen_seplt.sh FAILED"; bad=$((bad + 1)); }
sed "s|$T/||" $D/gen_seplt.out > $T/gs && cp $T/gs $D/gen_seplt.out && cat $D/gen_seplt.out
N=Tammes15/Nonunique/SepLt.lean
if cmp -s $T/SepLt.lean $N; then say "$N: identical to the file gen_seplt.sh writes ($(sha $N))"
else say "$N: DIFFERS from the file gen_seplt.sh writes ($(sha $T/SepLt.lean))"; bad=$((bad + 1)); fi

say "== 8. gen_tiedata.sh, tie_map.gp, gen_roots2.sh"
PS=Tammes15/PaperSteps
say "input: data/tie_targets.txt $(sha data/tie_targets.txt)"
bash $D/gen_tiedata.sh data/tie_targets.txt $T/TieData.lean > /dev/null || { say "gen_tiedata.sh FAILED"; bad=$((bad + 1)); }
TIEMAP_IN=data/tie_targets.txt TIEMAP_OUT=$T/TieMap.lean gp -q $D/tie_map.gp < /dev/null > $T/tm 2>&1 || { say "tie_map.gp FAILED"; bad=$((bad + 1)); }
sed "s|$T/||" $T/tm > $D/tie_map.out
say "tie_map.gp: $(grep -c "the 30 contacts go onto those of" $D/tie_map.out) of 8 configurations matched to a frame; $(grep -c "^symbol " $D/tie_map.out) coordinate values"
[ "$(grep -c "the 30 contacts go onto those of" $D/tie_map.out)" = 8 ] || bad=$((bad + 1))
bash $D/gen_roots2.sh $T/Roots2.lean $T/TieMap.lean > /dev/null || { say "gen_roots2.sh FAILED"; bad=$((bad + 1)); }
for f in TieData TieMap Roots2; do
  if cmp -s $T/$f.lean $PS/$f.lean; then say "$PS/$f.lean: identical to the file written ($(sha $PS/$f.lean))"
  else say "$PS/$f.lean: DIFFERS from the file written ($(sha $T/$f.lean 2>/dev/null))"; bad=$((bad + 1)); fi
done

[ $bad = 0 ] && say "REGEN OK" || { say "REGEN FAILED ($bad)"; exit 1; }
