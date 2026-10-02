#!/bin/bash
# The rounded frames of the certificates against the exact frames: the entries of C1.Pn and C3.Pn
# minus 2^101 are, up to sign, nine integers Q_X = 2^100 x rounded, one per numerator X of
# Tammes15.Attained.ptN (a b c d e f r s t), placed as in ptN (keepC1, keepC3); and each Q_X / 2^100
# lies within 2e-20 of every point of the enclosure [L_X, H_X] of X / 225008 (encl_XN of Close.lean).
# Checks both in PARI/GP and prints the Lean text of the constants and tables.
# Usage: code/lean-data/gen_close.sh   (from the repository root); record: code/lean-data/gen_close.out
set -eu
cd "$(dirname "$0")/../.."
t=$(mktemp -d)
for c in C1 C3; do grep '^def Pn' Tammes15/Kappa/$c.lean | sed 's/^def Pn : List (List Nat) := //' > $t/Pn_$c.gp; done
grep -A1 '^theorem encl_' Tammes15/Kappa/Close.lean | grep '225008' |
  sed -E 's/.*\(225008 : ℝ\) \* (-?)0\.([0-9]{40}) ≤ ([a-z])N b u ∧ [a-z]N b u ≤ \(225008 : ℝ\) \* (-?)0\.([0-9]{40}) := by/[\1\2\/10^40, \4\5\/10^40]/' |
  paste -sd, | sed 's/^/E = [/; s/$/];/' > $t/encl.gp
cat > $t/main.gp <<'GP'
\\ ptN layout: rows 0..17, entries (sign, letter) with letters 1..9 = a b c d e f r s t
lay = [[1,2,3],[3,1,2],[2,3,1],[4,5,6],[6,4,5],[5,6,4],[7,8,9],[9,7,8],[8,9,7],[-9,-8,-7],[-7,-9,-8],[-8,-7,-9],[-6,-5,-4],[-5,-4,-6],[-4,-6,-5],[-3,-2,-1],[-2,-1,-3],[-1,-3,-2]];
keep = [[0,1,2,3,4,5,6,7,10,12,13,14,15,16,17], [0,1,2,3,4,5,6,7,8,12,13,14,15,16,17]];
names = ["A","B","C","D","E","F","R","S","T"];
P = [eval(read(Pfile1)), eval(read(Pfile3))];
o = 2^101;
\\ Q_X from C3 rows 0, 3, 6 (keep indices 0, 3, 6)
Q = [P[2][1][1],P[2][1][2],P[2][1][3],P[2][4][1],P[2][4][2],P[2][4][3],P[2][7][1],P[2][7][2],P[2][7][3]] - vector(9,j,o);
ok = 1;
for(f=1,2, for(i=1,15, for(m=1,3, my(l=lay[keep[f][i]+1][m]); if(P[f][i][m]-o != sign(l)*Q[abs(l)], ok=0; print("MISMATCH frame ",f," i=",i-1," m=",m-1)))));
print("layout check (all 90 entries of C1.Pn and C3.Pn are the signed Q_X of ptN): ", if(ok,"OK","FAIL"));
d = 2/10^20; worst = 0;
{for(j=1,9, my(q=Q[j]/2^100, L=E[j][1], H=E[j][2], s=max(q-L, H-q));
  worst = max(worst, s);
  printf("%s: max over [L,H] of |x - Q/2^100| = %.6e  (<= 2e-20: %s)\n", names[j], s*1., if(s<=d,"yes","NO")))};
printf("worst %.6e, margin to 2e-20: %.6e\n", worst*1., (d-worst)*1.);
print("-- Lean text");
for(j=1,9, print("def Q", names[j], " : ℤ := ", Q[j]));
tab(f) = { my(s="![");
  for(i=1,15, my(r="!["); for(m=1,3, my(l=lay[keep[f][i]+1][m]); r = concat(r, concat(if(l<0,"-Q","Q"), names[abs(l)])); if(m<3, r=concat(r,", "))); r=concat(r,"]"); s=concat(s,r); if(i<15, s=concat(s,", ")));
  concat(s,"]") };
{my(s="![");
  for(k=1,18, my(r="!["); for(m=1,3, my(l=lay[k][m]); r = concat(r, concat(if(l<0,"-Q","Q"), names[abs(l)])); if(m<3, r=concat(r,", "))); r=concat(r,"]"); s=concat(s,r); if(k<18, s=concat(s,", ")));
  print("def Qall : Fin 18 → Fin 3 → ℤ := ", s, "]")};
print("def QtabC1 : Fin 15 → Fin 3 → ℤ := ", tab(1));
print("def QtabC3 : Fin 15 → Fin 3 → ℤ := ", tab(2));
GP
gp -q -D parisize=100000000 <<GPIN
Pfile1 = "$t/Pn_C1.gp"; Pfile3 = "$t/Pn_C3.gp";
read("$t/encl.gp");
read("$t/main.gp");
GPIN
rm -rf $t
