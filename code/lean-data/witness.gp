\\ witness.gp: rational witnesses of the Lean proofs of Tammes15/Params/Checks.lean, checked here in exact
\\ rational arithmetic with the same Taylor bounds as Tammes15/Numerics/Taylor.lean:
\\   cosT n x = sum_{k<n} (-1)^k x^(2k)/(2k)!, |cos x - cosT n x| <= |x|^(2n)/(2n)!;
\\   sinT n x = sum_{k<n} (-1)^k x^(2k+1)/(2k+1)!, |sin x - sinT n x| <= |x|^(2n+1)/(2n+1)!.
\\ pi enclosures: plo = 3.14159265358979323846 (Real.pi_gt_d20), phi = 3.14159265358979323847 (Real.pi_lt_d20),
\\ p21 = 3.141592653589793238463 (Tammes15.Params.pi_lt_d21).
\\ Usage, from the repository root: gp -q code/lean-data/witness.gp > code/lean-data/witness.out (code/lean-data/regen.sh
\\ checks that each witness printed is the one of Checks.lean)
default(realprecision, 80);
cosT(n, x) = sum(k = 0, n - 1, (-1)^k * x^(2*k) / (2*k)!);
sinT(n, x) = sum(k = 0, n - 1, (-1)^k * x^(2*k+1) / (2*k+1)!);
cosUp(n, x) = cosT(n, x) + x^(2*n) / (2*n)!;
cosLo(n, x) = cosT(n, x) - x^(2*n) / (2*n)!;
sinUp(n, x) = sinT(n, x) + x^(2*n+1) / (2*n+1)!;
sinLo(n, x) = sinT(n, x) - x^(2*n+1) / (2*n+1)!;
dec(s) = eval(s);
\\ rationals with D decimals, rounded up or down
up(x, D) = ceil(x * 10^D) / 10^D;
dn(x, D) = floor(x * 10^D) / 10^D;
plo = 314159265358979323846 / 10^20; phi = 314159265358979323847 / 10^20; p21 = 3141592653589793238463 / 10^21;
ok(name, b) = print(name, ": ", if(b, "OK", "FAIL"));
qlo = 5365785 / 18000000; qhi = 141679 / 450000;
dloF = 93650615204123937289 / 10^20; dhiF = 98910601237321848052 / 10^20;
aloF = 118952772983819258225 / 10^20; ahiF = 120830549335659207180 / 10^20; shiF = 373170040409990243346 / 10^20;
print("== P1 dlo_file_le: dloF <= qlo * plo");
ok("P1", dloF <= qlo * plo); print("  slack ", (qlo * plo - dloF) * 1.);
print("== P2 dhi_le_file: qhi * phi <= dhiF");
ok("P2", qhi * phi <= dhiF); print("  slack ", (dhiF - qhi * phi) * 1.);
print("== P3 alo_file_le: cos dlo <= cU (cos_mul_pi_le 13, p = plo), cU / (1 + cU) <= cosLo 13 aloF");
n = 13; cU = up(cosUp(n, qlo * plo), 30); print("  cU = ", cU);
ok("P3a", cosUp(n, qlo * plo) <= cU); ok("P3b", cU / (1 + cU) <= cosLo(n, aloF));
print("  slack ", (cosLo(n, aloF) - cU / (1 + cU)) * 1.);
print("== P4 alpha_dhi_le_file: cL <= cos dhi (le_cos_mul_pi 13, p = phi), cosUp 13 ahiF <= cL / (1 + cL)");
cL = dn(cosLo(n, qhi * phi), 30); print("  cL = ", cL);
ok("P4a", cL <= cosLo(n, qhi * phi)); ok("P4b", cosUp(n, ahiF) <= cL / (1 + cL));
print("  slack ", (cL / (1 + cL) - cosUp(n, ahiF)) * 1.);
print("== P5 smax_dhi_le_file: cL5 <= cos dhi (le_cos_mul_pi 13, p = p21), s = shiF / 4, cos s <= Cu, Sl <= sin s, Cu^2 <= cL5 Sl^2");
cL5 = dn(cosLo(n, qhi * p21), 30); s = shiF / 4; Cu = up(cosUp(n, s), 30); Sl = dn(sinLo(n, s), 30);
print("  cL5 = ", cL5, "  Cu = ", Cu, "  Sl = ", Sl);
ok("P5a", cL5 <= cosLo(n, qhi * p21)); ok("P5b", cosUp(n, s) <= Cu); ok("P5c", Sl <= sinLo(n, s));
ok("P5d", Cu^2 <= cL5 * Sl^2); print("  slack ", (cL5 * Sl^2 - Cu^2) * 1.);
print("== P7 arccos_root_lt: b = 268289251/900000000 pi, cos b <= cU7 (cos_mul_pi_le 10, p = plo), quintic cU7 < 0");
qb = 268289251 / 900000000; n7 = 10; cU7 = up(cosUp(n7, qb * plo), 15); print("  cU7 = ", cU7);
quin(u) = 13*u^5 - u^4 + 6*u^3 + 2*u^2 - 3*u - 1;
ok("P7a", cosUp(n7, qb * plo) <= cU7); ok("P7b", quin(cU7) < 0); print("  quintic(cU7) = ", quin(cU7) * 1.);
ok("P7c", qb * 180 == 536578502 / 10000000);
print("== P8 fejesToth_value_lt_dhi: sin (5/26 pi) <= SU (sin_mul_pi_le 10, p = 3.1415926536), cos dhi <= cU8 (cos_mul_pi_le 10, p = 3.1415926535), cU8 < 1 / (2 SU^2) - 1");
n8 = 10; SU = up(sinUp(n8, 5/26 * 31415926536/10^10), 12); cU8 = up(cosUp(n8, qhi * 31415926535/10^10), 12);
print("  SU = ", SU, "  cU8 = ", cU8);
ok("P8a", sinUp(n8, 5/26 * 31415926536/10^10) <= SU); ok("P8b", cosUp(n8, qhi * 31415926535/10^10) <= cU8);
ok("P8c", cU8 < 1 / (2 * SU^2) - 1); print("  slack ", (1 / (2 * SU^2) - 1 - cU8) * 1.);
print("== check against floating point: pi = ", Pi, "; dlo = ", qlo * Pi, "; alpha(dlo) = ", acos(cos(qlo*Pi) / (1 + cos(qlo*Pi))));
print("   smax(dhi) = ", 4 * atan(1 / sqrt(cos(qhi * Pi))), " shi = ", shiF * 1.);
quit;
