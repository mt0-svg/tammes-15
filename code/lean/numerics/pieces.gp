\\ Proposition onehex, inscribed polygon form (paper, Proposition onehex; Tammes15/Rattlers/HexPoly.lean):
\\ the ten pieces hex_piece_i, each reduced to rational checkpoints by the generic lemmas hex_piece_of,
\\ le_tanLen_hrad, tanAng_hrad_le, le_chordC_hrad (Rattlers/HexPoly.lean) and to rational enclosures of cos and
\\ sin at points q*Pi (Numerics/Taylor.lean: cos_mul_pi_le, le_cos_mul_pi, sin_mul_pi_le at Taylor order NT, with
\\ PLO = 3.1415926535 <= Pi <= PHI = 3.1415926536). Every rational inequality the Lean proofs close by norm_num is
\\ checked here exactly (rational arithmetic); the script stops at the first failure.
\\ Output: the data table on stdout (pieces.out), and the Lean text of the enclosures (Numerics/HexData.lean) and
\\ of the ten piece proofs (written to hexdata.gen.lean and hexpieces.gen.lean, spliced by hand).
default(realprecision, 60);
NT = 10; PLO = 31415926535/10^10; PHI = 31415926536/10^10;
if(!(PLO < Pi && Pi < PHI), error("pi bounds"));
cosT(n, x) = sum(k = 0, n - 1, (-1)^k*x^(2*k)/(2*k)!);
sinT(n, x) = sum(k = 0, n - 1, (-1)^k*x^(2*k+1)/(2*k+1)!);
\\ exact Taylor side conditions, as in the Lean lemmas
cosUp(q) = my(x = q*PLO); if(!(0 <= q && q <= 1), error("cosUp range ", q)); cosT(NT, x) + x^(2*NT)/(2*NT)!;
cosLo(q) = my(x = q*PHI); if(!(0 <= q && x <= 3), error("cosLo range ", q)); cosT(NT, x) - x^(2*NT)/(2*NT)!;
sinUp(q) = my(x = q*PHI); if(!(0 <= q && x <= 3/2), error("sinUp range ", q)); sinT(NT, x) + x^(2*NT+1)/(2*NT+1)!;
D = 10^9;
up(v) = ceil(v*D + 1)/D;
dn(v) = floor(v*D - 1)/D;
chk(b, msg) = if(!b, error("check failed: ", msg));
deg = Pi/180;
qd(j) = (10731570 + 60275*j)/36000000;   \\ dpt j = qd(j) * Pi
hrad(d) = acos(cos(d)/cos(d/2));
Lt(l, h) = acos((cos(l) - sin(h)^2)/cos(h)^2);
gt(l, h) = acos(-tan(h)*tan(l/2));
ch(h, s) = acos(cos(h)^2 + sin(h)^2*cos(s));
\\ point enclosures, j = 0..10: cos(dpt j) in [cl, cu], cos(dpt j / 2) in [hl, hu], sin(dpt j / 2) <= su
cu = vector(11); cl = vector(11); hu = vector(11); hl = vector(11); su = vector(11);
{
for(j = 0, 10, my(q = qd(j));
  cu[j+1] = up(cosUp(q)); cl[j+1] = dn(cosLo(q)); hu[j+1] = up(cosUp(q/2)); hl[j+1] = dn(cosLo(q/2)); su[j+1] = up(sinUp(q/2));
  chk(cosUp(q) <= cu[j+1] && cl[j+1] <= cosLo(q) && cosUp(q/2) <= hu[j+1] && hl[j+1] <= cosLo(q/2) && sinUp(q/2) <= su[j+1], "point");
  chk(cl[j+1] <= cos(q*Pi) && cos(q*Pi) <= cu[j+1] && hl[j+1] <= cos(q*Pi/2) && cos(q*Pi/2) <= hu[j+1] && sin(q*Pi/2) <= su[j+1], "point sanity");
  printf("point %d: q = %s, cos in [%s, %s] (width %.2e), cos half in [%s, %s], sin half <= %s\n", j, q, cl[j+1], cu[j+1], cu[j+1] - cl[j+1], hl[j+1], hu[j+1], su[j+1]));
}
\\ pieces
PC = vector(10);
{
for(i = 0, 9,
  my(qa = qd(i), qb = qd(i + 1), a = qa*Pi, b = qb*Pi, L1, gb, G, sG, chG, m, T1, T2, K1, Gu, Kc, K2, C, L, c, H1, H2, S, M, X2, Y1, Y2);
  L1 = Lt(a, hrad(a))/deg; gb = gt(b, hrad(b))/deg;
  G = ceil((gb + 2/1000)*1000)/1000;                 \\ degrees
  sG = (180 - G)/360;                                \\ the step (2 pi - 2 G)/4 = sG * pi
  chG = ch(hrad(a), sG*Pi)/deg;
  m = 2*L1 + 8*chG - 6*qb*180;
  T1 = floor((L1 - m/8)*100)/100; T2 = floor((chG - m/32)*100)/100;
  \\ checkpoint enclosures
  K1 = dn(cosLo(T1/180)); Gu = up(cosUp(G/180)); Kc = up(cosUp(sG)); K2 = dn(cosLo(T2/180));
  chk(K1 <= cosLo(T1/180) && cosUp(G/180) <= Gu && cosUp(sG) <= Kc && K2 <= cosLo(T2/180), "checkpoints");
  \\ le_tanLen_hrad at a: C = cu, L = hl
  C = cu[i+1]; L = hl[i+1];
  chk(0 < cl[i+1] && 0 < L && C <= L && 0 <= T1/180 && T1/180 <= 1, "tanLen side");
  Y1 = 1 - (1 - C)*L^2/C^2; chk(Y1 <= K1, "tanLen hY");
  \\ tanAng_hrad_le at b: c = cl, H1 = hu, H2 = hl, S = su, cos b <= cos (b/2) from cu <= hl
  c = cl[i+2]; H1 = hu[i+2]; H2 = hl[i+2]; S = su[i+2];
  chk(0 < c && 0 < H2 && cu[i+2] <= hl[i+2], "tanAng side");
  X2 = (H1^2 - c^2)/c^2*(S^2/H2^2); M = ceil(sqrt(X2)*10^8 + 1)/10^8;
  chk(0 <= M && X2 <= M^2 && Gu <= -M && 0 <= G/180 && G/180 <= 1, "tanAng hM hG");
  \\ le_chordC_hrad at a with s = sG * pi: C, L as above
  chk(Kc <= 1 && 0 <= T2/180 && T2/180 <= 1, "chord side");
  Y2 = C^2/L^2 + (1 - C^2/L^2)*Kc; chk(Y2 <= K2, "chord hY");
  \\ hex_piece_of: 6 b < 2 T1 + 8 T2, in units of pi
  chk(6*qb < 2*T1/180 + 8*T2/180, "piece sum");
  PC[i+1] = [T1, G, T2, K1, Gu, Kc, K2, M];
  printf("piece %d: tanLen(a) = %.6f deg, tanAng(b) = %.6f deg, G = %s deg, chord at G = %.6f deg, margin at G %.4f deg; T1 = %s deg, T2 = %s deg, 2 T1 + 8 T2 - 6 b = %.4f deg; slacks: tanLen %.3e, tanAng %.3e (in -cos G - M), chord %.3e\n",
    i, L1, gb, G, chG, m, T1, T2, 2*T1 + 8*T2 - 6*qb*180, (K1 - Y1)*1., (-Gu - M)*1., (K2 - Y2)*1.));
}
print("all checks passed");
\\ Lean text
f = "hexdata.gen.lean"; system(Str("rm -f ", f));
lc(name, stmt, lemma, q, p, sub) = write(f, "theorem ", name, " : ", stmt, " := by\n  refine ", lemma, " ", NT, " (p := ", p, ") ", sub, " ?_\n  simp only [", if(lemma == "sin_mul_pi_le", "sinT", "cosT"), ", Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]\n  norm_num");
UPS = "(by norm_num) pi_ge_lo (by norm_num) (by norm_num)"; LOS = "pi_le_hi (by norm_num) (by norm_num)";
{
for(j = 0, 10, my(q = qd(j));
  lc(Str("cos_dpt_le_", j), Str("cos (", q, " * π) ≤ ", cu[j+1]), "cos_mul_pi_le", q, "3.1415926535", UPS);
  lc(Str("le_cos_dpt_", j), Str(cl[j+1], " ≤ cos (", q, " * π)"), "le_cos_mul_pi", q, "3.1415926536", LOS);
  lc(Str("cos_hdpt_le_", j), Str("cos (", q/2, " * π) ≤ ", hu[j+1]), "cos_mul_pi_le", q/2, "3.1415926535", UPS);
  lc(Str("le_cos_hdpt_", j), Str(hl[j+1], " ≤ cos (", q/2, " * π)"), "le_cos_mul_pi", q/2, "3.1415926536", LOS);
  lc(Str("sin_hdpt_le_", j), Str("sin (", q/2, " * π) ≤ ", su[j+1]), "sin_mul_pi_le", q/2, "3.1415926536", LOS));
}
{
for(i = 0, 9, my(P = PC[i+1], T1 = P[1], G = P[2], T2 = P[3]);
  lc(Str("le_cos_T1_", i), Str(P[4], " ≤ cos (", T1/180, " * π)"), "le_cos_mul_pi", T1/180, "3.1415926536", LOS);
  lc(Str("cos_G_le_", i), Str("cos (", G/180, " * π) ≤ ", P[5]), "cos_mul_pi_le", G/180, "3.1415926535", UPS);
  lc(Str("cos_sG_le_", i), Str("cos (", (180 - G)/360, " * π) ≤ ", P[6]), "cos_mul_pi_le", (180 - G)/360, "3.1415926535", UPS);
  lc(Str("le_cos_T2_", i), Str(P[7], " ≤ cos (", T2/180, " * π)"), "le_cos_mul_pi", T2/180, "3.1415926536", LOS));
}
g = "hexpieces.gen.lean"; system(Str("rm -f ", g));
{
for(i = 0, 9, my(P = PC[i+1], T1 = P[1], G = P[2], T2 = P[3], qa = qd(i), qb = qd(i + 1));
  write(g, "theorem hex_piece_", i, " : 6 * dpt ", i + 1, " < 2 * tanLen (dpt ", i, ") (hrad (dpt ", i, ")) +\n    8 * chordC (hrad (dpt ", i, ")) ((2 * π - 2 * tanAng (dpt ", i + 1, ") (hrad (dpt ", i + 1, "))) / 4) := by");
  write(g, "  have ha : dpt ", i, " = ", qa, " * π := by unfold dpt; push_cast; ring");
  write(g, "  have ha2 : dpt ", i, " / 2 = ", qa/2, " * π := by rw [ha]; ring");
  write(g, "  have hb : dpt ", i + 1, " = ", qb, " * π := by unfold dpt; push_cast; ring");
  write(g, "  have hb2 : dpt ", i + 1, " / 2 = ", qb/2, " * π := by rw [hb]; ring");
  write(g, "  have hπ := Real.pi_pos");
  write(g, "  refine hex_piece_of (T1 := ", T1/180, " * π) (G := ", G/180, " * π) (T2 := ", T2/180, " * π) ?_ ?_ (by nlinarith) ?_ (by rw [hb]; nlinarith)");
  write(g, "  · refine le_tanLen_hrad (C := ", cu[i+1], ") (L := ", hl[i+1], ") (K := ", P[4], ") ?_ ?_ (by norm_num) ?_ (by norm_num) (by positivity) (by nlinarith) le_cos_T1_", i, " (by norm_num)");
  write(g, "    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_", i);
  write(g, "    · rw [ha]; exact cos_dpt_le_", i);
  write(g, "    · rw [ha2]; exact le_cos_hdpt_", i);
  write(g, "  · refine tanAng_hrad_le (c := ", cl[i+2], ") (H1 := ", hu[i+2], ") (H2 := ", hl[i+2], ") (S := ", su[i+2], ") (M := ", P[8], ") (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_", i, " (by norm_num))");
  write(g, "    · rw [hb]; exact le_cos_dpt_", i + 1);
  write(g, "    · rw [hb2]; exact cos_hdpt_le_", i + 1);
  write(g, "    · rw [hb2]; exact le_cos_hdpt_", i + 1);
  write(g, "    · rw [hb2, hb]; exact le_trans cos_dpt_le_", i + 1, " (le_trans (by norm_num) le_cos_hdpt_", i + 1, ")");
  write(g, "    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)");
  write(g, "    · rw [hb2]; exact sin_hdpt_le_", i + 1);
  write(g, "  · have hs : (2 * π - 2 * (", G/180, " * π)) / 4 = ", (180 - G)/360, " * π := by ring");
  write(g, "    rw [hs]");
  write(g, "    refine le_chordC_hrad (C := ", cu[i+1], ") (L := ", hl[i+1], ") (Kc := ", P[6], ") (K := ", P[7], ") ?_ ?_ (by norm_num) ?_ (by norm_num) cos_sG_le_", i, " (by norm_num) (by positivity) (by nlinarith) le_cos_T2_", i, " (by norm_num)");
  write(g, "    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_", i);
  write(g, "    · rw [ha]; exact cos_dpt_le_", i);
  write(g, "    · rw [ha2]; exact le_cos_hdpt_", i);
  if(i < 9, write(g, "")));
}
quit
