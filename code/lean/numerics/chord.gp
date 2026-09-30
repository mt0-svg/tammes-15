\\ onehex_chord_margin (Tammes15/Rattlers/HexChord.lean; paper, Proposition onehex, inscribed polygon form):
\\ one piece [a, b] = [dpt 0, dpt 10] = [dlo, dhi] of chord_piece_of, with rational bounds at its ends. Every rational
\\ inequality closed by norm_num in the Lean proof is checked here exactly; enclosures as in pieces.gp (Taylor order
\\ NT, PLO <= Pi <= PHI). Reuses the enclosures of Numerics/HexData.lean at the points 0 and 10 and the upper bound
\\ G of tanAng at dpt 10 from piece 9 (recomputed here with the same rule). Output: pieces of Lean text in
\\ chorddata.gen.lean (Numerics/ChordData.lean) and chordproof.gen.lean (the proof of onehex_chord_margin).
default(realprecision, 60);
NT = 10; PLO = 31415926535/10^10; PHI = 31415926536/10^10;
if(!(PLO < Pi && Pi < PHI), error("pi bounds"));
cosT(n, x) = sum(k = 0, n - 1, (-1)^k*x^(2*k)/(2*k)!);
sinT(n, x) = sum(k = 0, n - 1, (-1)^k*x^(2*k+1)/(2*k+1)!);
cosUp(q) = my(x = q*PLO); if(!(0 <= q && q <= 1), error("cosUp range ", q)); cosT(NT, x) + x^(2*NT)/(2*NT)!;
cosLo(q) = my(x = q*PHI); if(!(0 <= q && x <= 3), error("cosLo range ", q)); cosT(NT, x) - x^(2*NT)/(2*NT)!;
sinUp(q) = my(x = q*PHI); if(!(0 <= q && x <= 3/2), error("sinUp range ", q)); sinT(NT, x) + x^(2*NT+1)/(2*NT+1)!;
sinLo(q) = my(x = q*PLO); if(!(0 <= q && q <= 1/2), error("sinLo range ", q)); sinT(NT, x) - x^(2*NT+1)/(2*NT+1)!;
D = 10^9;
up(v) = ceil(v*D + 1)/D;
dn(v) = floor(v*D - 1)/D;
chk(b, msg) = if(!b, error("check failed: ", msg));
deg = Pi/180;
qd(j) = (10731570 + 60275*j)/36000000;
hrad(d) = acos(cos(d)/cos(d/2));
gt(l, h) = acos(-tan(h)*tan(l/2));
q0 = qd(0); q10 = qd(10); a = q0*Pi; b = q10*Pi;
\\ the enclosures of HexData at the points 0 and 10 (same rule as pieces.gp)
C = up(cosUp(q0)); L = dn(cosLo(q0/2)); H = up(cosUp(q0/2));
c = dn(cosLo(q10)); H1 = up(cosUp(q10/2)); H2 = dn(cosLo(q10/2)); S10 = up(sinUp(q10/2));
\\ new enclosures
S0 = dn(sinLo(q0/2)); chk(S0 <= sinLo(q0/2), "S0");
sA = dn(sinLo(q0)); chk(sA <= sinLo(q0), "sA");
\\ sin h(a) >= sigma_a, cos h(b) >= Rb, sin h(b) <= sigma_b
sa = dn(sqrt(1 - C^2/L^2)); chk(0 <= sa && sa^2 <= 1 - C^2/L^2 && C <= L && 0 < L, "sigma_a");
Rb = dn(c/H1); chk(0 <= Rb && Rb*H1 <= c && 0 < c, "Rb");
sb = up(sqrt(1 - Rb^2)); chk(0 <= sb && 1 - Rb^2 <= sb^2, "sigma_b");
\\ Gamma <= tanAng a (hrad a): X_a >= m, -m <= KG <= cos Gamma
ga = gt(a, hrad(a))/deg; Gam = floor((ga - 2/1000)*1000)/1000;
m = dn(sqrt((L^2 - C^2)/C^2*(S0^2/H^2))); chk(0 <= m && m^2 <= (L^2 - C^2)/C^2*(S0^2/H^2) && 0 <= S0, "m");
KG = dn(cosLo(Gam/180)); chk(KG <= cosLo(Gam/180) && -m <= KG && 0 <= Gam && Gam <= 180, "Gamma");
\\ G >= tanAng b (hrad b), as piece 9 of pieces.gp
gb = gt(b, hrad(b))/deg; G = ceil((gb + 2/1000)*1000)/1000;
Gu = up(cosUp(G/180)); M = ceil(sqrt((H1^2 - c^2)/c^2*(S10^2/H2^2))*10^8 + 1)/10^8;
chk((H1^2 - c^2)/c^2*(S10^2/H2^2) <= M^2 && Gu <= -M && G <= 180, "G");
\\ the step bounds
r3 = (180 - Gam)/240; r1 = (180 - Gam)/720; rg = (180 - G)/720;
k3 = dn(cosLo(r3)); k1 = dn(cosLo(r1)); m1 = dn(sinLo(rg));
chk(0 <= k3 && k3 <= cosLo(r3) && 0 <= k1 && k1 <= cosLo(r1) && 0 <= m1 && m1 <= sinLo(rg), "steps");
cB = c;
lhs = sb^2*(1 - sa^2*m1^2); rhs = (Rb*sA*k3 + sa*k1*cB)^2;
chk(lhs < rhs, "hkey");
printf("a = dlo, b = dhi: tanAng(a) = %.6f deg, Gamma = %s deg; tanAng(b) = %.6f deg, G = %s deg\n", ga, Gam, gb, G);
printf("C = %s, L = %s, H = %s, S0 = %s, sA = %s, c = %s, H1 = %s, H2 = %s, S10 = %s\n", C, L, H, S0, sA, c, H1, H2, S10);
printf("sigma_a = %s, Rb = %s, sigma_b = %s, m = %s, KG = %s, M = %s, Gu = %s, k3 = %s, k1 = %s, m1 = %s\n", sa, Rb, sb, m, KG, M, Gu, k3, k1, m1);
printf("hkey: sqrt(lhs) = %.6f < sqrt(rhs) = %.6f, margin %.6f (true E at dhi %.6f)\n", sqrt(lhs), sqrt(rhs), sqrt(rhs) - sqrt(lhs), 0.0727159353);
print("all checks passed");
\\ Lean text
f = "chorddata.gen.lean"; system(Str("rm -f ", f));
lc(name, stmt, lemma, p, sub, un) = write(f, "theorem ", name, " : ", stmt, " := by\n  refine ", lemma, " ", NT, " (p := ", p, ") ", sub, " ?_\n  simp only [", un, ", Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]\n  norm_num");
LOS = "pi_le_hi (by norm_num) (by norm_num)"; SLS = "(by norm_num) pi_ge_lo (by norm_num) (by norm_num)";
lc("le_sin_hdpt_0", Str(S0, " ≤ sin (", q0/2, " * π)"), "le_sin_mul_pi", "3.1415926535", SLS, "sinT");
lc("le_sin_dpt_0", Str(sA, " ≤ sin (", q0, " * π)"), "le_sin_mul_pi", "3.1415926535", SLS, "sinT");
lc("le_cos_chordGam", Str(KG, " ≤ cos (", Gam/180, " * π)"), "le_cos_mul_pi", "3.1415926536", LOS, "cosT");
lc("le_cos_chord3", Str(k3, " ≤ cos (", r3, " * π)"), "le_cos_mul_pi", "3.1415926536", LOS, "cosT");
lc("le_cos_chord1", Str(k1, " ≤ cos (", r1, " * π)"), "le_cos_mul_pi", "3.1415926536", LOS, "cosT");
lc("le_sin_chordG", Str(m1, " ≤ sin (", rg, " * π)"), "le_sin_mul_pi", "3.1415926535", SLS, "sinT");
g = "chordproof.gen.lean"; system(Str("rm -f ", g));
{
write(g, "  have ha : dpt 0 = ", q0, " * π := by unfold dpt; push_cast; ring");
write(g, "  have ha2 : dpt 0 / 2 = ", q0/2, " * π := by rw [ha]; ring");
write(g, "  have hb : dpt 10 = ", q10, " * π := by unfold dpt; push_cast; ring");
write(g, "  have hb2 : dpt 10 / 2 = ", q10/2, " * π := by rw [hb]; ring");
write(g, "  have hπ := Real.pi_pos");
write(g, "  refine chord_piece_of (a := dpt 0) (b := dpt 10) (Γ := ", Gam/180, " * π) (G := ", G/180, " * π) (C := ", C, ") (L := ", L, ") (c := ", c, ") (H1 := ", H1, ") (Rb := ", Rb, ") (σa := ", sa, ") (σb := ", sb, ") (k3 := ", k3, ") (k1 := ", k1, ") (m1 := ", m1, ") (sA := ", sA, ") (cB := ", cB, ")");
write(g, "    (by rw [dpt_zero]) (by rw [dpt_zero]; exact h1) (by rw [dpt_ten]; exact h2) (by rw [dpt_ten]) ?_ (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) ?_ ?_ (by nlinarith) (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num)");
write(g, "  · rw [ha]; exact cos_dpt_le_0");
write(g, "  · rw [ha2]; exact le_cos_hdpt_0");
write(g, "  · rw [hb]; exact le_cos_dpt_10");
write(g, "  · rw [hb2]; exact cos_hdpt_le_10");
write(g, "  · refine le_tanAng_hrad (C := ", C, ") (L := ", L, ") (H := ", H, ") (S := ", S0, ") (m := ", m, ") ?_ ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans (by norm_num) le_cos_chordGam)");
write(g, "    · rw [ha]; exact lt_of_lt_of_le (by norm_num) le_cos_dpt_0");
write(g, "    · rw [ha]; exact cos_dpt_le_0");
write(g, "    · rw [ha2]; exact le_cos_hdpt_0");
write(g, "    · rw [ha2]; exact cos_hdpt_le_0");
write(g, "    · rw [ha2]; exact le_sin_hdpt_0");
write(g, "  · refine tanAng_hrad_le (c := ", c, ") (H1 := ", H1, ") (H2 := ", H2, ") (S := ", S10, ") (M := ", M, ") (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by positivity) (by nlinarith) (le_trans cos_G_le_9 (by norm_num))");
write(g, "    · rw [hb]; exact le_cos_dpt_10");
write(g, "    · rw [hb2]; exact cos_hdpt_le_10");
write(g, "    · rw [hb2]; exact le_cos_hdpt_10");
write(g, "    · rw [hb2, hb]; exact le_trans cos_dpt_le_10 (le_trans (by norm_num) le_cos_hdpt_10)");
write(g, "    · rw [hb2]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)");
write(g, "    · rw [hb2]; exact sin_hdpt_le_10");
write(g, "  · rw [show 3 * ((π - ", Gam/180, " * π) / 2) / 2 = ", r3, " * π by ring]; exact le_cos_chord3");
write(g, "  · rw [show (π - ", Gam/180, " * π) / 4 = ", r1, " * π by ring]; exact le_cos_chord1");
write(g, "  · rw [show (π - ", G/180, " * π) / 4 = ", rg, " * π by ring]; exact le_sin_chordG");
write(g, "  · rw [ha]; exact le_sin_dpt_0");
write(g, "  · rw [hb]; exact le_cos_dpt_10");
}
quit
