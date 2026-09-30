\\ Numerical constants behind Section 3 (faces, rattlers, k <= 3; N = 15).
\\ Run: gp -q code/gp/structure_checks.gp
\\ Every inequality below is checked with a margin far above the working precision;
\\ monotonicity in d (proved in Section 3) reduces each range statement to
\\ finitely many evaluations at subinterval endpoints.
default(parisizemax, 10^8);
default(nbthreads, 1);
\p 60
dg = Pi/180;
dlo = 53.65785*dg; dhi = 56.6716*dg;
alph(d) = acos(cos(d)/(1+cos(d)));
hh(d) = acos(cos(d)/cos(d/2));
\\ perimeter of conv(D(r1,h) u D(r2,h)), |r1 r2| = l, closed form from the tangent construction
Pform(l, h) = 2*acos((cos(l) - sin(h)^2)/cos(h)^2) + 2*sin(h)*(Pi - 2*asin(tan(h)*tan(l/2)));
\\ Crofton: per = 2 Pi - area{n : <n,r1> > sin h, <n,r2> > sin h}
Acap(l, h) = {my(s = sin(h), t1 = acos(s/cos(l/2))); \\ support: |theta| < t1, integrand smooth there
  2*intnum(t = 0, t1, 2*(acos(s/cos(t)) - l/2)*cos(t));}
Pcrof(l, h) = 2*Pi - Acap(l, h);

print("alpha(dlo), alpha(dhi) in deg: ", alph(dlo)/dg, "  ", alph(dhi)/dg);
print("h(dlo), h(dhi) in deg: ", hh(dlo)/dg, "  ", hh(dhi)/dg);
print("2h - d at dlo, dhi (deg): ", (2*hh(dlo)-dlo)/dg, "  ", (2*hh(dhi)-dhi)/dg);
print("2Pi/d range: ", 2*Pi/dhi, " .. ", 2*Pi/dlo, ";  Pi/d range: ", Pi/dhi, " .. ", Pi/dlo);
print("7 dlo - 360 (deg): ", 7*dlo/dg - 360);
print("[3.1] 2Pi - 5 alpha(dhi) (deg, alpha increasing): ", (2*Pi - 5*alph(dhi))/dg);
print("[3.2] Pi(1+sin h(dlo)) - 5 dhi (deg, h increasing): ", (Pi*(1+sin(hh(dlo))) - 5*dhi)/dg);
print("[3.3] d < Pi - 2h at dhi (deg margin): ", (Pi - 2*hh(dhi) - dhi)/dg);
\\ formula check against Crofton at both ends and one interior point
{
foreach([dlo, (dlo+dhi)/2, dhi], d,
  my(h = hh(d)); print("   P formula vs Crofton at d = ", d/dg, ": ", Pform(d,h), "  ", Pcrof(d,h), "  diff ", Pform(d,h)-Pcrof(d,h)));
}
\\ hexagon: P(d, h(d)) > 6 d on the range; P increases in l and in h, both increase with d,
\\ so on [a,b] it suffices that P(a, h(a)) > 6 b.
{
my(K = 40, worst = 10^9, a, b, m);
for(i = 0, K-1, a = dlo + i*(dhi-dlo)/K; b = dlo + (i+1)*(dhi-dlo)/K;
  m = Pform(a, hh(a)) - 6*b; if(m < worst, worst = m));
print("[3.4] min over 40 subintervals of P(a,h(a)) - 6b (deg): ", worst/dg);
print("   P(dlo) - 6 dlo, P(dhi) - 6 dhi (deg): ", (Pform(dlo,hh(dlo)) - 6*dlo)/dg, "  ", (Pform(dhi,hh(dhi)) - 6*dhi)/dg);
}
\\ angle bound: f(a,b) = cos(beta) >= cos(alpha) on [d, Pi/2]^2 (grid sanity check of the calculus proof)
{
localprec(19); foreach([dlo, dhi], d, my(mn = 10, ab, K = 80, f);
  for(i = 0, K, for(j = 0, K,
    my(a = d + i*(Pi/2-d)/K, b = d + j*(Pi/2-d)/K);
    if(abs(a-b) <= d, f = (cos(d) - cos(a)*cos(b))/(sin(a)*sin(b)); if(f < mn, mn = f; ab = [a,b]/dg))));
  print("   min f on grid at d = ", d/dg, ": ", mn, " at ", ab, "; cos alpha = ", cos(alph(d))));
}
