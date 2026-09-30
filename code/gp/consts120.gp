\\ Independent recomputation of the constants of the reduction (Sections 2 to 4).
\\ PARI/GP floating point at 120 digits; margins are printed so that their size can be judged.
default(parisizemax, 512000000);
default(nbthreads, 1);
\p 120
deg = Pi/180;
q(x) = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
\\ uniqueness of the root in (1/2, 7/10): Sturm count
print("real roots of q in [1/2, 7/10]: ", polsturm(q('x), [1/2, 7/10]));
u = solve(x = 1/2, 7/10, q(x));
psis = acos(u);
print("u = ", u);
print("psi* (deg) = ", psis/deg);
print("psi* - 53.65785 deg (deg) = ", psis/deg - 53.65785);
print("53.6578502 - psi* (deg) = ", 53.6578502 - psis/deg);
w = 15*Pi/78;
ft = acos((cotan(w)^2 - 1)/2);
print("Fejes Toth bound (deg) = ", ft/deg);
print("56.6716 - FT (deg) = ", 56.6716 - ft/deg);
dlo = 53.65785*deg; dhi = 56.6716*deg;
print("params15ft dlo - true (rad, must be <= 0): ", 0.93650615204123937289 - dlo);
print("params15ft dhi - true (rad, must be >= 0): ", 0.98910601237321848052 - dhi);
alpha(d) = acos(cos(d)/(1 + cos(d)));
S(d) = 4*atan(1/sqrt(cos(d)));
print("alo - alpha(dlo) (<= 0): ", 1.18952772983819258225 - alpha(dlo));
print("ahi - alpha(dhi) (>= 0): ", 1.20830549335659207180 - alpha(dhi));
print("shi - S(dhi) (>= 0): ", 3.73170040409990243346 - S(dhi));
print("alpha(dlo), alpha(dhi) (deg): ", alpha(dlo)/deg, "  ", alpha(dhi)/deg);
print("6 alpha(dlo) - 360 (deg): ", 6*alpha(dlo)/deg - 360);
print("7 dlo - 360 (deg): ", 7*dlo/deg - 360);
print("2 pi/d on the range: [", 2*Pi/dhi, ", ", 2*Pi/dlo, "];  pi/d: [", Pi/dhi, ", ", Pi/dlo, "]");
print("5 alpha(dhi) - 360 (deg, all-triangle degree-5 vertex): ", 5*alpha(dhi)/deg - 360);
\\ Proposition 3.3
h(d) = acos(cos(d)/cos(d/2));
print("h(dlo), h(dhi) (deg): ", h(dlo)/deg, "  ", h(dhi)/deg);
print("Prop 3.16: 72 - alpha(dhi) (deg): ", 72 - alpha(dhi)/deg);
print("Prop 3.16: pi(1 + sin h(dlo)) - 5 dhi (deg): ", (Pi*(1 + sin(h(dlo))) - 5*dhi)/deg);
\\ check f(a,b) >= cos alpha(d) on [d, pi/2]^2 by a grid (sanity only; the proof is analytic)
{
  my(mn = 10, d, a, b, f, N = 60);
  forstep(dd = 0, 1, 1/4,
    d = dlo + dd*(dhi - dlo);
    for(i = 0, N, for(j = 0, N,
      a = d + i*(Pi/2 - d)/N; b = d + j*(Pi/2 - d)/N;
      f = (cos(d) - cos(a)*cos(b))/(sin(a)*sin(b)) - cos(alpha(d));
      mn = min(mn, f))));
  print("Prop 3.16 grid: min of f(a,b) - cos alpha(d) = ", mn);
}
\\ Proposition 3.4: P(l, h) by the closed form and by the Crofton integral
Pc(l, hh) = 2*acos((cos(l) - sin(hh)^2)/cos(hh)^2) + 2*sin(hh)*(Pi - 2*asin(tan(hh)*tan(l/2)));
Pi_(l, hh) = my(t1 = acos(sin(hh)/cos(l/2))); 2*Pi - 2*intnum(t = 0, t1, 2*(acos(sin(hh)/cos(t)) - l/2)*cos(t));
{
  foreach([dlo, (dlo + dhi)/2, dhi], d,
    print("P closed form - Crofton at d = ", d/deg, ": ", Pc(d, h(d)) - Pi_(d, h(d))));
}
print("Prop 3.17 side condition pi - 2h(dhi) - dhi (deg): ", (Pi - 2*h(dhi) - dhi)/deg);
print("Prop 3.17 single interval P(dlo,h(dlo)) - 6 dhi (deg): ", (Pc(dlo, h(dlo)) - 6*dhi)/deg);
{
  foreach([10, 20, 40, 200], N,
    my(mn = 1000, a, b);
    for(i = 0, N - 1,
      a = dlo + i*(dhi - dlo)/N; b = dlo + (i + 1)*(dhi - dlo)/N;
      mn = min(mn, (Pc(a, h(a)) - 6*b)/deg));
    print("Prop 3.17 with ", N, " subintervals: min P(a,h(a)) - 6b = ", mn, " deg"));
}
\\ monotonicity of P in l and h (numerical derivative signs on a grid)
{
  my(mn1 = 1, mn2 = 1, d, e = 1e-30);
  for(i = 0, 40, d = dlo + i*(dhi - dlo)/40;
    mn1 = min(mn1, (Pc(d + e, h(d)) - Pc(d, h(d)))/e);
    mn2 = min(mn2, (Pc(d, h(d) + e) - Pc(d, h(d)))/e));
  print("min dP/dl, dP/dh on the range: ", mn1, "  ", mn2);
}
\\ Corollary 3.5: k <= 3
print("Cor 3.18: 3k <= 11 gives k <= ", floor(11/3));
\\ radius of Theorem 4.1 from kappa (C1 type, the smaller one)
{
  foreach([6.4980e-3, 6.8142e-3], kap,
    print("kappa = ", kap, ": radius kappa/((1+u)*1.01*sqrt(15)) = ", kap/((1 + u)*1.01*sqrt(15))));
  print("s_k bound: 15 r^2 at r = 1.04e-3: ", 15*(1.04e-3)^2, "  factor 1/(1 - 15r^2/4) = ", 1/(1 - 15*(1.04e-3)^2/4));
}
