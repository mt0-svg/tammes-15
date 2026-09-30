\\ Rigorous constants for the level-1 linear system of the Tammes contact graph filter.
\\ Usage: gp -q consts.gp with DLO, DHI (degrees, exact rationals) set before reading, e.g.
\\   echo 'DLO=571367/10000; DHI=585/10; read("consts.gp")' | gp -q > params13.txt
\\ Every printed bound is rounded outward at 1e-20 from a 100-digit evaluation; the Rust side
\\ nudges the parsed f64 one more ulp outward.
\p 100
default(parisizemax, 256000000);
alpha(d) = acos(cos(d)/(1+cos(d)));
\\ rhombus with side d and angle u: the other angle
rho(u,d) = 2*atan(1/(tan(u/2)*cos(d)));
rhop(u,d) = my(k=cos(d), t=tan(u/2)); -k*(1+t^2)/(1+k^2*t^2);
\\ maximal angle sum u1+u2 of a rhombus with side d (attained at u1 = u2)
smax(d) = 4*atan(1/sqrt(cos(d)));
dn(x) = floor(x*10^20)/10^20;
upr(x) = ceil(x*10^20)/10^20;
pr(key, q) = print(key, " ", strprintf("%.20f", q));
{
  my(dlo = DLO*Pi/180, dhi = DHI*Pi/180, alo, ahi, shi, K = 12);
  alo = alpha(dlo); ahi = alpha(dhi); shi = smax(dhi);
  print("# dlo_deg ", strprintf("%.10f", DLO*1.), "  dhi_deg ", strprintf("%.10f", DHI*1.));
  pr("dlo", dn(dlo)); pr("dhi", upr(dhi));
  pr("alo", dn(alo)); pr("ahi", upr(ahi));
  pr("shi", upr(shi));
  \\ tangent cuts y - c*x <= c0, valid for every rhombus angle pair (x, y) with d <= dhi,
  \\ x in [alo, 2 ahi]: rho(., dhi) is concave, rho increasing in d.
  for (k = 0, K,
    my(x0 = alo + k*(2*ahi - alo)/K, c = round(rhop(x0, dhi)*10^4)/10^4, xs, c0);
    if (rhop(alo, dhi) <= c, xs = alo,
      if (rhop(2*ahi, dhi) >= c, xs = 2*ahi,
        xs = solve(x = alo, 2*ahi, rhop(x, dhi) - c)));
    c0 = rho(xs, dhi) - c*xs + 10^-15;
    print("cut ", strprintf("%.4f", c*1.), " ", strprintf("%.20f", upr(c0))));
}
