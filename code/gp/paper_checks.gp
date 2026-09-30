\\ Short checks shown in the paper. Run: gp -q paper_checks.gp < /dev/null
default(realprecision, 60);
\\ [1] Theorem 1.1: the quintic, its root u, psi* = acos u in degrees.
f = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
u = polrootsreal(f)[1];
print([polisirreducible(f), #polrootsreal(f), subst(f,x,1/2) < 0, subst(f,x,7/10) > 0]);
printf("u = %.20f, psi* = %.14f deg\n", u, acos(u)*180/Pi);
\\ [2] Section 3: the range [dlo, dhi] and the bound of Fejes Toth.
deg = Pi/180; dlo = 53.65785*deg; dhi = 56.6716*deg; w = Pi*15/(6*15-12);
dft = acos((cotan(w)^2 - 1)/2);
printf("dlo < psi*: %d, FT = %.10f deg < dhi: %d\n", dlo < acos(u), dft/deg, dft < dhi);
\\ [3] Section 3.4: the margins of the structure theorem, in degrees.
al(d) = acos(cos(d)/(1+cos(d)));
h(d) = acos(cos(d)/cos(d/2));
P(l,t) = 2*acos((cos(l)-sin(t)^2)/cos(t)^2) + 2*sin(t)*(Pi - 2*asin(tan(t)*tan(l/2)));
m = vector(40, i, my(a = dlo+(i-1)*(dhi-dlo)/40, b = dlo+i*(dhi-dlo)/40); P(a,h(a)) - 6*b);
printf("%.2f %.2f %.2f %.2f\n", (7*dlo-2*Pi)/deg, 72-al(dhi)/deg, \
  (Pi-2*h(dhi)-dhi)/deg, vecmin(m)/deg);
quit;
