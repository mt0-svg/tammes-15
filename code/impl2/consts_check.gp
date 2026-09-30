\\ Independent check of the constants of code/impl2/src/consts.rs (PARI/GP, 200 digits).
\\ psis* = acos(u), u the root in (0.5, 0.7) of 13x^5 - x^4 + 6x^3 + 2x^2 - 3x - 1 (Section 2);
\\ Fejes Toth bound for N = 15: acos((cot(w)^2 - 1)/2), w = N pi / (6 (N - 2)).
default(realprecision, 200);
default(parisizemax, 200000000);
default(nbthreads, 1);
P = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
r = [z | z <- polrootsreal(P), z > 1/2 && z < 7/10];
if (#r != 1, error("root count"));
u = r[1];
psis = acos(u) * 180 / Pi;
w = 15 * Pi / (6 * 13);
ft = acos((cotan(w)^2 - 1) / 2) * 180 / Pi;
printf("psi* = %.30f deg\n", psis);
printf("FT(15) = %.30f deg\n", ft);
printf("psi* - 53.65785 = %.6e (must be > 0)\n", psis - 53.65785);
printf("56.6716 - FT = %.6e (must be > 0)\n", 56.6716 - ft);
\\ the f64 values printed by vkill (exact decimal expansions of the doubles are compared)
dlo = 53.65785 * Pi / 180; dhi = 56.6716 * Pi / 180;
alpha(d) = acos(cos(d) / (1 + cos(d)));
printf("dlo = %.25f rad, dhi = %.25f rad\n", dlo, dhi);
printf("alpha(dlo) = %.25f, alpha(dhi) = %.25f\n", alpha(dlo), alpha(dhi));
\\ vkill prints its range as doubles; they must enclose [dlo, dhi] and [alpha(dlo), alpha(dhi)]
vd = [9.36506152041239104e-1, 9.89106012373218935e-1, 1.18952772983819077e0, 1.20830549335659398e0];
printf("vkill dlo below: %d, dhi above: %d, alo below: %d, ahi above: %d\n", vd[1] < dlo, vd[2] > dhi, vd[3] < alpha(dlo), vd[4] > alpha(dhi));
