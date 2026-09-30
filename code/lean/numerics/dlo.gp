\\ dlo < psi* = arccos u (Tammes15/Hyps/Interfaces.lean, dlo_lt_arccos_root).
\\ u: the root in (1/2, 7/10) of 13u^5 - u^4 + 6u^3 + 2u^2 - 3u - 1; dlo = 5365785/100000 deg = q pi, q = 5365785/18000000.
\\ Lean route: u < c (quintic c > 0, quintic increasing on (1/2, 7/10)), c < cos dlo from le_cos_mul_pi with
\\ p = 3.14159265358979323847 (Real.pi_lt_d20) and n Taylor terms: c <= cosT n (q p) - (q p)^(2n)/(2n)!.
default(realprecision, 80);
Q(x) = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
u = polrootsreal(Q(x))[1]; print("real roots: ", polrootsreal(Q(x)));
q = 5365785/18000000; p = 31415926536/10^10; \\ p >= pi from Real.pi_lt_d20
print("u = ", u); print("cos dlo = ", cos(q*Pi)); print("cos dlo - u = ", cos(q*Pi) - u);
print("psi* - dlo (deg) = ", acos(u)*180/Pi - 5365785/100000);
cosT(n, x) = sum(k = 0, n - 1, (-1)^k*x^(2*k)/(2*k)!);
for(n = 8, 12, my(x = q*p, lo = cosT(n, x) - x^(2*n)/(2*n)!); print("n = ", n, ": (cosT - rem at q p) - cos dlo = ", (lo - cos(q*Pi))*1.));
c = 592605904/10^9; print("c = ", c, ": Q(c) = ", Q(c)*1., " (> 0 needed), c - u = ", c - u, ", cosT(10) - rem - c = ", (cosT(10, q*p) - (q*p)^20/20! - c)*1.);
c2 = 592605903/10^9; print("c2 = ", c2, " (le_cos_dpt_0 of Numerics/HexData.lean): Q(c2) = ", Q(c2)*1., " (> 0 needed), c2 - u = ", (c2 - u)*1., ", Q(c2) > 0 exactly: ", Q(c2) > 0);
\\ the monotonicity of Q on (1/2, 7/10): Q'(x) = 65x^4 - 4x^3 + 18x^2 + 4x - 3 > 0 there
print("Q'(1/2) = ", subst(Q(x)', x, 1/2), ", min of Q' on [1/2, 7/10] (sampled) = ", vecmin(vector(201, i, subst(Q(x)', x, 1/2 + (i - 1)/1000))));
quit
