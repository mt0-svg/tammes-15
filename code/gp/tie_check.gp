\\ The targets of Local (data/tie_targets.txt) against the frame of Section 2 of the paper, rebuilt from its
\\ formulas at 100 digits, in floating point (not in interval arithmetic).
\\ Checks: every target point encloses (per coordinate, midpoint and radius of the file) a frame
\\ point; the 15 points are distinct frame points keeping one point of each toggle pair; the 30
\\ listed contacts have inner product u; every other pair is below u - 0.1679; the types C1, C3.
\\ Run from this directory: gp -q tie_check.gp < /dev/null > tie_check.out
default(realprecision, 100);
REL = "../../data/";
u = select(t -> t > 1/2 && t < 7/10, polrootsreal(13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1))[1];
Q = 9*(4*u^2-u-1)*(3*u+1)^2*y^2 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*y + u^2*(4*u^2-u-1)*(5*u-1)^2;
be = select(t -> abs(t - 0.0294089) < 1e-4, polrootsreal(Q))[1];
b = sqrt(be);
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u));
a = (u - b*c)/(b + c);
q = [((2*a-b+2*c)*u-b)/(u+1), ((2*a+2*b-c)*u-c)/(u+1), ((-a+2*b+2*c)*u-a)/(u+1)];
r = [((6*a+3*b-2*c)*u^2+2*(a-b-c)*u-b)/(u+1)^2, ((3*c-2*a+6*b)*u^2+2*(b-c-a)*u-c)/(u+1)^2, ((3*a-2*b+6*c)*u^2+2*(c-a-b)*u-a)/(u+1)^2];
rh(p) = [p[3], p[1], p[2]];
ta(p) = [-p[3], -p[2], -p[1]];
pV = [a, b, c]; pW = q; pT = r;
\\ rows 1 to 18 of Table 1
F = [pV, rh(pV), rh(rh(pV)), pW, rh(pW), rh(rh(pW)), pT, rh(pT), rh(rh(pT)), ta(pT), rh(ta(pT)), rh(rh(ta(pT))), ta(pW), rh(rh(ta(pW))), rh(ta(pW)), ta(pV), rh(rh(ta(pV))), rh(ta(pV))];
dot(v, w) = sum(k = 1, 3, v[k]*w[k]);
printf("frame: a^2+b^2+c^2-1 = %.2e, ab+bc+ca-u = %.2e, max |norm - 1| = %.2e\n", a^2+b^2+c^2-1, a*b+b*c+c*a-u, vecmax(apply(p -> abs(dot(p,p)-1), F)));
printf("row 1 = (%.10f, %.10f, %.10f), row 7 = (%.10f, %.10f, %.10f)\n", F[1][1], F[1][2], F[1][3], F[7][1], F[7][2], F[7][3]);
pairs = [[7,12], [8,10], [9,11]];
{
  my(L = select(s -> #s > 0 && Vec(s)[1] != "#", readstr(concat(REL, "tie_targets.txt"))), pos = 1, ntype = Map(), allok = 1);
  while (pos <= #L,
    my(h = L[pos], name, P = vector(15), R = vector(15), idx = vector(15), ok = 1);
    name = h; pos++;
    for (i = 1, 15, my(w = select(s -> s != "", strsplit(L[pos], " "))); pos++;
      P[i] = vector(3, k, eval(w[2*k-1])); R[i] = vector(3, k, eval(w[2*k])));
    my(cw = apply(eval, select(s -> s != "", strsplit(L[pos], " "))[2..-1])); pos++;
    for (i = 1, 15,
      my(m = select(j -> vecmax(vector(3, k, abs(P[i][k] - F[j][k]) - R[i][k])) <= 0, [1..18]));
      if (#m != 1, ok = 0, idx[i] = m[1]));
    if (#Set(idx) != 15, ok = 0);
    foreach (pairs, pr, if (#setintersect(Set(idx), Set(pr)) != 1, ok = 0));
    my(S = Set(vector(30, e, Set([cw[2*e-1]+1, cw[2*e]+1]))), gap = 1., cerr = 0.);
    if (#S != 30, ok = 0);
    for (i = 1, 15, for (j = i+1, 15,
      my(g = dot(F[idx[i]], F[idx[j]]));
      if (setsearch(S, [i, j]), cerr = max(cerr, abs(g - u)), gap = min(gap, u - g))));
    if (cerr > 1e-90 || gap < 0.1679, ok = 0);
    my(t = if (#setintersect(Set(idx), Set([7,8,9])) == 3 || #setintersect(Set(idx), Set([10,11,12])) == 3, "C3", "C1"), cnt);
    if (!mapisdefined(ntype, t, &cnt), cnt = 0); mapput(ntype, t, cnt + 1);
    if (strsplit(name, " ")[3] != t, ok = 0);
    printf("%s: frame rows %s, toggle points %s, contact error %.1e, gap %.10f, type %s, %s\n", name, idx, setintersect(Set(idx), [7..12]), cerr, gap, t, if (ok, "ok", "FAIL"));
    allok = allok && ok);
  printf("configurations: C3 %d, C1 %d; all checks %s\n", mapget(ntype, "C3"), mapget(ntype, "C1"), if (allok, "pass", "FAIL"));
}
quit;
