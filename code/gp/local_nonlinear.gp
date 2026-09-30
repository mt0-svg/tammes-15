\\ Nonlinear sanity test of Theorem 4.1 (Section 4) near the frame
\\ configurations of data/tie_targets.txt. For the tangent direction w of the vertex of
\\ P = {t in T' : L t <= 1} farthest from 0 (the direction in which the contacts shrink slowest to
\\ first order, ratio kappa) and for random directions, move the points to x_i = normalise(p_i + s w_i)
\\ and print max_{i<j} <x_i, x_j> - u, which Theorem 4.1 says is >= 0 (psi(X) <= psi*) while
\\ |X - C| <= sqrt(15) * 1.04e-3. Floating point at 60 digits (numerical evidence, not a proof).
\\ Run from code/gp.
default(parisizemax, 2000000000);
default(nbthreads, 1);
\p 60
q(x) = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
u = solve(x = 1/2, 7/10, q(x));
LL = readstr("../../data/tie_targets.txt");
parseconfs() =
{
  my(i = 1, n = #LL, w, P, C, nm, z, out = List());
  while(i <= n,
    w = strsplit(LL[i], " ");
    if(w[1] == "conf",
      nm = concat(w[2], concat(" ", w[3]));
      P = vector(15, k, my(y = strsplit(LL[i + k], " ")); [eval(y[1]), eval(y[3]), eval(y[5])]~);
      z = strsplit(LL[i + 16], " ");
      C = vector((#z - 1)/2, k, [eval(z[2*k]) + 1, eval(z[2*k + 1]) + 1]);
      listput(out, [nm, P, C]);
      i += 17,
      i++));
  out;
}
confs = parseconfs();
cross(a, b) = [a[2]*b[3] - a[3]*b[2], a[3]*b[1] - a[1]*b[3], a[1]*b[2] - a[2]*b[1]]~;
frame(p) =
{
  my(a = if(abs(p[1]) < 0.9, [1, 0, 0]~, [0, 1, 0]~), e1, e2);
  e1 = a - (a~*p)*p; e1 = e1/sqrt(e1~*e1);
  e2 = cross(p, e1);
  [e1, e2];
}
\\ max over all pairs of <x_i, x_j> - u after moving by s * (tangent vector t in frame coordinates)
margin(P, F, t, s) =
{
  my(X = vector(15, i, my(y = P[i] + s*(t[2*i - 1]*F[i][1] + t[2*i]*F[i][2])); y/sqrt(y~*y)), m = -2);
  for(i = 1, 15, for(j = i + 1, 15, m = max(m, X[i]~*X[j])));
  m - u;
}
doconf(cf) =
{
  my(nm = cf[1], P = cf[2], C = cf[3], F, Lm, Qm, i, j, om, rhs, A, Mx, dt, hn, t, best = 0, tb, K, w, S, mn);
  F = vector(15, i, frame(P[i]));
  Lm = matrix(#C, 30);
  for(k = 1, #C,
    i = C[k][1]; j = C[k][2];
    for(s = 1, 2,
      Lm[k, 2*(j - 1) + s] += P[i]~*F[j][s];
      Lm[k, 2*(i - 1) + s] += P[j]~*F[i][s]));
  Qm = matrix(3, 30);
  for(r = 1, 3,
    om = vector(3, z, z == r)~;
    for(i = 1, 15, for(s = 1, 2, Qm[r, 2*(i - 1) + s] = cross(om, P[i])~*F[i][s])));
  rhs = concat(vector(27, z, 1), [0, 0, 0])~;
  forsubset([30, 3], S,
    A = setminus([1..30], Vec(S));
    Mx = matrix(30, 30, r, c, if(r <= 27, Lm[A[r], c], Qm[r - 27, c]));
    hn = prod(r = 1, 30, sqrt(Mx[r, ]*Mx[r, ]~));
    dt = abs(matdet(Mx))/hn;
    if(dt >= 1e-30,
      t = matsolve(Mx, rhs);
      if(vecmax(Lm*t) <= 1 + 1e-40 && t~*t > best, best = t~*t; tb = t)));
  w = tb/sqrt(tb~*tb);
  print(nm, ": Rmax = ", sqrt(best), ", kappa = ", 1/sqrt(best), "; along the extreme direction, max_e (L w)_e = ", vecmax(Lm*w));
  foreach([1e-4, 1e-3, sqrt(15)*1.04e-3, 1e-2, 3e-2, 1e-1, 2e-1], s,
    print("   s = ", s, ": max <x_i,x_j> - u = ", margin(P, F, w, s), " (first order kappa*s = ", s/sqrt(best), ")"));
  \\ random directions in T' (kernel of Qm), |t| = sqrt(15) * 1.04e-3
  K = matker(Qm);
  mn = 1;
  for(it = 1, 3000,
    t = K*vector(#K, z, random(1.)*2 - 1)~; t = t/sqrt(t~*t);
    mn = min(mn, margin(P, F, t, sqrt(15)*1.04e-3)));
  print("   3000 random directions of T' at s = sqrt(15)*1.04e-3: min over directions of max <x_i,x_j> - u = ", mn);
  \\ random per-point perturbations of size <= 1.04e-3 (no rotation normalisation)
  mn = 1;
  for(it = 1, 3000,
    t = vector(30, z, random(1.)*2 - 1)~;
    for(i = 1, 15, my(nn = sqrt(t[2*i - 1]^2 + t[2*i]^2)); if(nn > 0, t[2*i - 1] *= 1.04e-3/nn; t[2*i] *= 1.04e-3/nn));
    mn = min(mn, margin(P, F, t, 1)));
  print("   3000 random per-point tangent moves of length 1.04e-3: min of max <x_i,x_j> - u = ", mn);
}
doconf(confs[2]);
doconf(confs[1]);
