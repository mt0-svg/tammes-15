\\ Independent numerical recomputation of the first-order rigidity
\\ constant kappa of Lemma 4.2 (Section 4) for the 8 frame configurations of
\\ data/tie_targets.txt, by direct vertex enumeration of P = {t in T' : L t <= 1}, plus the checks
\\ that make P bounded (rank of L on T' is 27, a strictly positive self-stress exists) and the
\\ separation of the non-contact pairs. PARI floating point at 100 digits (numerical evidence).
\\ Run from code/gp.
default(parisizemax, 2000000000);
default(nbthreads, 1);
\p 100
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
print("configurations read: ", #confs);
cross(a, b) = [a[2]*b[3] - a[3]*b[2], a[3]*b[1] - a[1]*b[3], a[1]*b[2] - a[2]*b[1]]~;
frame(p) =
{
  my(a = if(abs(p[1]) < 0.9, [1, 0, 0]~, [0, 1, 0]~), e1, e2);
  e1 = a - (a~*p)*p; e1 = e1/sqrt(e1~*e1);
  e2 = cross(p, e1);
  [e1, e2];
}
stresses(Lm) =
{
  my(E = mateigen(Lm*Lm~, 1), ev = real(E[1]), V = real(E[2]), idx = []);
  for(i = 1, #ev, if(abs(ev[i]) < 1e-30, idx = concat(idx, i)));
  matrix(#ev, #idx, r, c, V[r, idx[c]]);
}
bestpos(K) =
{
  my(best = -1, x, om, v);
  for(it = 1, 20000,
    x = vector(#K, z, random(1.)*2 - 1)~;
    om = K*x;
    if(vecsum(om) < 0, om = -om);
    if(vecsum(om) == 0, next);
    om = om/vecsum(om);
    v = vecmin(om);
    if(v > best, best = v));
  best;
}
venum(Lm, Qm) =
{
  my(sing = 0, sing40 = 0, dmin = 1, feas = 0, Rmax = 0, A, Mx, rhs, dt, hn, t);
  rhs = concat(vector(27, z, 1), [0, 0, 0])~;
  forsubset([30, 3], S,
    A = setminus([1..30], Vec(S));
    Mx = matrix(30, 30, r, c, if(r <= 27, Lm[A[r], c], Qm[r - 27, c]));
    hn = prod(r = 1, 30, sqrt(Mx[r, ]*Mx[r, ]~));
    dt = abs(matdet(Mx))/hn;
    if(dt < 1e-30, sing++; if(dt > 1e-50, sing40++),
      dmin = min(dmin, dt); t = matsolve(Mx, rhs);
      if(vecmax(Lm*t) <= 1 + 1e-60, feas++; Rmax = max(Rmax, sqrt(t~*t)))));
  print("   singular (normalised det < 1e-30): ", sing, ", of which with det in (1e-50, 1e-30) (singular up to the 40-digit data): ", sing40, "; smallest det of the others: ", dmin);
  [sing, feas, Rmax];
}
doconf(cf) =
{
  my(nm = cf[1], P = cf[2], C = cf[3], F, Lm, Qm, nrm, cmax, ncmax, sv, K, SC, i, j, om, ve);
  SC = Set(C);
  nrm = vecmax(vector(15, i, abs(P[i]~*P[i] - 1)));
  cmax = vecmax(vector(#C, k, abs(P[C[k][1]]~*P[C[k][2]] - u)));
  ncmax = -2;
  for(i = 1, 15, for(j = i + 1, 15, if(!setsearch(SC, [i, j]), ncmax = max(ncmax, P[i]~*P[j]))));
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
  print(nm, ": max |p|^2-1 ", nrm, "; contacts ", #C, ", max |<pi,pj>-u| ", cmax,
        "; max non-contact <pi,pj> - u = ", ncmax - u, "; |L Q^T| = ", normlp(Lm*Qm~));
  sv = vecsort(sqrt(abs(real(mateigen(matconcat([Lm; Qm])~*matconcat([Lm; Qm]), 1)[1]))));
  print("   two smallest singular values of [L; Q]: ", sv[1], ", ", sv[2]);
  K = stresses(Lm);
  print("   self-stress space dim ", #K, "; best min omega_i (sum 1), random search: ", bestpos(K));
  ve = venum(Lm, Qm);
  print("   vertex enumeration: singular ", ve[1], ", feasible vertices ", ve[2], ", Rmax = ", ve[3], ", kappa = 1/Rmax = ", 1/ve[3]);
  print("   radius kappa/((1+u)*1.01*sqrt 15) = ", 1/ve[3]/((1 + u)*1.01*sqrt(15)));
}
for(c = 1, #confs, doconf(confs[c]));
