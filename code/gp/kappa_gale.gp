\\ Independent recomputation of the first-order constant kappa of Lemma 4.2 (Section 4,
\\ step (4b) of the proof) for the 8 frame configurations, in PARI/GP at 120 digits.
\\ Method, different from rigidity2.sage:
\\  - points built here from the Buddenhagen-Kottwitz formulas, contacts detected numerically;
\\  - other tangent frames (Gram-Schmidt of a fixed generic vector);
\\  - an orthonormal basis B of T' = ker Q, so P becomes {y in R^27 : l_e . y <= 1}, l_e = L_e B;
\\  - the 3-dimensional stress space K (left kernel of l): a 27-set A = complement of S gives a
\\    basis l_A iff det K[S,] != 0 (Gale duality), and the values z = l_S . y_A of the vertex
\\    y_A on the 3 missing rows solve K[S,]~ z = -K[A,]~ 1 (a 3 x 3 system), which decides
\\    feasibility without the 27 x 27 solve; |y_A| is then computed from the 27 x 27 solve;
\\  - the Laman surplus test is recomputed and compared with the singular 3-sets.
default(parisizemax, 1000000000);
default(nbthreads, 1);
\p 120
pu = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
U = select(z -> z > 0.5 && z < 0.7, polrootsreal(pu));
if (#U != 1, error("u"));
u = U[1];
qb = 9*(4*u^2-u-1)*(3*u+1)^2*y^2 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*y + u^2*(4*u^2-u-1)*(5*u-1)^2;
Y = select(z -> abs(z - 0.0294089263585154) < 1e-6, polrootsreal(qb));
if (#Y != 1, error("b^2"));
b = sqrt(Y[1]);
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u));
a = (u - b*c)/(b+c);
dd = ((2*a-b+2*c)*u-b)/(u+1); ee = ((2*a+2*b-c)*u-c)/(u+1); ff = ((-a+2*b+2*c)*u-a)/(u+1);
r = ((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)/(u+1)^2;
s = ((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)/(u+1)^2;
t = ((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)/(u+1)^2;
F = [[a,b,c],[c,a,b],[b,c,a],[dd,ee,ff],[ff,dd,ee],[ee,ff,dd],[r,s,t],[t,r,s],[s,t,r],\
     [-t,-s,-r],[-r,-t,-s],[-s,-r,-t],[-ff,-ee,-dd],[-ee,-dd,-ff],[-dd,-ff,-ee],[-c,-b,-a],[-b,-a,-c],[-a,-c,-b]];
for (k = 1, 18, if (abs(F[k]*F[k]~ - 1) > 1e-100, error("norm")));
cr(p, q) = [p[2]*q[3]-p[3]*q[2], p[3]*q[1]-p[1]*q[3], p[1]*q[2]-p[2]*q[1]];
nz(v) = v / sqrt(v*v~);
w0 = nz([0.3141, -0.7182, 0.5772]);
\\ Laman data for a contact list (edges as pairs of 1-based point indices)
lamanover(E) = {
  my(over = List());
  for (m = 1, 2^15 - 1,
    my(k = hammingweight(m), em = 0, ne = 0);
    if (k < 2, next);
    for (e = 1, #E, if (bittest(m, E[e][1]-1) && bittest(m, E[e][2]-1), em += 2^(e-1); ne++));
    if (ne - (2*k - 3) >= 1, listput(over, [em, ne - (2*k - 3)])));
  Vec(over);
}
lamanviol(over, S) = {
  my(sm = sum(i = 1, #S, 2^(S[i]-1)));
  for (i = 1, #over, if (hammingweight(bitand(over[i][1], sm)) < over[i][2], return(1)));
  0;
}
run(name, keep) = {
  my(X = vector(15, i, F[keep[i]]), E = List(), fr, L, Q, B, l, K, over,
     nsing = 0, nfeas = 0, ninf = 0, ntie = 0, Rsq = 0, arg = 0, mindetns = 1e9, maxdets = 0,
     mismatch = 0, zdiff = 0, secmax = 0);
  for (i = 1, 15, for (j = i+1, 15, my(g = X[i]*X[j]~);
    if (abs(g - u) < 1e-90, listput(E, [i, j]), if (g - u > -0.16, error("near contact")))));
  E = Vec(E);
  if (#E != 30, error("contacts"));
  fr = vector(15, i, my(e1 = nz(w0 - (w0*X[i]~)*X[i])); [e1, cr(X[i], e1)]);
  L = matrix(30, 30);
  for (e = 1, 30, my(i = E[e][1], j = E[e][2]);
    for (h = 1, 2,
      L[e, 2*j-2+h] += X[i]*fr[j][h]~;
      L[e, 2*i-2+h] += X[j]*fr[i][h]~));
  Q = matrix(3, 30);
  for (w = 1, 3, my(om = vector(3, k, k == w));
    for (k = 1, 15, my(v = cr(om, X[k])); for (h = 1, 2, Q[w, 2*k-2+h] = v*fr[k][h]~)));
  if (normlp(L*Q~) > 1e-100, error("L does not kill rotations"));
  \\ orthonormal basis of ker Q by Gram-Schmidt
  my(B0 = matker(Q), cols = List());
  for (k = 1, #B0, my(v = B0[, k]);
    for (m = 1, #cols, v -= (cols[m]~*v) * cols[m]);
    v /= sqrt(v~*v); listput(cols, v));
  B = Mat(Vec(cols));
  if (matsize(B) != [30, 27], error("basis"));
  if (normlp(Q*B) > 1e-100 || normlp(B~*B - matid(27)) > 1e-100, error("basis check"));
  l = L*B;
  K = matker(l~);
  if (matsize(K) != [30, 3], error("stress space"));
  over = lamanover(E);
  forsubset([30, 3], S,
    my(Sv = Vec(S), A = setminus([1..30], Sv), KS = matrix(3, 3, i, j, K[Sv[j], i]), dt = abs(matdet(KS)), lv = lamanviol(over, Sv));
    if (dt < 1e-60,
      nsing++; maxdets = max(maxdets, dt); if (!lv, mismatch++); next);
    mindetns = min(mindetns, dt);
    if (lv, mismatch++);
    my(rhs = -sum(e = 1, 27, K[A[e], ]~), z = matsolve(KS, rhs));
    my(lA = matrix(27, 27, i, j, l[A[i], j]), yv = matsolve(lA, vectorv(27, i, 1)));
    zdiff = max(zdiff, normlp(vector(3, m, l[Sv[m], ]*yv) - z~));
    if (vecmax(z) > 1 + 1e-50, ninf++; next);
    if (vecmax(z) > 1 - 1e-50, ntie++);
    nfeas++;
    my(n2 = yv~*yv);
    if (n2 > Rsq, secmax = Rsq; Rsq = n2; arg = Sv - [1,1,1], if (n2 > secmax && n2 < Rsq, secmax = n2)));
  printf("%s: %d contacts; singular 3-sets %d (max |det K_S| %.3e, min over nonsingular %.3e), Laman mismatches %d\n",
    name, #E, nsing, maxdets, mindetns, mismatch);
  printf("%s: infeasible %d, feasible %d (of which %d degenerate ties), max |z(Gale) - l_S y| = %.3e\n", name, ninf, nfeas, ntie, zdiff);
  printf("%s: Rmax = %.12f at S = %s (0-based), second largest |y| = %.12f; kappa = 1/Rmax = %.12e\n", name, sqrt(Rsq), arg, sqrt(secmax), 1/sqrt(Rsq));
  printf("%s: r = kappa/((1+u) 1.01 sqrt 15) = %.10e\n", name, 1/sqrt(Rsq)/((1+u)*1.01*sqrt(15)));
  [1/sqrt(Rsq), E];
}
base = [1,2,3,4,5,6,13,14,15,16,17,18];
prs = [[7,12],[8,10],[9,11]];
res = List();
{forvec(ch = [[0,1],[0,1],[0,1]],
  my(keep = vecsort(concat(base, vector(3, m, prs[m][ch[m]+1]))));
  my(nm = Str("frame", ch[1], ch[2], ch[3]));
  listput(res, run(nm, keep)[1]));}
printf("min kappa over the 8 configurations: %.12e\n", vecmin(Vec(res)));
printf("psi* deg: %.15f\n", acos(u)*180/Pi);
quit;
