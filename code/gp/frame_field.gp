\\ Check of Proposition 2.1 and the targets of Theorem 4.1: exact construction of the Buddenhagen-Kottwitz frame in a degree-20
\\ field built with rnfequation (independent of the Sage code), a rigorous real embedding by Sturm
\\ isolation, rigorous rational enclosures of all coordinates, exact checks of norms and contacts.
\\ Defines: z2, uE, F (18 frame points as polmods mod z2), encl(g) = [center, radius] (rationals).
\\ run with: gp -q --default parisizemax=2000000000 --default nbthreads=1 (a default(parisizemax) inside a nested read aborts the read)
default(realprecision, 250);
pu = 13*y^5 - y^4 + 6*y^3 + 2*y^2 - 3*y - 1;
qbx = 9*(4*y^2-y-1)*(3*y+1)^2*x^2 + 2*y*(62*y^4-155*y^3-37*y^2+51*y+15)*x + y^2*(4*y^2-y-1)*(5*y-1)^2;
R1 = rnfequation(pu, qbx, 1);   \\ [z1(x), u as polmod in theta1, k1], theta1 = beta + k1 u
z1 = R1[1]; a1 = R1[2]; k1 = R1[3];
beta1 = Mod(x, z1) - k1*a1;
R2 = rnfequation(subst(z1, x, y), x^2 - subst(lift(beta1), x, y), 1);
z2 = R2[1]; a2 = R2[2]; k2 = R2[3];
print("tower degrees: ", poldegree(z1), " ", poldegree(z2), "; z2 irreducible over Q: ", polisirreducible(z2), " (so each step of the tower is irreducible)");
th1 = a2;
bE = Mod(x, z2) - k2*th1;
uE = subst(lift(a1), x, lift(th1)) * Mod(1, z2);
betaE = subst(lift(beta1), x, lift(th1)) * Mod(1, z2);
print("exact: pu(u) = 0: ", subst(pu, y, uE) == 0, "; b^2 = beta: ", bE^2 == betaE, "; qb(u, beta) = 0: ", subst(subst(qbx, x, betaE), y, uE) == 0);
rr = polrootsreal(z2);
evn(g, w0) = subst(lift(g), x, w0);
sel = [];
for(k = 1, #rr, my(w0 = rr[k]); if(abs(evn(uE,w0) - 0.5926059029) < 1e-8 && abs(evn(betaE,w0) - 0.02940892635) < 1e-8 && abs(evn(bE,w0) - 0.1714903098) < 1e-8, sel = concat(sel, k)));
print("real roots of z2: ", #rr, "; embeddings with u ~ 0.5926, b^2 ~ 0.0294, b ~ +0.1715: ", sel);
if(#sel != 1, error("embedding"));
w0 = rr[sel[1]];
DEN = 10^220;
wlo = floor(w0*DEN)/DEN - 1/DEN; whi = wlo + 3/DEN;
print("Sturm count of z2 in [wlo, whi] (width 3e-220): ", polsturm(z2, [wlo, whi]));
if(polsturm(z2, [wlo, whi]) != 1, error("isolation"));
wmid = (wlo + whi)/2; wh = (whi - wlo)/2; wrho = max(abs(wlo), abs(whi));
\\ rigorous enclosure of g(w), w the root in [wlo, whi]: mean value theorem on the polynomial lift
encl(g) = { my(P = lift(g), c0, dd, c1);
  if(type(P) != "t_POL", return([P, 0]));
  c0 = subst(P, x, wmid);
  dd = sum(k = 1, poldegree(P), k * abs(polcoef(P, k)) * wrho^(k-1));
  c1 = round(c0 * 10^150) / 10^150;
  [c1, wh * dd + abs(c0 - c1)]; }
u = uE; b = bE;
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u));
a = (u - b*c)/(b+c);
print("exact: a^2+b^2+c^2 = 1: ", a^2+b^2+c^2 == 1, "; ab+bc+ca = u: ", a*b+b*c+c*a == u);
dd = ((2*a-b+2*c)*u-b)/(u+1); ee = ((2*a+2*b-c)*u-c)/(u+1); ff = ((-a+2*b+2*c)*u-a)/(u+1);
rq = ((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)/(u+1)^2;
sq = ((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)/(u+1)^2;
tq = ((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)/(u+1)^2;
names = ["V1","V2","V3","V12","V23","V31","P","I","A","Q","J","B","W12","W23","W31","W1","W2","W3"];
F = [[a,b,c],[c,a,b],[b,c,a],[dd,ee,ff],[ff,dd,ee],[ee,ff,dd],[rq,sq,tq],[tq,rq,sq],[sq,tq,rq],\
     [-tq,-sq,-rq],[-rq,-tq,-sq],[-sq,-rq,-tq],[-ff,-ee,-dd],[-ee,-dd,-ff],[-dd,-ff,-ee],[-c,-b,-a],[-b,-a,-c],[-a,-c,-b]];
print("exact: all 18 frame points have norm 1: ", prod(k = 1, 18, F[k][1]^2 + F[k][2]^2 + F[k][3]^2 == 1));
ipE(p, q) = p[1]*q[1] + p[2]*q[2] + p[3]*q[3];
FE = vector(18, k, vector(3, m, encl(F[k][m])));
print("max enclosure radius of the 54 coordinates: ", vecmax(concat(vector(18, k, vector(3, m, FE[k][m][2])))) * 1.0);
uEnc = encl(uE);
print("u enclosure: ", uEnc[1]*1.0, " +- ", uEnc[2]*1.0);
