# Attainment psi(C1) = psi(C3) = arccos u (Section 2), recomputed with Sage's exact
# real algebraic numbers AA (no number field tower), from the construction formulas of
# code/sage/bk15_exact.sage (Buddenhagen-Kottwitz frame). Every equality below is exact in AA;
# the inequalities for non-contact pairs are exact comparisons in AA.
x = polygen(QQ, 'x')
pu = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1
us = [r for r in pu.roots(AA, multiplicities=False) if 1/2 < r < 7/10]
assert len(us) == 1
u = us[0]
y = polygen(AA, 'y')
qb = 9*(4*u^2-u-1)*(3*u+1)^2*y^2 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*y + u^2*(4*u^2-u-1)*(5*u-1)^2
ys = [r for r in qb.roots(AA, multiplicities=False) if abs(r - 0.0294089263585154) < 1e-9]
assert len(ys) == 1, qb.roots(AA)
b = ys[0].sqrt()
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u))
a = (u - b*c)/(b+c)
print("a, b, c =", RR(a), RR(b), RR(c))
assert a^2 + b^2 + c^2 == 1 and a*c + b*a + c*b == u
dd = ((2*a-b+2*c)*u-b)/(u+1); ee = ((2*a+2*b-c)*u-c)/(u+1); ff = ((-a+2*b+2*c)*u-a)/(u+1)
r = ((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)/(u+1)^2
s = ((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)/(u+1)^2
t = ((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)/(u+1)^2
F = [[a,b,c],[c,a,b],[b,c,a],[dd,ee,ff],[ff,dd,ee],[ee,ff,dd],[r,s,t],[t,r,s],[s,t,r],
     [-t,-s,-r],[-r,-t,-s],[-s,-r,-t],[-ff,-ee,-dd],[-ee,-dd,-ff],[-dd,-ff,-ee],[-c,-b,-a],[-b,-a,-c],[-a,-c,-b]]
for p in F:
    assert p[0]^2 + p[1]^2 + p[2]^2 == 1
print("18 frame points: exact unit norm")
ip = lambda p, q: p[0]*q[0] + p[1]*q[1] + p[2]*q[2]
codes = {"C3": [1,2,3,4,5,6,7,8,9,13,14,15,16,17,18], "C1": [1,2,3,4,5,6,7,8,11,13,14,15,16,17,18]}
for nm, keep in codes.items():
    X = [F[k-1] for k in keep]
    ncont = 0; worst = None
    for i in range(15):
        for j in range(i+1, 15):
            g = ip(X[i], X[j])
            if g == u:
                ncont += 1
            else:
                assert g < u, (nm, i, j)
                worst = g if worst is None or g > worst else worst
    print(nm, ": pairs with inner product exactly u:", ncont, "; all other pairs < u; max other - u =", RR(worst - u))
print("psi* =", RR(arccos(RR(u))*180/pi), "deg")
# Match with the data files: each data point within 1e-20 of a distinct point of the exact code.
for nm, keep in codes.items():
    X = [F[k-1] for k in keep]
    fn = "../../data/bk15_%s.txt" % nm.lower()
    D = [[RealField(200)(z) for z in l.split()] for l in open(fn) if l.strip()]
    used = set(); worst = 0
    for p in D:
        dist = [(sum((RealField(200)(X[j][i]) - p[i])^2 for i in range(3)).sqrt(), j) for j in range(15)]
        m, j = min(dist)
        assert j not in used; used.add(j); worst = max(worst, m)
    print(fn, ": bijective match with the exact", nm, ", max distance", worst)
# C1 and C3 are not congruent: compare the sorted multisets of inner products.
G = {}
for nm, keep in codes.items():
    X = [F[k-1] for k in keep]
    G[nm] = sorted(RR(ip(X[i], X[j])) for i in range(15) for j in range(i+1, 15))
print("max |sorted Gram C1 - sorted Gram C3| =", max(abs(p - q) for p, q in zip(G["C1"], G["C3"])))
