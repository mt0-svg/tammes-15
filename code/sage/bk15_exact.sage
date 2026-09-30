# Exact construction of the Buddenhagen-Kottwitz 18-point frame and the optimal codes C3, C1
# (formulas of Buddenhagen and Kottwitz, Section 4) in a number field, with a real embedding to ball arithmetic.
# Checks, exactly in the field: unit norms, the 30 contacts of C3 and C1 (inner product = u), and,
# in ball arithmetic, that every other pair has inner product < u with a margin.
# Output: data/bk15_exact.txt (coordinates as 120-digit balls) and the contact lists.
import sys
Qx.<x> = QQ[]
pu = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1
assert pu.is_irreducible()
K.<uu> = NumberField(pu)
Ky.<y> = K[]
qb = 9*(4*uu^2-uu-1)*(3*uu+1)^2*y^2 + 2*uu*(62*uu^4-155*uu^3-37*uu^2+51*uu+15)*y + uu^2*(4*uu^2-uu-1)*(5*uu-1)^2
fq = qb.factor()
print("qb over Q(u):", [ (f.degree(), e) for f, e in fq ])
PREC = 600
RB = RealBallField(PREC)
# real embedding of K with u in (0.5, 0.7)
embs = [e for e in K.embeddings(RealField(200)) if 0.5 < e(uu) < 0.7]
assert len(embs) == 1
u0 = embs[0](uu)
# b^2 is the root of qb near 0.0294 (bk15_check.out)
if fq[0][0].degree() == 2 and len(fq) == 1:
    K2.<yy> = K.extension(qb)
else:
    # pick the linear factor with the right root
    raise RuntimeError("qb reducible: handle")
Kz.<z> = K2[]
K3.<bb> = K2.extension(z^2 - yy)
L = K3.absolute_field('w')
fromL, toL = L.structure()
print("absolute degree:", L.degree())
# the real embedding of L with u ~ 0.5926, b^2 ~ 0.0294, b ~ 0.1715 (b > 0)
uL = toL(K3(uu)); yL = toL(K3(yy)); bL = toL(bb)
cands = []
for e in L.embeddings(RealField(300)):
    if abs(e(uL) - u0) < 1e-50 and abs(e(yL) - 0.0294089263585154) < 1e-12 and abs(e(bL) - 0.171490309809375) < 1e-12:
        cands.append(e)
assert len(cands) == 1, len(cands)
emb = cands[0]
u = uL; b = bL
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u))
a = (u - b*c)/(b+c)
assert a^2 + b^2 + c^2 == 1 and a*c + b*a + c*b == u
dd = ((2*a-b+2*c)*u-b)/(u+1); ee = ((2*a+2*b-c)*u-c)/(u+1); ff = ((-a+2*b+2*c)*u-a)/(u+1)
r = ((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)/(u+1)^2
s = ((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)/(u+1)^2
t = ((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)/(u+1)^2
names = ["V1","V2","V3","V12","V23","V31","P","I","A","Q","J","B","W12","W23","W31","W1","W2","W3"]
F = [[a,b,c],[c,a,b],[b,c,a],[dd,ee,ff],[ff,dd,ee],[ee,ff,dd],[r,s,t],[t,r,s],[s,t,r],
     [-t,-s,-r],[-r,-t,-s],[-s,-r,-t],[-ff,-ee,-dd],[-ee,-dd,-ff],[-dd,-ff,-ee],[-c,-b,-a],[-b,-a,-c],[-a,-c,-b]]
for p in F:
    assert p[0]^2 + p[1]^2 + p[2]^2 == 1
print("18 frame points have exact unit norm")
def ip(p, q): return p[0]*q[0] + p[1]*q[1] + p[2]*q[2]
# embedding to balls: evaluate the polynomial expression of v in w at a ball for w
wR = emb(L.gen())
# refine the generator root to PREC bits
fw = L.polynomial()
RIF_ = RealIntervalField(PREC)
roots = [rr for rr in fw.roots(RIF_, multiplicities=False) if abs(rr.center() - wR) < 1e-60]
assert len(roots) == 1
wI = roots[0]
def tob(v):
    return RB(v.polynomial()(wI))
codes = {"C3": [1,2,3,4,5,6,7,8,9,13,14,15,16,17,18], "C1": [1,2,3,4,5,6,7,8,11,13,14,15,16,17,18]}
uB = tob(u)
def bs(z): return "%s %s" % (z.mid().str(digits=150), z.rad().str(digits=3))
out = open("data/bk15_exact.txt", "w")
out.write("# u = cos(psi*) and the 18 frame points of Buddenhagen-Kottwitz as balls (%d bits); exact checks in bk15_exact.sage\n" % PREC)
out.write("u %s\n" % bs(uB))
for i, p in enumerate(F):
    out.write("%s %s\n" % (names[i], " ".join(bs(tob(q)) for q in p)))
for nm, keep in codes.items():
    X = [F[k-1] for k in keep]
    cont = []
    other_max = None
    for i in range(15):
        for j in range(i+1, 15):
            g = ip(X[i], X[j])
            if g == u:
                cont.append((i, j))
            else:
                gb = tob(g) - uB
                assert gb < 0, (nm, i, j, gb)
                other_max = gb if other_max is None else other_max.max(gb)
    print(nm, "exact contacts:", len(cont), " max over other pairs of <x,y> - u:", other_max.upper())
    out.write("%s keep %s\n" % (nm, keep))
    out.write("%s contacts %s\n" % (nm, cont))
out.close()
print("psi* deg:", (uB.arccos() * 180 / RB.pi()))
