# Radius of Theorem 4.1 from Lemma 4.2 (Section 4): exact first-order constant
#   kappa = min over t in T', |t| = 1, of max over the 30 contacts ij of L(t)_ij
# by vertex enumeration of the polytope P = {t in R^30 : Q t = 0, L t <= 1} (tangent vectors in
# orthonormal frames, L and Q as in rigidity.sage). For t in T' \ 0, M = max L(t) > 0 (P is
# bounded, see below) and t / M lies in P, so M >= |t| / R with R = max over P of |t|, attained
# at a vertex of P. A vertex has 30 linearly independent active constraints among the 3 rows of
# Q and the 30 rows of L, hence is the solution of [L_A; Q] t = (1, 0) for a 27-subset A of the
# contacts (complement of a 3-set S) with [L_A; Q] nonsingular. For every 3-set S either
#   (a) [L_A; Q] is certified nonsingular in ball arithmetic (acb_mat_solve), giving an enclosure of
#       t_S; if L_S t_S <= 1 is possible, |t_S| enters the maximum (an upper bound of R); or
#   (b) the 27 contacts of A violate the Laman count: some set U of k >= 2 points spans more than
#       2k - 3 contacts of A. The rows of L for contacts inside U only involve the tangent vectors
#       at U, and they vanish on the 3 independent rotation fields restricted to U (k >= 2 points,
#       no two antipodal), so they have rank <= 2k - 3 and are linearly dependent: L_A has rank
#       < 27 on T' and [L_A; Q] is exactly singular.
# A 3-set in neither case stops the script. P is bounded: a recession direction t != 0 in T' has
# L t <= 0, and the stress omega > 0 of rigidity.out (|omega^T L| < 1e-14, omega_min >= 5.4e-3)
# gives |L t|_2 <= sqrt(30) |eps| |t| / omega_min < sigma |t|, a contradiction with sigma >= 0.31.
# Radius: the proof of Theorem 4.1 with c replaced by kappa: r = kappa / ((1 + u) 1.01 sqrt(15)).
load("code/sage/bk15_exact.sage")
import itertools
RBr = RB
CB = ComplexBallField(RBr.precision())
def vb(p): return vector(RBr, [tob(q) for q in p])
def cross(p, q): return vector(RBr, [p[1]*q[2]-p[2]*q[1], p[2]*q[0]-p[0]*q[2], p[0]*q[1]-p[1]*q[0]])
def nrm(v): return (v*v).sqrt()
allconf = dict(codes)
for choice in itertools.product([0,1], repeat=3):
    kp = sorted([1,2,3,4,5,6,13,14,15,16,17,18] + [[(7,12),(8,10),(9,11)][m][choice[m]] for m in range(3)])
    allconf["frame" + "".join(str(z) for z in choice)] = kp
R100 = RealField(100)
uhi = R100(uB.upper())
res = {}
for nm, keep in allconf.items():
    X = [vb(F[k-1]) for k in keep]
    cont = [(i, j) for i in range(15) for j in range(i+1, 15) if ip(F[keep[i]-1], F[keep[j]-1]) == u]
    assert len(cont) == 30
    E = []
    for p in X:
        ax = min(range(3), key=lambda k: abs(p[k].mid()))
        a = vector(RBr, [1 if k == ax else 0 for k in range(3)])
        e1 = cross(a, p); e1 = e1 / nrm(e1)
        e2 = cross(p, e1)
        E.append((e1, e2))
    Lm = matrix(RBr, 30, 30)
    for row, (i, j) in enumerate(cont):
        for (k, other) in [(j, i), (i, j)]:
            Lm[row, 2*k] += X[other] * E[k][0]
            Lm[row, 2*k+1] += X[other] * E[k][1]
    Qm = matrix(RBr, 3, 30)
    for w in range(3):
        om = vector(RBr, [1 if k == w else 0 for k in range(3)])
        for k in range(15):
            v = cross(om, X[k])
            Qm[w, 2*k] = v * E[k][0]
            Qm[w, 2*k+1] = v * E[k][1]
    # sets U of >= 2 points with surplus s(U) = e(U) - (2|U| - 3) >= 1 in the full contact graph;
    # removing S leaves a Laman violation inside U iff |S cap E(U)| < s(U)
    over = []
    for mask in range(1, 2**15):
        k = bin(mask).count("1")
        if k < 2:
            continue
        eu = [e for e in range(30) if (mask >> cont[e][0]) & 1 and (mask >> cont[e][1]) & 1]
        s = len(eu) - (2*k - 3)
        if s >= 1:
            over.append((sum(2**e for e in eu), s))
    def laman_violated(S):
        sm = sum(2**e for e in S)
        return any(bin(em & sm).count("1") < s for (em, s) in over)
    rhs = matrix(CB, 30, 1, [1]*27 + [0]*3)
    Rsq = RBr(0).upper()
    nsing = nfeas = ninf = 0
    arg = None
    for S in itertools.combinations(range(30), 3):
        A = [e for e in range(30) if e not in S]
        M = matrix(CB, [list(Lm.row(e)) for e in A] + [list(Qm.row(w)) for w in range(3)])
        try:
            t = M.solve_right(rhs)
        except (ValueError, ZeroDivisionError):
            t = None
        if t is None or not all(z.real().is_finite() for z in t.list()):
            if not laman_violated(S):
                raise RuntimeError("%s: 3-set %s neither certified nonsingular nor Laman-singular" % (nm, S))
            nsing += 1
            continue
        tv = vector(RBr, [z.real() for z in t.list()])
        LS = [Lm.row(e) * tv for e in S]
        if any(z.lower() > 1 for z in LS):
            ninf += 1
            continue
        nfeas += 1
        n2 = (tv * tv).upper()
        if n2 > Rsq:
            Rsq = n2; arg = S
    Rup = RBr(Rsq).sqrt().upper()
    kappa = (1 / RBr(Rup)).lower()
    r = (RBr(kappa) / ((1 + RBr(uB.upper())) * RBr(101) / 100 * RBr(15).sqrt())).lower()
    ok = RBr(15).sqrt() * RBr(r) <= RBr(1) / 10
    print("%s: 3-sets: %d singular (Laman count), %d infeasible, %d possibly feasible vertices" % (nm, nsing, ninf, nfeas))
    print("%s: max |t| over P <= %.8e (at S = %s); kappa >= %.8e ; radius r = %.8e, sqrt(15) r <= 0.1: %s" % (nm, Rup, arg, kappa, r, ok))
    sys.stdout.flush()
    res[nm] = (kappa, r)
print("minimum radius over all configurations >=", dec(min(v[1] for v in res.values()).exact_rational(), False))
