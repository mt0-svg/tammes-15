# First-order (strut) rigidity of the optimal codes C3 and C1, and of the 8 frame configurations
# (one point of each toggle pair; frame000 = C3, frame001 = C1), with an explicit radius.
# Theorem 4.1 (Section 4): if X is a configuration of 15 unit vectors with
# |x_i - R p_i| <= r for all i and some rotation R, then max over the 30 contacts ij of C of
# <x_i, x_j> >= u = cos psi*, i.e. psi(X) <= psi*, with equality only when X is a rotation of C.
# Proof ingredients computed here, in ball arithmetic from the exact construction (bk15_exact.sage):
#   L : tangent vectors (orthonormal frames at the p_i, R^30) -> R^30, L(t)_ij = <p_i,t_j> + <p_j,t_i>;
#   Q : the three infinitesimal rotations; A = L^T L + Q^T Q; lambda_min(A) <= sigma^2, where sigma is
#       the smallest singular value of L on the complement T' of the rotations (block argument);
#   omega > 0 with residual eps = omega^T L; then for t in T', max_ij L(t)_ij >= c |t| with
#       c = (sigma / sqrt(30) - |eps| / omega_min) / W, W = sum(omega) / omega_min;
#   second order: <x_i,x_j> - u >= L(t)_ij - (1+u)(1+|t|^2)|t|^2, and |t| <= sqrt(15) r after the
#       optimal rotation, so r = c / ((1+u) 1.01 sqrt(15)) works as long as sqrt(15) r <= 0.1.
load("code/sage/bk15_exact.sage")
RBr = RB
def vb(p): return vector(RBr, [tob(q) for q in p])
def cross(p, q): return vector(RBr, [p[1]*q[2]-p[2]*q[1], p[2]*q[0]-p[0]*q[2], p[0]*q[1]-p[1]*q[0]])
def nrm(v): return (v*v).sqrt()
import itertools
allconf = dict(codes)
for choice in itertools.product([0,1], repeat=3):
    kp = sorted([1,2,3,4,5,6,13,14,15,16,17,18] + [[(7,12),(8,10),(9,11)][m][choice[m]] for m in range(3)])
    allconf["frame" + "".join(str(z) for z in choice)] = kp
res = {}
for nm, keep in allconf.items():
    X = [vb(F[k-1]) for k in keep]
    cont = []
    for i in range(15):
        for j in range(i+1, 15):
            if ip(F[keep[i]-1], F[keep[j]-1]) == u:
                cont.append((i, j))
    assert len(cont) == 30
    # orthonormal tangent frames (contain the exact frames of the exact points)
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
    # check L annihilates rotations (balls contain 0)
    Z = Lm * Qm.transpose()
    assert all(z.contains_zero() for z in Z.list())
    A = Lm.transpose() * Lm + Qm.transpose() * Qm
    # rational midpoint and radius
    Am = matrix(QQ, 30, 30, [z.mid().exact_rational() for z in A.list()])
    Am = (Am + Am.transpose()) / 2
    # interval arithmetic from here on: every printed bound is rounded outward from an interval
    RI = RealIntervalField(100)
    radF = RI(sum(RI(z.rad()) ** 2 for z in A.list())).sqrt().upper()
    assert radF < 1e-100
    ev = sorted(matrix(RDF, Am).eigenvalues())
    lam0 = QQ(floor(RDF(ev[0]) * 0.99 * 10**6)) / 10**6
    assert (Am - lam0 * identity_matrix(QQ, 30)).is_positive_definite()
    lam_lo = RI(lam0) - RI(radF)
    sigma_lo = lam_lo.sqrt()
    # stress: left kernel of L (numerical), positive combination by LP, then rigorous residual
    Ld = matrix(RDF, 30, 30, [z.mid() for z in Lm.list()])
    U, S, V = Ld.transpose().SVD()
    sv = S.diagonal()
    K3 = V[:, 27:30]  # right singular vectors of L^T for the 3 smallest singular values
    p = MixedIntegerLinearProgram(maximization=True, solver="GLPK")
    g = p.new_variable(real=True, nonnegative=False)
    sm = p.new_variable(real=True, nonnegative=False)
    for k in range(30):
        p.add_constraint(sum(K3[k, m] * g[m] for m in range(3)) >= sm[0])
    p.add_constraint(sum(sum(K3[k, m] * g[m] for m in range(3)) for k in range(30)) == 1)
    p.set_objective(sm[0])
    p.solve()
    gv = p.get_values(g)
    omega = [QQ(round(RDF(sum(K3[k, m] * gv[m] for m in range(3))) * 10**15)) / 10**15 for k in range(30)]
    wmin = min(omega)
    assert wmin > 0
    eps = vector(RBr, omega) * Lm
    epsn = RI(sum(RI(abs(z).upper()) ** 2 for z in eps)).sqrt().upper()
    W = sum(omega) / wmin
    c_lo = ((sigma_lo / RI(30).sqrt() - RI(epsn) / RI(wmin)) / RI(W)).lower()
    r = (RI(c_lo) / ((1 + RI(uB.upper())) * RI(101) / 100 * RI(15).sqrt())).lower()
    ok = RI(15).sqrt() * RI(r) <= RI(1) / 10
    assert max(sv[27:30]) < 1e-12
    assert epsn < 1e-14
    assert abs(sum(omega) - 1) < 10**-12
    print("%s: singular values of L^T: the 3 smallest are below 1e-12" % nm)
    print("%s: lambda_min(A) >= %s (rational Cholesky at %s, radius < 1e-100); sigma >= %s" % (nm, sci(lam_lo.lower().exact_rational(), False), dec(lam0, False, 6), sci(sigma_lo.lower().exact_rational(), False)))
    print("%s: stress omega > 0: min >= %s, sum 1 within 1e-12, W <= %s, |eps| < 1e-14" % (nm, sci(wmin, False), sci(W, True)))
    print("%s: c >= %s ; radius r >= %s (per point, Euclidean), sqrt(15) r <= 0.1: %s" % (nm, sci(c_lo.exact_rational(), False), sci(r.exact_rational(), False), ok))
    res[nm] = (c_lo, r)
    # the strictly positive stress and exact contact list, for the record
    print("%s: contacts %s" % (nm, cont))
    print("%s: omega [%s]" % (nm, ", ".join("%.6e" % RDF(w) for w in omega)))
print("minimum radius over all configurations >= %s" % sci(min(v[1] for v in res.values()).exact_rational(), False))
