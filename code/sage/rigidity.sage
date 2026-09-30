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
    radF = sqrt(RealField(100)(sum((z.rad()) ** 2 for z in A.list())))
    ev = sorted(matrix(RDF, Am).eigenvalues())
    lam0 = QQ(round(RDF(ev[0]) * 0.99 * 10**12)) / 10**12
    assert (Am - lam0 * identity_matrix(QQ, 30)).is_positive_definite()
    lam_lo = RealField(100)(lam0) - radF
    sigma_lo = sqrt(lam_lo)
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
    epsn = sqrt(sum((abs(z).upper()) ** 2 for z in eps))
    W = sum(omega) / wmin
    c_lo = (sigma_lo / sqrt(RealField(100)(30)) - RealField(100)(epsn) / RealField(100)(wmin)) / RealField(100)(W)
    uhi = RealField(100)(uB.upper())
    r = c_lo / ((1 + uhi) * RealField(100)(1.01) * sqrt(RealField(100)(15)))
    ok = sqrt(RealField(100)(15)) * r <= 0.1
    assert max(sv[27:30]) < 1e-12
    assert epsn < 1e-14
    print("%s: singular values of L^T: the 3 smallest are below 1e-12" % nm)
    print("%s: lambda_min(A) >= %.6e (rational Cholesky at %.6e, radius %.2e); sigma >= %.6e" % (nm, lam_lo, RealField(53)(lam0), radF, sigma_lo))
    print("%s: stress omega > 0: min %.6e, sum %.6e, W = %.4f, |eps| < 1e-14" % (nm, RDF(wmin), RDF(sum(omega)), RDF(W)))
    print("%s: c >= %.6e ; radius r = %.6e (per point, Euclidean), sqrt(15) r <= 0.1: %s" % (nm, c_lo, r, ok))
    res[nm] = (c_lo, r)
    # the strictly positive stress and exact contact list, for the record
    print("%s: contacts %s" % (nm, cont))
    print("%s: omega [%s]" % (nm, ", ".join("%.6e" % RDF(w) for w in omega)))
# rounded down to 6 significant digits
rmin = min(v[1] for v in res.values()).exact_rational()
e = floor(RR(rmin).log10())
while floor(rmin / 10**(e - 5)) >= 10**6: e += 1
while floor(rmin / 10**(e - 5)) < 10**5: e -= 1
m = int(floor(rmin / 10**(e - 5)))
print("minimum radius over all configurations >= %d.%05de%+03d" % (m // 10**5, m % 10**5, e))
