# Run from the repository root: OUT=DIR sage code/lean-data/d1_lp.sage (DIR receives d1_lp_cert_C1.txt, d1_lp_cert_C3.txt)
# D1, floating point, no rigour: the linear program that finds the certificate of Tammes15/Kappa/. A certificate with no SOS part,
#   R^2 - |y|^2 = sum_i lam_i s_i + sum_{i<=j} mu_ij s_i s_j,   s_i = 1 - l_i y,   lam, mu >= 0,
# an identity of quadratic polynomials on T' (27 variables), is a solution of a linear program (406 equations,
# 496 unknowns). Its optimum is an upper bound on R_max^2 = max |y|^2 over P = {y : l_i y <= 1};
# when it equals the vertex value, D1 needs no vertex enumeration and no PSD check (only a positive
# combination, plus a small diagonal margin to absorb the rounding of the data).
# Output: code/lean-data/d1_lp.out
import itertools, os
from cvxopt import matrix as cm, solvers
solvers.options['show_progress'] = False
solvers.options['maxiters'] = int(400)
solvers.options['abstol'] = float(1e-10); solvers.options['reltol'] = float(1e-12); solvers.options['feastol'] = float(1e-10)
lines = open("data/bk15_exact.txt").read().splitlines()
pts = {}
for ln in lines:
    w = ln.split()
    if len(w) == 7 and w[0][0] in "VPIAQJBW":
        pts[w[0]] = vector(RDF, [RDF(w[1]), RDF(w[3]), RDF(w[5])])
names = ["V1","V2","V3","V12","V23","V31","P","I","A","Q","J","B","W12","W23","W31","W1","W2","W3"]
import ast
keep = {}; cont = {}
for ln in lines:
    w = ln.split(None, 2)
    if len(w) == 3 and w[1] == "keep": keep[w[0]] = ast.literal_eval(w[2])
    if len(w) == 3 and w[1] == "contacts": cont[w[0]] = ast.literal_eval(w[2])
def cross(a, b): return vector(RDF, [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]])
for nm in ["C1", "C3"]:
    X = [pts[names[k-1]] for k in keep[nm]]
    S = cont[nm]
    # tangent orthonormal bases
    E = []
    for p in X:
        ax = min(range(3), key=lambda k: abs(p[k]))
        a = vector(RDF, [1 if k == ax else 0 for k in range(3)])
        e1 = cross(a, p); e1 = e1 / e1.norm(); e2 = cross(p, e1)
        E.append((e1, e2))
    Lm = matrix(RDF, 30, 30); Qm = matrix(RDF, 3, 30)
    for r, (i, j) in enumerate(S):
        for (k, o) in [(j, i), (i, j)]:
            Lm[r, 2*k] += X[o] * E[k][0]; Lm[r, 2*k+1] += X[o] * E[k][1]
    for w in range(3):
        om = vector(RDF, [1 if k == w else 0 for k in range(3)])
        for k in range(15):
            v = cross(om, X[k]); Qm[w, 2*k] = v * E[k][0]; Qm[w, 2*k+1] = v * E[k][1]
    # orthonormal basis of T' = kernel of Qm in the 30-dim tangent coordinates
    N = Qm.right_kernel_matrix()          # rows span T'
    Bt = N.transpose()
    Qo, _ = Bt.QR()
    Bt = Qo[:, :27]                        # 30 x 27 orthonormal
    ell = Lm * Bt                          # 30 x 27: rows are l_i in T' coordinates
    import numpy as np
    n = 27
    R0 = float(150.0)
    E0 = np.array(ell, dtype=float) * R0     # x = y / R0
    # vertex value, for comparison
    Rmax2 = 0
    for Bs in itertools.combinations(range(30), 3):
        A = [e for e in range(30) if e not in Bs]
        M = E0[A]
        if abs(np.linalg.det(M)) < 1e-10: continue
        xx = np.linalg.solve(M, np.ones(27))
        if (E0[list(Bs)] @ xx).max() <= 1 + 1e-9: Rmax2 = max(Rmax2, xx @ xx)
    pairs = [(i, j) for i in range(30) for j in range(i, 30)]
    quad = [(a, b) for a in range(n) for b in range(a, n)]
    nv = 1 + 30 + len(pairs)                  # R2, lam, mu
    neq = 1 + n + len(quad)
    A = np.zeros((neq, nv)); rhs = np.zeros(neq)
    # constant term: R2 - sum lam - sum mu = 0
    A[0, 0] = 1; A[0, 1:31] = -1; A[0, 31:] = -1
    # linear terms: sum lam_i l_i + sum mu_ij (l_i + l_j) = 0
    for a in range(n):
        A[1 + a, 1:31] = E0[:, a]
        for k, (i, j) in enumerate(pairs):
            A[1 + a, 31 + k] = E0[i, a] + E0[j, a]
    # quadratic terms: sum mu_ij sym(l_i l_j)_{ab} = -delta_ab
    for q, (a, b) in enumerate(quad):
        row = 1 + n + q
        for k, (i, j) in enumerate(pairs):
            A[row, 31 + k] = E0[i, a] * E0[j, b] + (E0[i, b] * E0[j, a] if a != b else 0)
        rhs[row] = -1 if a == b else 0
    c = np.zeros(nv); c[0] = 1
    G = np.zeros((nv - 1, nv)); G[:, 1:] = -np.eye(nv - 1); h = np.zeros(nv - 1)
    solvers.options['maxiters'] = int(200)
    sol = solvers.lp(cm(c), cm(G), cm(h), cm(A), cm(rhs))
    print(nm, "vertex R_max = %.7f" % (sqrt(Rmax2) * R0))
    print(nm, "LP status", sol['status'], " primal residual %.2e dual residual %.2e" % (sol['primal infeasibility'] or -1, sol['dual infeasibility'] or -1))
    if sol['x'] is not None:
        xs = np.array(sol['x']).ravel()
        print(nm, "LP bound R = %.7f  ratio to vertex value %.9f  equation residual %.2e  min multiplier %.2e" % (sqrt(max(xs[0], 0)) * R0, sqrt(max(xs[0], 0) / Rmax2), np.abs(A @ xs - rhs).max(), xs[1:].min()))
    # rank of the quadratic part: can sums of mu_ij sym(l_i l_j), mu >= 0, reach -I at all?
    rk = np.linalg.matrix_rank(A[1 + n:, 31:])
    print(nm, "rank of the quadratic block", rk, "of", len(quad), "equations")
    # checks of the certificate: identity at random points, value at the maximising vertex, supports
    xs = np.array(sol['x']).ravel(); R2 = xs[0]; lam = xs[1:31]; mu = xs[31:]
    rng = np.random.default_rng(int(7))
    worst = 0
    for trial in range(20):
        y = rng.normal(size=int(n)) * float(0.5)
        sv = 1 - E0 @ y
        rhs_v = lam @ sv + sum(mu[k] * sv[i] * sv[j] for k, (i, j) in enumerate(pairs))
        worst = max(worst, abs((R2 - y @ y) - rhs_v) / (1 + y @ y))
    print(nm, "identity R2 - |x|^2 = sum lam s + sum mu s s at 20 random points: max relative residual %.2e" % worst)
    print(nm, "multipliers above 1e-9: lam %d of 30, mu %d of %d (squares %d)" % ((lam > 1e-9).sum(), (mu > 1e-9).sum(), len(pairs), sum(1 for k, (i, j) in enumerate(pairs) if i == j and mu[k] > 1e-9)))
    np.savetxt(os.environ["OUT"] + "/d1_lp_cert_%s.txt" % nm, xs, fmt="%.17e", header="%s: R2 (scaled by 1/150^2), lam_i (i < 30), mu_ij (i <= j, row-major); x = y / 150" % nm)
