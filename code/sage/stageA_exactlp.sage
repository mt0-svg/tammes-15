# Independent check of stage A (Section 6.2) by exact rational LP.
# For each graph of a planar_code file: faces traced from the rotation system, then the level-1
# system (Section 5.2): a in [alpha(dlo), alpha(dhi)], triangle corners = a, rhombus x (corners
# 0, 2), y (1, 3) with a <= x, y <= 2a, x + y >= 3a, x + y <= S(dhi), pentagon and hexagon corners in
# [a, pi], vertex sums = 2 pi. Every constant is replaced by a rational rounded outward (so this LP is
# a relaxation of the true one), and feasibility is decided exactly (GLPK exact simplex, rational).
# A graph that stage A killed but that this LP finds feasible would be a wrong kill.
# Usage: sage stageA_exactlp.sage IN.pc SURVIVORS.pc K NSAMPLE SEED > OUT
import os, sys, random
from sage.numerical.mip import MIPSolverException
R = RealField(300)
deg = R.pi()/180
dlo = R('53.65785')*deg
dhi = R('56.6716')*deg
alpha = lambda d: (d.cos()/(1 + d.cos())).arccos()
S = lambda d: 4*(1/d.cos().sqrt()).arctan()
def dn(x): return QQ(floor(x*2**50))/2**50
def up(x): return QQ(ceil(x*2**50))/2**50
ALO, AHI, SHI = dn(alpha(dlo)), up(alpha(dhi)), up(S(dhi))
PIHI, TPLO, TPHI = up(R.pi()), dn(2*R.pi()), up(2*R.pi())

def read_pc(path):
    b = open(path, 'rb').read()
    i = 0
    if b.startswith(b'>>planar_code<<'):
        i = 15
    out = []
    while i < len(b):
        n = b[i]; i += 1
        adj = []
        for v in range(n):
            nb = []
            while b[i] != 0:
                nb.append(b[i] - 1); i += 1
            i += 1
            adj.append(nb)
        out.append(adj)
    return out

def key(adj):
    return tuple(tuple(a) for a in adj)

def faces(adj):
    seen = set(); F = []
    for v0 in range(len(adj)):
        for j0 in range(len(adj[v0])):
            if (v0, j0) in seen: continue
            cyc = []; v, j = v0, j0
            while (v, j) not in seen:
                seen.add((v, j)); cyc.append(v)
                w = adj[v][j]
                i = adj[w].index(v)
                v, j = w, (i + 1) % len(adj[w])
            F.append(cyc)
    return F

def feasible(adj):
    F = faces(adj)
    if max(len(a) for a in adj) > 5 or any(not (3 <= len(c) <= 6) for c in F):
        return None
    p = MixedIntegerLinearProgram(solver="GLPK/exact", maximization=False)
    x = p.new_variable(real=True, nonnegative=False)
    a = x['a']
    p.add_constraint(a >= ALO); p.add_constraint(a <= AHI)
    corners = {v: [] for v in range(len(adj))}
    for f, c in enumerate(F):
        m = len(c)
        if m == 3:
            cv = [a, a, a]
        elif m == 4:
            X, Y = x[('x', f)], x[('y', f)]
            cv = [X, Y, X, Y]
            for Z in (X, Y):
                p.add_constraint(Z >= a); p.add_constraint(Z <= 2*a)
            p.add_constraint(X + Y >= 3*a); p.add_constraint(X + Y <= SHI)
        else:
            cv = [x[('u', f, i)] for i in range(m)]
            for Z in cv:
                p.add_constraint(Z >= a); p.add_constraint(Z <= PIHI)
        for i in range(m):
            corners[c[i]].append(cv[i])
    for v in corners:
        s = sum(corners[v])
        p.add_constraint(s >= TPLO); p.add_constraint(s <= TPHI)
    p.set_objective(a)
    try:
        p.solve()
        return True
    except MIPSolverException:
        return False

def stream_pc(path):
    f = open(path, 'rb')
    b = f.read(15)
    if b != b'>>planar_code<<':
        f.seek(0)
    buf = f.read()
    i = 0
    while i < len(buf):
        n = buf[i]; i += 1
        adj = []
        for v in range(n):
            j = buf.index(0, i)
            adj.append([c - 1 for c in buf[i:j]])
            i = j + 1
        yield adj

inp, surv, K, NS, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
Sv = set(key(g) for g in read_pc(surv))
random.seed(seed)
ntot = 0; ncls = 0; kept = []; res = []; nk = 0; found = set()
for g in stream_pc(inp):
    ntot += 1
    k = key(g)
    if k in Sv:
        found.add(k)
        if sum(1 for c in faces(g) if len(c) == 6) >= K:
            kept.append(g); ncls += 1
        continue
    if K > 0 and sum(1 for c in faces(g) if len(c) == 6) < K:
        continue
    ncls += 1; nk += 1
    if len(res) < NS:
        res.append(g)
    else:
        r = random.randrange(nk)
        if r < NS:
            res[r] = g
print("input %s: %d graphs, %d with >= %d hexagons, %d of them survivors of stage A, %d killed; testing all survivors and %d killed" % (os.path.basename(inp), ntot, ncls, K, len(kept), nk, len(res)))
bad = 0; ki = 0
for g in res:
    if feasible(g): bad += 1
    else: ki += 1
sf = 0; si = 0
for g in kept:
    if feasible(g): sf += 1
    else: si += 1
print("killed by stage A: LP infeasible %d, LP FEASIBLE (wrong kill) %d" % (ki, bad))
print("survivors of stage A: LP feasible %d, LP infeasible %d" % (sf, si))
print("survivor file graphs not found in the input: %d" % (len(Sv) - len(found)))
