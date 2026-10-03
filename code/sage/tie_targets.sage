# Targets of the tie-window discard "Local" (Section 6.3): the 8 configurations
# obtained from the Buddenhagen-Kottwitz frame by keeping one point of each toggle pair
# (P,B), (I,Q), (A,J); each is congruent to C3 or C1 (checked here by the exact contact count and
# the degree-5 pattern). Output data/tie_targets.txt: per configuration a line "conf NAME TYPE",
# 15 lines "x_mid x_rad y_mid y_rad z_mid z_rad" (decimal, 40 digits), a line "contacts i j ...".
load("code/sage/bk15_exact.sage")
import itertools
base = [1,2,3,4,5,6,13,14,15,16,17,18]
pairs = [(7,12), (8,10), (9,11)]
out = open("data/tie_targets.txt", "w")
out.write("# 8 frame configurations (one point of each toggle pair), exact contacts; from code/sage/tie_targets.sage\n")
def bs2(z): return "%s %s" % (z.mid().str(digits=40), (z.rad() + RealField(53)(1e-38)).str(digits=3))
for choice in itertools.product([0,1], repeat=3):
    keep = sorted(base + [pairs[m][choice[m]] for m in range(3)])
    X = [F[k-1] for k in keep]
    cont = [(i, j) for i in range(15) for j in range(i+1, 15) if ip(X[i], X[j]) == u]
    for i in range(15):
        for j in range(i+1, 15):
            if (i, j) not in cont:
                assert tob(ip(X[i], X[j])) - uB < RB(-1)/10
    deg = [sum(1 for (a, b) in cont if i in (a, b)) for i in range(15)]
    d5 = [i for i in range(15) if deg[i] == 5]
    e5 = sum(1 for (a, b) in cont if a in d5 and b in d5)
    typ = "C3" if e5 == 3 else ("C1" if e5 == 1 else "?")
    name = "".join(names[k-1] + "," for k in keep if 7 <= k <= 12)
    print(choice, name, "contacts", len(cont), "type", typ)
    assert len(cont) == 30 and typ != "?"
    out.write("conf %s %s\n" % (name.rstrip(","), typ))
    for p in X:
        out.write(" ".join(bs2(tob(q)) for q in p) + "\n")
    out.write("contacts " + " ".join("%d %d" % c for c in cont) + "\n")
out.close()
