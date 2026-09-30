\\ Numeric test of the Lean definitions of Tammes15/Hyps/Case.lean on the
\\ configurations of data/genuine: optima.txt (C1, C3, the six other frame configurations
\\ and their mirror images, at d = psi*) and flex-C1.txt, flex-C3.txt (realisations of subgraphs of
\\ the contact graphs of C1 and C3, some with free points).
\\
\\ Every object is rebuilt from the points and the edges with the formulas of the Lean files, not
\\ with the library's rotation systems or faces (which are compared at the end): `ocorner`
\\ (Draw/Defs.lean), the angular rotation (`IsAngular`: the next dart has the least corner), the face
\\ permutation (`RotSys.face`: reverse, then `rot.symm`), `alpha`, `rho`, `ebase`, `bangle`, `eta`,
\\ `gam` (Trigrows/Defs.lean), `longDiag` (Case.lean), `dlo`, `dhi` (Trigrows/Margins.lean), with
\\ Lean's clamped `arccos` and `arcsin`. For each record it evaluates:
\\   InClass: 3-connectivity, degrees 3 to 5, faces of size 3 to 6, V - E + F = 2;
\\   Realisation: every field (edge, unit, angular uniqueness margin, convex = StrictSupportFace,
\\     corners in [alpha d, pi), sep, inside) with the free points in their hexagons (HexChoice);
\\   RelSys on assignOf: every field, for every base dart (every rotation of every face) and every
\\     rotation of the base dart of each hexagon with a free point;
\\   glueY (Case.lean, with stepM, rotZ, rotY, flipZ of Glue/): for every root, the first dart at
\\     the root, a breadth-first tree and every freeCorner, the Gram matrix against the points
\\     (glue_congruent claims a linear isometry) and the sign of one triple product;
\\   the d range dlo <= d <= dhi of the reduction for the records at d = psi* (the others, at
\\     d = psi* - delta, print d - dlo for information: delta >= 1e-7 puts them below dlo).
\\ Negative controls at the end: four deliberately wrong conventions, each of which must fail some
\\ check on a record with a free point.
\\ Equalities pass at |residual| < TOL, inequalities at slack > -TOL (strict ones at slack > TOL).
\\ Run: sh code/hyps/run_check.sh (60 digits); log code/hyps/check.out.

read("genuine_lib.gp");
TOL = 1e-30;
PSI = acos(ustar());

\\ ---------- the Lean definitions ----------
lacos(t) = if(t >= 1, 0, if(t <= -1, Pi, acos(t)));
lasin(t) = if(t >= 1, Pi/2, if(t <= -1, -Pi/2, asin(t)));
ldiv(a, b) = if(b == 0, 0, a / b);
ltan(x) = ldiv(sin(x), cos(x));
lcot(x) = ldiv(cos(x), sin(x));
lsdist(p, q) = lacos(dot3(p, q));
tdir(v, w) = w - dot3(v, w) * v;
ocorner(v, a, b) = {
  my(ta = tdir(v, a), tb = tdir(v, b), z, t);
  z = dot3(ta, tb) + I * dot3(v, cross3(ta, tb));
  t = if(z == 0, 0, arg(z));
  t = if(t < 0, t + 2 * Pi, t);
  if(MUTANT == 4 && t > 0, 2 * Pi - t, t);
}
lalpha(d) = lacos(ldiv(cos(d), 1 + cos(d)));
lrho(d, x) = Pi - 2 * atan(if(MUTANT == 3, 1, cos(d)) * ltan(x / 2));
lebase(d, u) = 2 * lasin(sin(d) * sin(u / 2));
lbangle(d, u) = atan(ldiv(cos(u / 2), cos(d) * sin(u / 2)));
leta(g, e, f) = ldiv(cos(g) - cos(e) * cos(f), sin(e) * sin(f));
lgam(g, e, f) = lacos(leta(g, e, f));
llongDiag(d, u) = lbangle(d, u) + lacos(min(1, lcot(d) * ltan(lebase(d, u) / 2)));
LDLO = 5365785 / 100000 * (Pi / 180);
LDHI = 566716 / 10000 * (Pi / 180);
rotZ(t) = [cos(t), -sin(t), 0; sin(t), cos(t), 0; 0, 0, 1];
rotY(t) = [cos(t), 0, sin(t); 0, 1, 0; -sin(t), 0, cos(t)];
flipZ = [-1, 0, 0; 0, -1, 0; 0, 0, 1];
MUTANT = 0;
stepM(p, t) = if(MUTANT == 2, rotZ(p) * rotY(t), rotZ(p) * rotY(t) * flipZ);
E3 = [0, 0, 1]~;

\\ ---------- bookkeeping of the checks ----------
\\ S: Map name -> [worst value, kind] with kind "eq" (max |res|), "ge" (min slack), "gt" (min slack)
chk(~S, name, kind, val) = {
  my(w);
  if(!mapisdefined(S, name), mapput(S, name, [val, kind]); return);
  w = mapget(S, name)[1];
  if(kind == "eq", if(abs(val) > w, mapput(S, name, [abs(val), kind])),
    if(val < w, mapput(S, name, [val, kind])));
}
chkeq(~S, name, res) = chk(~S, name, "eq", abs(res));
chkge(~S, name, slack) = chk(~S, name, "ge", slack);
chkgt(~S, name, slack) = chk(~S, name, "gt", slack);
chkbool(~S, name, b) = chk(~S, name, "ge", if(b, 1, -1));
passes(v) = if(v[2] == "info", 1, if(v[2] == "eq", v[1] < TOL, if(v[2] == "ge", v[1] > -TOL, v[1] > TOL)));
chkinfo(~S, name, val) = mapput(S, name, [val, "info"]);

\\ ---------- one record: helpers ----------
\\ darts of the edges, both orientations; DI maps a dart to its index
mkdarts(E) = {
  my(D = List(), DI = Map());
  for(k = 1, #E, listput(D, [E[k][1], E[k][2]]); listput(D, [E[k][2], E[k][1]]));
  D = Vec(D);
  for(i = 1, #D, mapput(DI, D[i], i));
  [D, DI];
}
\\ angular rotation (IsAngular): after the dart v -> w comes the dart at v with the least corner;
\\ returns [rot, least gap between the two smallest corners]
angularrot(X, D) = {
  my(nd = #D, rot = vector(nd), gap = oo, v, w, best, bj, second, val);
  for(i = 1, nd,
    v = D[i][1]; w = D[i][2]; best = oo; bj = i; second = oo;
    for(j = 1, nd,
      if(D[j][1] == v && j != i,
        val = ocorner(X[v], X[w], X[D[j][2]]);
        if(val < best, second = best; best = val; bj = j, if(val < second, second = val))));
    rot[i] = bj;
    if(second < oo, gap = min(gap, second - best)));
  [rot, gap];
}
\\ (face ^ j) i
fpow(face, i, j) = {
  my(t = i);
  for(s = 1, j, t = face[t]);
  t;
}
\\ number of connected components of the graph on V minus del (a sorted set)
ncomp(N, V, E, del) = {
  my(mark = vector(N), cnt = 0, st, x, y);
  for(a = 1, #V,
    if(!mark[V[a]] && !setsearch(del, V[a]),
      cnt++; st = List([V[a]]); mark[V[a]] = 1;
      while(#st,
        x = st[#st]; listpop(st);
        for(k = 1, #E,
          y = if(E[k][1] == x, E[k][2], if(E[k][2] == x, E[k][1], 0));
          if(y && !mark[y] && !setsearch(del, y), mark[y] = 1; listput(st, y))))));
  cnt;
}
\\ the angle turned at a vertex from dart a to dart b: the corners passed
turnang(A, rot, a, b) = {
  my(t = a, s = 0, acc = 0);
  while(t != b, acc += A[t]; t = rot[t]; s++; if(s > #rot, error("turn: not at the same vertex")));
  acc;
}
modi(j, m) = ((j % m) + m) % m + 1;

\\ ---------- one record ----------
checkrecord(r) = {
  my(c = cfgparse(r), X = c[1], d = c[2], E = c[3], rt = c[4], LF = c[6], N, S = Map(),
    isv, V, D, DI, nd, ra, rot, rotinv, face, per, deg, k, e, f, val, v, w, F, nf, seen, ok,
    free, base, A, u, e1, e3, e5, f1, b, uu, r6, root, rootDart, order, q, par, depth, frame,
    Y, ed, Ai, ri, ri1, i0, sgnx, sgny, lib, mine, vs, p0, fcs);
  N = #X;
  isv = vector(N, i, 1); for(k = 1, #rt, isv[rt[k]] = 0);
  V = select(i -> isv[i], [1..N]);
  [D, DI] = mkdarts(E); nd = #D;
  deg = vector(N, i, #select(t -> t[1] == i, D));
  ra = angularrot(X, D); rot = ra[1];
  chkgt(~S, "angular: least corner unique (gap)", ra[2]);
  rotinv = vector(nd); for(i = 1, nd, rotinv[rot[i]] = i);
  chkbool(~S, "angular: rot is a permutation", #Set(rot) == nd);
  chkbool(~S, "angular: rot keeps the vertex", #select(i -> D[rot[i]][1] != D[i][1], [1..nd]) == 0);
  \\ face permutation: reverse, then rot.symm
  face = vector(nd, i, if(MUTANT == 1, rot, rotinv)[mapget(DI, [D[i][2], D[i][1]])]);
  per = vector(nd);
  for(i = 1, nd, k = 1; e = face[i]; while(e != i, e = face[e]; k++); per[i] = k);
  F = List(); seen = vector(nd);
  for(i = 1, nd,
    if(!seen[i],
      f = List(); e = i;
      until(e == i, seen[e] = 1; listput(f, e); e = face[e]);
      listput(F, Vec(f))));
  F = Vec(F); nf = #F;
  \\ ---- InClass
  chkbool(~S, "InClass: degrees 3 to 5", #select(v -> deg[v] < 3 || deg[v] > 5, V) == 0);
  chkbool(~S, "InClass: face sizes 3 to 6", #select(i -> per[i] < 3 || per[i] > 6, [1..nd]) == 0);
  chkeq(~S, "InClass: V - E + F - 2", #V - #E + nf - 2);
  ok = #V > 3 && ncomp(N, V, E, []) == 1;
  for(a = 1, #V,
    if(ncomp(N, V, E, [V[a]]) != 1, ok = 0);
    for(b = a + 1, #V, if(ncomp(N, V, E, Set([V[a], V[b]])) != 1, ok = 0)));
  chkbool(~S, "InClass: KConnected 3", ok);
  \\ ---- Realisation
  chkgt(~S, "Realisation: 0 < d", d); chkgt(~S, "Realisation: d < pi/2", Pi / 2 - d);
  for(i = 1, N, chkeq(~S, "Realisation: unit", nrm3(X[i]) - 1));
  for(k = 1, #E, chkeq(~S, "Realisation: edge sdist = d", lsdist(X[E[k][1]], X[E[k][2]]) - d));
  for(i = 1, N, for(j = i + 1, N, chkge(~S, "Realisation: sep", lsdist(X[i], X[j]) - d)));
  A = vector(nd, i, ocorner(X[D[i][1]], X[D[i][2]], X[D[rot[i]][2]]));
  for(i = 1, nd,
    chkge(~S, "Realisation: corner >= alpha d", A[i] - lalpha(d));
    chkgt(~S, "Realisation: corner < pi", Pi - A[i]));
  for(i = 1, nd,
    e = i;
    for(n = 0, per[i] - 1,
      if(e != i && e != face[i],
        chkgt(~S, "Realisation: convex (StrictSupportFace)",
          dot3(cross3(X[D[i][1]], X[D[i][2]]), X[D[e][1]])));
      e = face[e]));
  \\ HexChoice: the face of each free point
  free = rt; base = vector(#free);
  for(m = 1, #free,
    k = 0;
    for(qq = 1, nf,
      f = F[qq];
      if(vecmin(vector(#f, j, dot3(cross3(X[D[f[j]][1]], X[D[f[j]][2]]), X[free[m]]))) > 0,
        k++; base[m] = f[1]));
    chkbool(~S, "HexChoice: free point strictly inside exactly one face", k == 1);
    if(k == 1, chkbool(~S, "HexChoice: its face has size 6", per[base[m]] == 6)));
  chkbool(~S, "HexChoice: distinct faces", #Set(base) == #base);
  for(m = 1, #free, for(j = 0, 5,
    chkgt(~S, "Realisation: inside",
      dot3(cross3(X[D[fpow(face, base[m], j)][1]], X[D[fpow(face, base[m], j)][2]]), X[free[m]]))));
  \\ ---- assignOf and RelSys
  for(a = 1, #V,
    chkeq(~S, "RelSys: vertex_sum", sum(i = 1, nd, if(D[i][1] == V[a], A[i], 0)) - 2 * Pi));
  for(i = 1, nd,
    u = vector(per[i], j, A[fpow(face, i, j - 1)]);
    if(per[i] == 3, chkeq(~S, "RelSys: tri", A[i] - lalpha(d)));
    if(per[i] == 4,
      chkeq(~S, "RelSys: rhombus fc2 = fc0", u[3] - u[1]);
      chkeq(~S, "RelSys: rhombus fc1 = rho d fc0", u[2] - lrho(d, u[1])));
    if(per[i] == 5,
      e1 = lebase(d, u[2]); f1 = lebase(d, u[5]);
      chkge(~S, "RelSys: pent eta in [-1,1]", 1 - abs(leta(d, e1, f1)));
      chkge(~S, "RelSys: pent eta in [-1,1]", 1 - abs(leta(f1, e1, d)));
      chkge(~S, "RelSys: pent eta in [-1,1]", 1 - abs(leta(e1, f1, d)));
      chkeq(~S, "RelSys: pent u0", u[1] - (lbangle(d, u[2]) + lgam(d, e1, f1) + lbangle(d, u[5])));
      chkeq(~S, "RelSys: pent u2", u[3] - (lbangle(d, u[2]) + lgam(f1, e1, d)));
      chkeq(~S, "RelSys: pent u3", u[4] - (lbangle(d, u[5]) + lgam(e1, f1, d))));
    if(per[i] == 6,
      e1 = lebase(d, u[2]); e3 = lebase(d, u[4]); e5 = lebase(d, u[6]);
      chkge(~S, "RelSys: hex eta in [-1,1]", 1 - abs(leta(e3, e1, e5)));
      chkge(~S, "RelSys: hex eta in [-1,1]", 1 - abs(leta(e5, e1, e3)));
      chkge(~S, "RelSys: hex eta in [-1,1]", 1 - abs(leta(e1, e3, e5)));
      chkeq(~S, "RelSys: hex u0", u[1] - (lbangle(d, u[6]) + lgam(e3, e1, e5) + lbangle(d, u[2])));
      chkeq(~S, "RelSys: hex u2", u[3] - (lbangle(d, u[2]) + lgam(e5, e1, e3) + lbangle(d, u[4])));
      chkeq(~S, "RelSys: hex u4", u[5] - (lbangle(d, u[4]) + lgam(e1, e3, e5) + lbangle(d, u[6])));
      chkge(~S, "RelSys: hexDiag", u[2] - llongDiag(d, u[1]));
      chkge(~S, "RelSys: hexDiag", u[1] - llongDiag(d, u[2]))));
  \\ wheels, for every rotation s of the base dart of each hexagon with a free point
  for(m = 1, #free, for(s = 0, 5,
    b = fpow(face, base[m], s);
    uu = vector(6, j, A[fpow(face, b, j - 1)]);
    r6 = vector(6, j, lsdist(X[free[m]], X[D[fpow(face, b, j - 1)][1]]));
    for(j = 0, 5,
      chkge(~S, "RelSys: wheel d <= r", r6[modi(j, 6)] - d);
      chkge(~S, "RelSys: wheel r <= 3d", 3 * d - r6[modi(j, 6)]);
      chkge(~S, "RelSys: wheel eta in [-1,1]", 1 - abs(leta(d, r6[modi(j, 6)], r6[modi(j + 1, 6)])));
      chkge(~S, "RelSys: wheel eta in [-1,1]", 1 - abs(leta(r6[modi(j + 1, 6)], r6[modi(j, 6)], d)));
      chkge(~S, "RelSys: wheel eta in [-1,1]", 1 - abs(leta(r6[modi(j - 1, 6)], r6[modi(j, 6)], d)));
      chkeq(~S, "RelSys: wheel u = gam + gam", uu[modi(j, 6)]
        - (lgam(r6[modi(j + 1, 6)], r6[modi(j, 6)], d) + lgam(r6[modi(j - 1, 6)], r6[modi(j, 6)], d))));
    chkeq(~S, "RelSys: wheel angle sum 2 pi",
      sum(j = 0, 5, lgam(d, r6[modi(j, 6)], r6[modi(j + 1, 6)])) - 2 * Pi)));
  \\ ---- glueY for every root, the first dart at the root, a BFS tree, every freeCorner
  i0 = V[1..4];
  sgnx = sign(dot3(cross3(X[i0[1]] - X[i0[4]], X[i0[2]] - X[i0[4]]), X[i0[3]] - X[i0[4]]));
  for(a = 1, #V,
    root = V[a];
    rootDart = select(i -> D[i][1] == root, [1..nd])[1];
    order = List([root]); q = 1;
    par = vector(N); depth = vector(N, i, -1); depth[root] = 0;
    while(q <= #order,
      v = order[q]; q++;
      for(i = 1, nd,
        if(D[i][1] == v && depth[D[i][2]] < 0,
          depth[D[i][2]] = depth[v] + 1; par[D[i][2]] = i; listput(order, D[i][2]))));
    chkbool(~S, "glue: BFS tree spans", #order == #V);
    \\ refD v = rootDart at the root, the dart back to the parent elsewhere
    fcs = vector(N, x, if(x == root, rootDart, if(par[x], mapget(DI, [D[par[x]][2], D[par[x]][1]]), 0)));
    frame = vector(N); frame[root] = matid(3);
    for(qq = 2, #order,
      v = order[qq]; w = D[par[v]][1];
      frame[v] = frame[w] * stepM(turnang(A, rot, fcs[w], par[v]), d));
    for(fcn = 0, 5,
      Y = vector(N);
      for(t = 1, #V, Y[V[t]] = (frame[V[t]] * E3)~);
      for(m = 1, #free,
        ed = fpow(face, base[m], fcn); Ai = D[ed][1];
        ri = lsdist(X[free[m]], X[Ai]);
        ri1 = lsdist(X[free[m]], X[D[fpow(face, base[m], (fcn + 1) % 6)][1]]);
        Y[free[m]] = (frame[Ai] * rotZ(turnang(A, rot, fcs[Ai], ed) + lgam(ri1, ri, d)) * rotY(ri) * E3)~);
      for(x = 1, N, for(y = x, N,
        chkeq(~S, "glue: Gram of glueY = Gram of x", dot3(Y[x], Y[y]) - dot3(X[x], X[y]))));
      sgny = sign(dot3(cross3(Y[i0[1]] - Y[i0[4]], Y[i0[2]] - Y[i0[4]]), Y[i0[3]] - Y[i0[4]]));
      chkbool(~S, "glue: orientation kept", sgny == sgnx)));
  \\ ---- d range of the reduction
  if(abs(d - PSI) < TOL,
    chkge(~S, "range at d = psi*: dlo <= d", d - LDLO); chkge(~S, "range at d = psi*: d <= dhi", LDHI - d),
    chkinfo(~S, "range, d below psi* (not in the reduction when < 0): d - dlo", d - LDLO));
  \\ ---- comparison with the faces traced by genuine_lib.gp
  lib = Set(LF);
  mine = List();
  for(qq = 1, nf,
    vs = vector(#F[qq], j, D[F[qq][j]][1]);
    p0 = select(t -> t == vecmin(vs), vs, 1)[1];
    listput(mine, vector(#vs, j, vs[((p0 + j - 2) % #vs) + 1])));
  chkbool(~S, "library: same faces", lib == Set(Vec(mine)));
  [recname(r), S, [N, #V, #E, nf, #free]];
}

\\ ---------- driver ----------
report(res, expect) = {
  my(S = res[2], ks = vecsort(Vec(S)), bad = List(), v);
  foreach(ks, k, v = mapget(S, k); if(!passes(v), listput(bad, k)));
  printf("%s: N=%d V=%d E=%d F=%d free=%d  %s\n", res[1], res[3][1], res[3][2], res[3][3], res[3][4], res[3][5],
    if(#bad, "FAILS", "all pass"));
  foreach(ks, k, v = mapget(S, k);
    printf("  %-58s %s %s\n", k, if(v[2] == "info", "info", if(passes(v), "ok  ", "FAIL")),
      if(v[2] == "eq", Strprintf("max|res| %.3e", v[1]), if(v[2] == "info", Strprintf("value %.3e", v[1]), Strprintf("min slack %.3e", v[1])))));
  Vec(bad);
}

allbad = List(); nrec = 0; npsi = 0; nfree = 0;
{
  foreach(["../../data/genuine/optima.txt", "../../data/genuine/flex-C1.txt", "../../data/genuine/flex-C3.txt"], path,
    print("== ", path);
    foreach(readlib(path), r,
      if(mapget(r, "kind")[1][1] != "config", next);
      nrec++; if(abs(recnum(r, "d") - PSI) < TOL, npsi++);
      nfree += #recget(r, "rattler");
      my(b = report(checkrecord(r)));
      foreach(b, k, listput(allbad, [recname(r), k]))));
}
print("== summary");
printf("records: %d, at d = psi*: %d, below psi*: %d; free points: %d\n", nrec, npsi, nrec - npsi, nfree);
my_fail_kinds = Set(apply(t -> t[2], Vec(allbad)));
printf("records with a failing check: %d; failing checks: %s\n", #Set(apply(t -> t[1], Vec(allbad))), my_fail_kinds);
\\ negative controls: each deliberately wrong convention must make some check fail on a record with
\\ a free point (1: face permutation with rot for rot.symm; 2: stepM without flipZ; 3: rho without the
\\ factor cos d; 4: corners measured clockwise)
print("== negative controls on C1-rattler-18");
ctl = select(r -> recname(r) == "C1-rattler-18", readlib("../../data/genuine/flex-C1.txt"))[1];
survived = 0;
{
  for(mu = 1, 4,
    MUTANT = mu;
    my(res = checkrecord(ctl), S = res[2], ks = vecsort(Vec(S)), bad = List());
    foreach(ks, k, if(!passes(mapget(S, k)), listput(bad, k)));
    printf("mutant %d: %d failing checks: %s\n", mu, #bad, Vec(bad));
    if(#bad == 0, survived++));
  MUTANT = 0;
}
if(survived, error("a negative control passed every check"));
if(#allbad, error("a check failed"));
print("END OK");
