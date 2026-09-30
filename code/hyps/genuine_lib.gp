\\ Spherical geometry and the text format of the configurations of data/genuine.
\\ Read by every script here; the caller sets realprecision (60 digits for the library).
\\ Points are t_VEC [x, y, z] of unit length; angles in radians.

\\ ---------- constants of the paper ----------
U_POL = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
ustar() = {
  my(r = select(t -> t > 1/2 && t < 7/10, polrootsreal(U_POL)));
  if(#r != 1, error("ustar: expected one root in (1/2, 7/10), got ", #r));
  r[1];
}
deg2rad(t) = t * Pi / 180;
rad2deg(t) = t * 180 / Pi;
DLO() = deg2rad(5365785/100000);
DHI() = deg2rad(566716/10000);
alpha(d) = acos(cos(d) / (1 + cos(d)));
hh(d) = acos(cos(d) / cos(d/2));

\\ ---------- vectors ----------
dot3(a, b) = a[1]*b[1] + a[2]*b[2] + a[3]*b[3];
cross3(a, b) = [a[2]*b[3] - a[3]*b[2], a[3]*b[1] - a[1]*b[3], a[1]*b[2] - a[2]*b[1]];
nrm3(a) = sqrt(dot3(a, a));
unit3(a) = a / nrm3(a);
\\ angular distance, accurate at every angle
sdist(a, b) = arg(dot3(a, b) + I*nrm3(cross3(a, b)));
\\ unit tangent at p pointing to q along the minor arc
tang(p, q) = unit3(q - dot3(p, q)*p);
\\ rotate the tangent vector t at p counterclockwise (seen from outside) by th
rotccw(p, t, th) = cos(th)*t + sin(th)*cross3(p, t);
\\ counterclockwise angle at p from the arc p->a to the arc p->b, in [0, 2 pi)
ccwangle(p, a, b) = {
  my(ta = tang(p, a), tb = tang(p, b), th);
  th = arg(dot3(ta, tb) + I*dot3(cross3(ta, tb), p));
  if(th < 0, th += 2*Pi);
  th;
}
\\ point at distance s from p in the tangent direction t (unit, orthogonal to p)
geo(p, t, s) = cos(s)*p + sin(s)*t;
\\ angle of the triangle with sides g, e, f opposite g
gam(g, e, f) = acos((cos(g) - cos(e)*cos(f)) / (sin(e)*sin(f)));

\\ ---------- random numbers ----------
unif(a, b) = a + (b - a)*random(1.);
gauss() = sqrt(-2*log(1 - random(1.))) * cos(2*Pi*random(1.));
\\ uniform random rotation matrix (from a uniform unit quaternion)
randrot() = {
  my(q = vector(4, i, gauss()), w, x1, y1, z1);
  q = q / sqrt(q*q~);
  [w, x1, y1, z1] = q;
  [1 - 2*(y1^2 + z1^2), 2*(x1*y1 - z1*w), 2*(x1*z1 + y1*w);
   2*(x1*y1 + z1*w), 1 - 2*(x1^2 + z1^2), 2*(y1*z1 - x1*w);
   2*(x1*z1 - y1*w), 2*(y1*z1 + x1*w), 1 - 2*(x1^2 + y1^2)];
}
applyrot(R, p) = (R * p~)~;
randpoint() = unit3([gauss(), gauss(), gauss()]);

\\ ---------- equilateral polygons ----------
\\ Chain A_0, A_1, ..., with A_0 = [1,0,0], A_1 at distance d, and interior corner cs[k] at A_k
\\ (face on the left, counterclockwise seen from outside). Returns [A_0, ..., A_{#cs+1}].
chain(d, cs) = {
  my(A = vector(#cs + 2), t);
  A[1] = [1, 0, 0]; A[2] = [cos(d), sin(d), 0];
  for(k = 1, #cs,
    t = rotccw(A[k+1], tang(A[k+1], A[k]), -cs[k]);
    A[k+2] = geo(A[k+1], t, d));
  A;
}
\\ Close the chain by the apex of the isosceles triangle on the base A_last A_0 (legs d),
\\ on the side of the face. Returns 0 if the apex does not exist.
closepoly(d, A) = {
  my(n = #A, P = A[n], e = sdist(P, A[1]), cb, t);
  if(e < 10^-30, return(0));
  cb = cos(d)*(1 - cos(e)) / (sin(e)*sin(d));
  if(cb > 1 || cb < -1, return(0));
  t = rotccw(P, tang(P, A[1]), -acos(cb));
  concat(A, [geo(P, t, d)]);
}
\\ interior corners of the closed polygon V (face on the left)
polycorners(V) = {
  my(m = #V);
  \\ a walk that turns back (degree-1 vertex: next = prev) has corner 2 pi
  vector(m, k, my(nx = V[(k % m) + 1], pv = V[((k - 2 + m) % m) + 1]); if(nx == pv, 2*Pi, ccwangle(V[k], nx, pv)));
}
\\ check that V is a genuine m-gon of side d: sides d, corners in [alpha(d), pi],
\\ non-adjacent vertices at distance >= d, every vertex on the closed left of every side,
\\ total turning below 2 pi. Returns [ok, reason, corners, min non-adjacent distance].
polycheck(V, d, tol) = {
  my(m = #V, u, a = alpha(d), md = 10, s, n, e, turn);
  for(k = 1, m, s = sdist(V[k], V[(k % m) + 1]); if(abs(s - d) > tol, return([0, "side", 0, 0])));
  u = polycorners(V);
  for(k = 1, m, if(u[k] < a - tol, return([0, "corner<alpha", u, 0])); if(u[k] > Pi + tol, return([0, "corner>pi", u, 0])));
  for(i = 1, m, for(j = i + 1, m,
    if(j - i == 1 || (i == 1 && j == m), next);
    md = min(md, sdist(V[i], V[j]))));
  if(m > 3 && md < d - tol, return([0, "diagonal<d", u, md]));
  for(k = 1, m, n = cross3(V[k], V[(k % m) + 1]);
    for(j = 1, m, if(dot3(V[j], n) < -tol, return([0, "not convex", u, md]))));
  turn = sum(k = 1, m, Pi - u[k]);
  if(turn >= 2*Pi - tol, return([0, "turning", u, md]));
  [1, "ok", u, if(m > 3, md, 0)];
}

\\ p strictly inside the convex polygon V (face on the left)
insidepoly(V, p) = {
  my(m = #V);
  for(k = 1, m, if(dot3(p, cross3(V[k], V[(k % m) + 1])) <= 0, return(0)));
  1;
}
mindistv(V, p) = vecmin(apply(t -> sdist(p, t), V));
\\ largest min-distance point inside the convex polygon V: best circumcentre of three vertices
\\ (on the boundary the min distance is at most half a side). Returns [min distance, point].
maxminpoint(V) = {
  my(m = #V, best = [-1, 0], n, p, s);
  forsubset([m, 3], T,
    n = cross3(V[T[2]] - V[T[1]], V[T[3]] - V[T[1]]);
    if(nrm3(n) == 0, next);
    n = unit3(n);
    for(sg = 0, 1, p = if(sg, -n, n);
      if(!insidepoly(V, p), next);
      s = mindistv(V, p);
      if(s > best[1], best = [s, p])));
  best;
}

\\ ---------- plane graphs from points ----------
\\ contact edges: pairs with |<x_i, x_j> - cos d| < tol
contactedges(X, d, tol) = {
  my(E = List(), c = cos(d));
  for(i = 1, #X, for(j = i + 1, #X, if(abs(dot3(X[i], X[j]) - c) < tol, listput(E, [i, j]))));
  Vec(E);
}
\\ rotation system: for each vertex its neighbours in counterclockwise order seen from outside,
\\ starting at the smallest label
rotsystem(X, E) = {
  my(n = #X, nb = vector(n, i, List()), R = vector(n), w, ang, perm);
  for(k = 1, #E, listput(nb[E[k][1]], E[k][2]); listput(nb[E[k][2]], E[k][1]));
  for(v = 1, n,
    w = vecsort(Vec(nb[v]));
    if(#w == 0, R[v] = []; next);
    ang = vector(#w, i, if(i == 1, 0, ccwangle(X[v], X[w[1]], X[w[i]])));
    perm = vecsort(ang, , 1);
    R[v] = vector(#w, i, w[perm[i]]));
  R;
}
\\ faces: boundary walks with the face on the left; next dart after (v, w) is (w, prev of v at w).
\\ Each face starts at its smallest vertex.
tracefaces(R) = {
  my(n = #R, used = Map(), F = List(), v, w, f, pos, x, best);
  for(v0 = 1, n, for(i = 1, #R[v0],
    if(mapisdefined(used, [v0, R[v0][i]]), next);
    f = List(); v = v0; w = R[v0][i];
    while(!mapisdefined(used, [v, w]),
      mapput(used, [v, w], 1); listput(f, v);
      pos = select(t -> t == v, R[w], 1)[1];
      x = R[w][if(pos == 1, #R[w], pos - 1)];
      v = w; w = x);
    f = Vec(f);
    best = vecmin(f); pos = select(t -> t == best, f, 1)[1];
    f = vector(#f, k, f[((pos + k - 2) % #f) + 1]);
    listput(F, f)));
  Vec(F);
}
\\ corners at every vertex: [v, w, w', angle] for consecutive w, w' of the rotation at v
vertexcorners(X, R) = {
  my(C = List(), k);
  for(v = 1, #R, k = #R[v]; if(k == 0, next);
    for(i = 1, k, listput(C, [v, R[v][i], R[v][(i % k) + 1], if(k == 1, 2*Pi, ccwangle(X[v], X[R[v][i]], X[R[v][(i % k) + 1]]))])));
  Vec(C);
}
facecorners(X, f) = polycorners(vector(#f, k, X[f[k]]));

\\ ---------- output ----------
\\ numbers as fixed point with 40 decimals
fmt(x) = Strprintf("%.40f", x);
fmtv(p) = Str(fmt(p[1]), " ", fmt(p[2]), " ", fmt(p[3]));
\\ write one configuration record to the open file fh
writeconfig(fh, name, infos, X, d, E, rattlers, rfaces) = {
  my(R = rotsystem(X, E), F, C);
  F = tracefaces(R);
  C = vertexcorners(X, R);
  filewrite(fh, Str("begin config ", name));
  for(i = 1, #infos, filewrite(fh, Str("info ", infos[i])));
  filewrite(fh, Str("n ", #X));
  filewrite(fh, Str("d ", fmt(d)));
  for(i = 1, #X, filewrite(fh, Str("point ", i, " ", fmtv(X[i]))));
  for(k = 1, #E, filewrite(fh, Str("edge ", E[k][1], " ", E[k][2])));
  for(k = 1, #rattlers, filewrite(fh, Str("rattler ", rattlers[k])));
  for(v = 1, #R, if(#R[v], filewrite(fh, Str("rot ", v, " ", #R[v], " ", strjoin(apply(t -> Str(t), R[v]), " ")))));
  for(k = 1, #C, filewrite(fh, Str("corner ", C[k][1], " ", C[k][2], " ", C[k][3], " ", fmt(C[k][4]))));
  for(k = 1, #F,
    filewrite(fh, Str("face ", k, " ", #F[k], " ", strjoin(apply(t -> Str(t), F[k]), " ")));
    filewrite(fh, Str("facecorners ", k, " ", strjoin(apply(t -> fmt(t), facecorners(X, F[k])), " "))));
  for(k = 1, #rfaces, filewrite(fh, Str("rattlerface ", rfaces[k][1], " ", rfaces[k][2])));
  filewrite(fh, "end");
  [R, F, C];
}
\\ polygon record; pts = list of [point, distances to the vertices]
writepolygon(fh, name, family, V, d, pts) = {
  my(m = #V, u = polycorners(V));
  filewrite(fh, Str("begin polygon ", name));
  filewrite(fh, Str("family ", family));
  filewrite(fh, Str("d ", fmt(d)));
  filewrite(fh, Str("m ", m));
  for(k = 1, m, filewrite(fh, Str("vertex ", k - 1, " ", fmtv(V[k]))));
  filewrite(fh, Str("corners ", strjoin(apply(t -> fmt(t), u), " ")));
  for(i = 1, m, for(j = i + 1, m,
    if(j - i == 1 || (i == 1 && j == m), next);
    filewrite(fh, Str("diag ", i - 1, " ", j - 1, " ", fmt(sdist(V[i], V[j]))))));
  for(k = 1, #pts,
    filewrite(fh, Str("point ", k, " ", fmtv(pts[k]), " ", strjoin(apply(t -> fmt(sdist(pts[k], t)), V), " "))));
  filewrite(fh, "end");
}

\\ ---------- input ----------
\\ read a library file into a list of records; each record is a Map from keyword to the list of
\\ its lines (each line a vector of strings without the keyword); numbers are parsed with eval.
readlib(path) = {
  my(fh = fileopen(path, "r"), L = List(), cur = 0, s, t, key);
  while(1,
    s = filereadstr(fh);
    if(s === 0, break);
    if(#s == 0 || Vecsmall(s)[1] == 35, next);
    t = select(z -> #z, strsplit(s, " "));
    key = t[1];
    if(key == "begin", cur = Map(); mapput(cur, "kind", [[t[2]]]); mapput(cur, "name", [[t[3]]]); next);
    if(key == "end", listput(L, cur); cur = 0; next);
    if(cur === 0, error("readlib: line outside a record: ", s));
    if(mapisdefined(cur, key), mapput(cur, key, concat(mapget(cur, key), [t[2..#t]])), mapput(cur, key, [t[2..#t]])));
  fileclose(fh);
  Vec(L);
}
recget(r, key) = if(mapisdefined(r, key), mapget(r, key), []);
recname(r) = mapget(r, "name")[1][1];
recnum(r, key) = eval(mapget(r, key)[1][1]);
\\ configuration record -> [X, d, E, rattlers, R, F, FC] with F faces, FC their corners
cfgparse(r) = {
  my(n = recnum(r, "n"), X = vector(n), E, rt, R = vector(n, i, []), F, FC, t);
  foreach(recget(r, "point"), t, X[eval(t[1])] = [eval(t[2]), eval(t[3]), eval(t[4])]);
  E = apply(t -> [eval(t[1]), eval(t[2])], recget(r, "edge"));
  rt = apply(t -> eval(t[1]), recget(r, "rattler"));
  foreach(recget(r, "rot"), t, R[eval(t[1])] = apply(t -> eval(t), t[3..#t]));
  F = apply(t -> apply(t -> eval(t), t[3..#t]), recget(r, "face"));
  FC = apply(t -> apply(t -> eval(t), t[2..#t]), recget(r, "facecorners"));
  [X, recnum(r, "d"), E, rt, R, F, FC];
}
\\ polygon record -> [V, d, corners, points]
polyparse(r) = {
  my(m = recnum(r, "m"), V = vector(m), u, P, t);
  foreach(recget(r, "vertex"), t, V[eval(t[1]) + 1] = [eval(t[2]), eval(t[3]), eval(t[4])]);
  u = apply(t -> eval(t), recget(r, "corners")[1]);
  P = apply(t -> [eval(t[2]), eval(t[3]), eval(t[4])], recget(r, "point"));
  [V, recnum(r, "d"), u, P];
}
