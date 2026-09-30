\\ The contact graphs of C1 and C3 (Corollary 1.2 and the remark after it): degrees, the vertices of
\\ degree 5 with their names in Table 1 and the edges among them, the face sizes of the embedding on the
\\ sphere, and 3-connectivity. Contacts and point labels from ../../data/bk15_exact.txt (the exact lists
\\ of Computation 2.2), coordinates from ../../data/bk15_c1.txt and bk15_c3.txt.
\\ Run: gp -q contact_graphs.gp < /dev/null
default(realprecision, 40);
names = ["p_V", "rho p_V", "rho^2 p_V", "p_W", "rho p_W", "rho^2 p_W", "p_T", "rho p_T", "rho^2 p_T", \
  "tau p_T", "rho tau p_T", "rho^2 tau p_T", "tau p_W", "rho^2 tau p_W", "rho tau p_W", "tau p_V", \
  "rho^2 tau p_V", "rho tau p_V"];
lines = readstr("../../data/bk15_exact.txt");
field(key) = {
  for (i = 1, #lines, my(s = lines[i], k = #key);
    if (#s > k && strchr(Vecsmall(s)[1..k]) == key,
      my(t = Vec(strchr(Vecsmall(s)[k+2..#s]))); t = apply(c -> if (c == "(", "[", c == ")", "]", c), t);
      return(eval(concat(t)))));
  error("missing ", key);
}
coords(file) = apply(l -> eval(concat(["[", strjoin(strsplit(l, " "), ","), "]"])), readstr(file));
cross(a, b) = [a[2]*b[3]-a[3]*b[2], a[3]*b[1]-a[1]*b[3], a[1]*b[2]-a[2]*b[1]];
check(tag, file) = {
  my(keep = field(concat(tag, " keep")), E = field(concat(tag, " contacts")), X = coords(file), n = #X,
     nb = vector(n, i, List()), deg, d5, rot, seen, sizes = [], conn3 = 1);
  for (k = 1, #E, my(i = E[k][1] + 1, j = E[k][2] + 1); listput(nb[i], j); listput(nb[j], i));
  deg = vector(n, i, #nb[i]);
  \\ the coordinates match the contact list: contacts at inner product u, all other pairs below
  my(u = polrootsreal(13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1)[1], ce = 0, other = -1);
  for (i = 1, n, for (j = i + 1, n, my(t = X[i]*X[j]~);
    if (setsearch(Set(Vec(nb[i])), j), ce = max(ce, abs(t - u)), other = max(other, t))));
  \\ the bound is rounded up to 6 decimals (an exact decimal, printed exactly)
  printf("%s: coordinates of %s: |<x_i,x_j> - u| < 1e-20 on the contacts: %d, other inner products <= %.6f\n", tag, file, ce < 1e-20, ceil(other * 10^6) / 10^6);
  printf("%s: %d points, %d contacts, degrees %s\n", tag, n, #E, vecsort(deg));
  d5 = [i | i <- [1..n], deg[i] == 5];
  printf("  degree 5: %s\n", strjoin(apply(i -> names[keep[i]], d5), ", "));
  printf("  edges among them: %s\n", strjoin([concat(["{", names[keep[a]], ", ", names[keep[b]], "}"]) \
    | a <- d5; b <- d5, a < b && setsearch(Set(Vec(nb[a])), b)], "; "));
  \\ rotation system: neighbours of each point in angular order around it
  rot = vector(n, i, my(p = X[i], e1 = cross(p, if (abs(p[1]) < 0.9, [1,0,0], [0,1,0])), e2);
    e1 = e1 / sqrt(e1*e1~); e2 = cross(p, e1);
    my(L = Vec(nb[i])); vecsort(L, (a, b) -> sign(arg((X[a]*e1~) + I*(X[a]*e2~)) - arg((X[b]*e1~) + I*(X[b]*e2~)))));
  seen = Map();
  for (v0 = 1, n, for (j0 = 1, #rot[v0],
    if (mapisdefined(seen, [v0, rot[v0][j0]]), next);
    my(v = v0, w = rot[v0][j0], len = 0);
    while (!mapisdefined(seen, [v, w]),
      mapput(seen, [v, w], 1); len++;
      my(r = rot[w], k = select(x -> x == v, r, 1)[1]);
      [v, w] = [w, r[k % #r + 1]]);
    sizes = concat(sizes, len)));
  printf("  faces: %d, sizes %s, Euler n - e + f = %d\n", #sizes, vecsort(sizes), n - #E + #sizes);
  \\ 3-connectivity: removing any two points leaves a connected graph
  for (a = 1, n, for (b = a + 1, n,
    my(alive = vector(n, i, i != a && i != b), s = if (a > 1, 1, if (b > 2, 2, 3)), reach = Set([s]), todo = [s]);
    while (#todo, my(v = todo[#todo]); todo = todo[1..#todo-1];
      foreach(Vec(nb[v]), w, if (alive[w] && !setsearch(reach, w), reach = setunion(reach, [w]); todo = concat(todo, w))));
    if (#reach != n - 2, conn3 = 0)));
  printf("  3-connected: %d\n", conn3);
}
check("C1", "../../data/bk15_c1.txt");
check("C3", "../../data/bk15_c3.txt");
quit;
