\\ Figure 1 of the paper: the contact graphs of C1 and C3, drawn by stereographic projection from the
\\ centre of a pentagon (the normalized sum of its vertices), as TikZ code. Coordinates from
\\ ../../data/bk15_c1.txt and bk15_c3.txt, contacts and kept frame points from ../../data/bk15_exact.txt.
\\ Each arc is sampled at 16 points, and the plane is then compressed radially by r -> 3r/(3 + r),
\\ which keeps the drawing a plane drawing. Filled black: the three vertices of degree 5; grey squares:
\\ the three toggle points that the configuration keeps (rows 7 to 12 of Table 1).
\\ Run from code/paper: gp -q figure1.gp < /dev/null > figure1.out
default(realprecision, 40);
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
unit(v) = v / sqrt(v*v~);
fmt(t) = Strprintf("%.3f", t);
draw(tag, file) = {
  my(keep = field(concat(tag, " keep")), E = field(concat(tag, " contacts")), X = coords(file), n = #X,
     nb = vector(n, i, List()), rot, seen, best = [], c, e1, e2, e3, P, S = 2);
  for (k = 1, #E, my(i = E[k][1] + 1, j = E[k][2] + 1); listput(nb[i], j); listput(nb[j], i));
  \\ rotation system and faces, as in ../gp/contact_graphs.gp
  rot = vector(n, i, my(p = X[i], f1 = unit(cross(p, if (abs(p[1]) < 0.9, [1,0,0], [0,1,0]))), f2 = cross(p, f1));
    my(L = Vec(nb[i])); vecsort(L, (a, b) -> sign(arg((X[a]*f1~) + I*(X[a]*f2~)) - arg((X[b]*f1~) + I*(X[b]*f2~)))));
  seen = Map();
  for (v0 = 1, n, for (j0 = 1, #rot[v0],
    if (mapisdefined(seen, [v0, rot[v0][j0]]), next);
    my(v = v0, w = rot[v0][j0], face = List());
    while (!mapisdefined(seen, [v, w]),
      mapput(seen, [v, w], 1); listput(face, v);
      my(r = rot[w], k = select(x -> x == v, r, 1)[1]);
      [v, w] = [w, r[k % #r + 1]]);
    if (#face == 5 && best == [], best = Vec(face))));
  c = unit(sum(i = 1, #best, X[best[i]]));
  e3 = -c; e1 = unit(cross(e3, if (abs(e3[1]) < 0.9, [1,0,0], [0,1,0]))); e2 = cross(e3, e1);
  P = (p -> my(q = [p*e1~, p*e2~] / (1 + p*e3~), r = sqrt(q*q~)); q * 3 / (3 + r));
  printf("%% %s: stereographic projection from the centre of the pentagon on frame rows %s\n", tag,
    strjoin(apply(i -> Str(keep[i]), best), ", "));
  printf("\\begin{tikzpicture}[scale=%s]\n", fmt(S));
  for (k = 1, #E, my(a = X[E[k][1] + 1], b = X[E[k][2] + 1], th = acos(a*b~), pts = "");
    for (s = 0, 16, my(t = th * s / 16, q = P((sin(th - t) * a + sin(t) * b) / sin(th)));
      pts = concat(pts, Str("(", fmt(q[1]), ",", fmt(q[2]), ")")));
    printf("\\draw[thin] plot coordinates {%s};\n", pts));
  for (i = 1, n, my(q = P(X[i]), deg = #nb[i], row = keep[i]);
    if (deg == 5, printf("\\fill (%s,%s) circle (0.045);\n", fmt(q[1]), fmt(q[2])),
      row >= 7 && row <= 12, printf("\\filldraw[fill=black!35] (%s,%s) +(-0.04,-0.04) rectangle +(0.04,0.04);\n", fmt(q[1]), fmt(q[2])),
      printf("\\filldraw[fill=white] (%s,%s) circle (0.033);\n", fmt(q[1]), fmt(q[2]))));
  printf("\\end{tikzpicture}\n");
}
draw("C1", "../../data/bk15_c1.txt");
draw("C3", "../../data/bk15_c3.txt");
quit;
