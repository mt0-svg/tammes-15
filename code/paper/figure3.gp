\\ Figure 3 of the paper: the polygon q_0, ..., q_9 of the lemma on two discs (Appendix A), for
\\ d = 53.65785 degrees, h = h(d), with the circles of radius h about C and C', as TikZ code, in the
\\ stereographic projection from the point opposite the midpoint of C and C'; sides sampled at 12 points.
\\ Frame T = e1, F = e2, C = e3, as in the lemma. Circles sampled at 96 points.
\\ Run from code/paper: gp -q figure3.gp < /dev/null > figure3.out
default(realprecision, 40);
cross(a, b) = [a[2]*b[3]-a[3]*b[2], a[3]*b[1]-a[1]*b[3], a[1]*b[2]-a[2]*b[1]];
unit(v) = v / sqrt(v*v~);
fmt(t) = Strprintf("%.3f", t);
{
  my(d = 53.65785 * Pi / 180, h = acos(cos(d) / cos(d / 2)), g = acos(-tan(h) * tan(d / 2)), s = (Pi - g) / 2,
     T = [1,0,0], F = [0,1,0], C = [0,0,1], C2, T2, F2, M, a, b, P, q, S = 3);
  C2 = cos(d) * C - sin(d) * T; T2 = -(cos(d) * T + sin(d) * C); F2 = -F;
  M = unit(C + C2); a = unit(cross(F, M)); b = cross(M, a);
  P = (x -> [x*a~, x*b~] / (1 + x*M~));
  q = vector(10, j, my(k = (j - 1) % 5, t = (k - 2) * s);
    if (j <= 5, cos(h) * C + sin(h) * (cos(t) * T + sin(t) * F), cos(h) * C2 + sin(h) * (cos(t) * T2 + sin(t) * F2)));
  printf("%% d = 53.65785 degrees, h = %.6f degrees, gamma_t = %.6f degrees, s = %.6f degrees\n",
    h * 180 / Pi, g * 180 / Pi, s * 180 / Pi);
  printf("\\begin{tikzpicture}[scale=%d]\n", S);
  foreach([[C, T, F], [C2, T2, F2]], c,
    my(pts = "");
    for (k = 0, 96, my(t = 2 * Pi * k / 96, p = P(cos(h) * c[1] + sin(h) * (cos(t) * c[2] + sin(t) * c[3])));
      pts = concat(pts, Str("(", fmt(p[1]), ",", fmt(p[2]), ")")));
    printf("\\draw[densely dotted] plot[smooth] coordinates {%s};\n", pts));
  my(pts = "");
  for (j = 1, 10, my(x = q[j], y = q[j % 10 + 1], th = acos(x*y~));
    for (k = 0, 11, my(t = th * k / 12, p = P((sin(th - t) * x + sin(t) * y) / sin(th)));
      pts = concat(pts, Str("(", fmt(p[1]), ",", fmt(p[2]), ") -- "))));
  printf("\\draw %scycle;\n", pts);
  for (j = 1, 10, my(p = P(q[j]));
    printf("\\fill (%s,%s) circle (0.012) node[%s] {$q_{%d}$};\n", fmt(p[1]), fmt(p[2]),
      if (p[2] > 0.001, "above", p[2] < -0.001, "below", if (p[1] > 0, "right", "left")), j - 1));
  my(pc = P(C), pc2 = P(C2));
  printf("\\fill (%s,%s) circle (0.012) node[right] {$C$};\n", fmt(pc[1]), fmt(pc[2]));
  printf("\\fill (%s,%s) circle (0.012) node[left] {$C'$};\n", fmt(pc2[1]), fmt(pc2[2]));
  printf("\\end{tikzpicture}\n");
}
quit;
