\\ tie_map.gp: for each of the 8 target configurations of data/tie_targets.txt, the frame index (0..17, the order
\\ of Attained.ptN) of each of its 15 points, an element g of the group D (rho(x,y,z) = (z,x,y),
\\ tau(x,y,z) = (-z,-y,-x)) and a frame X in {C1, C3} with sigma such that point i of the configuration is
\\ g(X point sigma(i)) and the listed contacts go by sigma onto the contacts of X; and, for each of the 9 coordinate
\\ values a..t of Attained.Data, the midpoints of the data that stand for it and their largest distance to the exact
\\ value. Then it writes the Lean file TieMap.lean.
\\ Run from the repository root: TIEMAP_OUT=FILE gp -q code/lean-data/tie_map.gp < /dev/null. It appends to FILE,
\\ which should not exist; without TIEMAP_OUT, to Tammes15/PaperSteps/TieMap.lean, so remove that file first.
\\ TIEMAP_IN, if set, replaces the path of the targets, data/tie_targets.txt. code/lean-data/regen.sh compares the
\\ file written with the Lean file.
default(realprecision, 150);
u = select(t -> t > 0.5 && t < 0.7, polrootsreal(13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1))[1];
Qy = 9*(4*u^2-u-1)*(3*u+1)^2*y^2 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*y + u^2*(4*u^2-u-1)*(5*u-1)^2;
be = select(t -> abs(t - 0.0294089) < 1e-4, polrootsreal(Qy))[1];
b = sqrt(be);
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u));
a = (u - b*c)/(b + c);
q1 = ((2*a-b+2*c)*u-b)/(u+1);
q2 = ((2*a+2*b-c)*u-c)/(u+1);
q3 = ((-a+2*b+2*c)*u-a)/(u+1);
r1 = ((6*a+3*b-2*c)*u^2+2*(a-b-c)*u-b)/(u+1)^2;
r2 = ((3*c-2*a+6*b)*u^2+2*(b-c-a)*u-c)/(u+1)^2;
r3 = ((3*a-2*b+6*c)*u^2+2*(c-a-b)*u-a)/(u+1)^2;
V = [a, b, c, q1, q2, q3, r1, r2, r3];
\\ rows of Attained.ptN as signed 1-based symbol indices into V (aN bN cN dN eN fN rN sN tN)
T = [[1,2,3],[3,1,2],[2,3,1],[4,5,6],[6,4,5],[5,6,4],[7,8,9],[9,7,8],[8,9,7],[-9,-8,-7],[-7,-9,-8],[-8,-7,-9],[-6,-5,-4],[-5,-4,-6],[-4,-6,-5],[-3,-2,-1],[-2,-1,-3],[-1,-3,-2]];
P = vector(18, k, vector(3, l, sign(T[k][l]) * V[abs(T[k][l])]));
rho(w) = [w[3], w[1], w[2]];
tau(w) = [-w[3], -w[2], -w[1]];
idx(w) = { my(best = 0, bd = 1); for (k = 1, 18, my(dd = normlp(P[k] - w)); if (dd < bd, bd = dd; best = k)); if (bd > 1e-30, error("no frame point")); best - 1 };
Dw = ["1", "r", "rr", "t", "rt", "rrt"];
Dact(wd, w) = { my(z = w, s = Vec(wd)); if (wd == "1", return(z)); forstep (i = #s, 1, -1, z = if (s[i] == "r", rho(z), tau(z))); z };
keeps = [[0,1,2,3,4,5,6,7,10,12,13,14,15,16,17], [0,1,2,3,4,5,6,7,8,12,13,14,15,16,17]];
xname = ["C1", "C3"];
SS = [[[0,1],[0,2],[0,3],[0,5],[0,6],[1,2],[1,3],[1,4],[1,7],[2,4],[2,5],[3,7],[3,9],[4,8],[4,11],[5,6],[5,10],[6,9],[7,11],[8,10],[8,14],[9,12],[9,13],[10,13],[10,14],[11,12],[11,14],[12,13],[12,14],[13,14]], [[0,1],[0,2],[0,3],[0,5],[0,6],[1,2],[1,3],[1,4],[1,7],[2,4],[2,5],[2,8],[3,7],[3,9],[4,8],[4,11],[5,6],[5,10],[6,9],[7,11],[8,10],[9,12],[9,13],[10,13],[10,14],[11,12],[11,14],[12,13],[12,14],[13,14]]];
words(s) = select(t -> #t > 0, strsplit(s, " "));
L = select(s -> #s > 0 && Vec(s)[1] != "#", readstr(if (getenv("TIEMAP_IN"), getenv("TIEMAP_IN"), "data/tie_targets.txt")));
symMid = vector(9, s, List());
symErr = vector(9);
rhoIdx = vector(18, k, idx(rho(P[k])));
tauIdx = vector(18, k, idx(tau(P[k])));
printf("rhoIdx (k -> index of rho(pt k)) = %s\n", rhoIdx);
printf("tauIdx (k -> index of tau(pt k)) = %s\n", tauIdx);
{
for (cc = 1, 8,
  my(pos = 17 * (cc - 1) + 1, name, raw, num, K, cons, w2, found = 0);
  name = L[pos];
  raw = vector(15, i, my(w = words(L[pos + i])); [w[1], w[3], w[5]]);
  num = vector(15, i, vector(3, l, eval(raw[i][l])));
  w2 = words(L[pos + 16]);
  cons = vector(30, e, [eval(w2[2*e]), eval(w2[2*e+1])]);
  K = vector(15, i, idx(num[i]));
  for (xi = 1, 2,
    for (wi = 1, 6,
      if (found, break(2));
      my(img = vector(15, j, idx(Dact(Dw[wi], P[keeps[xi][j] + 1]))), sg, okc = 1);
      sg = vector(15, i, my(jj = 0); for (t = 1, 15, if (img[t] == K[i], jj = t)); jj);
      if (vecmin(sg) > 0 && #Set(sg) == 15,
        for (e = 1, 30,
          my(p1 = sg[cons[e][1] + 1] - 1, p2 = sg[cons[e][2] + 1] - 1);
          if (!setsearch(Set(SS[xi]), [min(p1, p2), max(p1, p2)]), okc = 0));
        if (okc,
          found = 1;
          printf("conf %d (%s): frame %s, g = %s, sigma = %s, frame indices = %s; the 30 contacts go onto those of %s\n",
            cc - 1, name, xname[xi], Dw[wi], apply(t -> t - 1, sg), K, xname[xi])))));
  if (!found, error(Str("no match for configuration ", cc - 1)));
  for (i = 1, 15, for (l = 1, 3,
    my(sy = T[K[i] + 1][l]);
    listput(symMid[abs(sy)], if (sy > 0, raw[i][l], Str("-(", raw[i][l], ")")));
    symErr[abs(sy)] = max(symErr[abs(sy)], abs(sign(sy) * V[abs(sy)] - num[i][l])))));
}
{
for (s = 1, 9,
  printf("symbol %d (%s): value %.45f; midpoints standing for it: %s; largest distance %.3e\n",
    s, ["aN","bN","cN","dN","eN","fN","rN","sN","tN"][s], V[s], Set(Vec(symMid[s])), symErr[s]));
}
\\ Lean data: Tammes15/PaperSteps/TieMap.lean
{
my(f = if (getenv("TIEMAP_OUT"), getenv("TIEMAP_OUT"), "Tammes15/PaperSteps/TieMap.lean"), vrow, bnd, cf = vector(8), rd = 10^50);
for (cc = 1, 8,
  my(pos = 17 * (cc - 1) + 1, raw, num, K, w2, cons, done = 0);
  raw = vector(15, i, my(w = words(L[pos + i])); [w[1], w[3], w[5]]);
  num = vector(15, i, vector(3, l, eval(raw[i][l])));
  w2 = words(L[pos + 16]);
  cons = vector(30, e, [eval(w2[2*e]), eval(w2[2*e+1])]);
  K = vector(15, i, idx(num[i]));
  for (xi = 1, 2, for (wi = 1, 6, if (done, break(2));
    my(img = vector(15, j, idx(Dact(Dw[wi], P[keeps[xi][j] + 1]))), sg, okc = 1);
    sg = vector(15, i, my(jj = 0); for (t = 1, 15, if (img[t] == K[i], jj = t)); jj);
    if (vecmin(sg) > 0 && #Set(sg) == 15,
      for (e = 1, 30, my(p1 = sg[cons[e][1] + 1] - 1, p2 = sg[cons[e][2] + 1] - 1);
        if (!setsearch(Set(SS[xi]), [min(p1, p2), max(p1, p2)]), okc = 0));
      if (okc, done = 1; cf[cc] = [xi, wi, apply(t -> t - 1, sg), K, raw])))));
\\ the data midpoint of each frame point and coordinate (the same in every configuration, checked above)
my(pm = vector(18, k, vector(3)));
for (cc = 1, 8, for (i = 1, 15, for (l = 1, 3, pm[cf[cc][4][i] + 1][l] = cf[cc][5][i][l])));
vrow = (v -> Str("![", v[1], ", ", v[2], ", ", v[3], "]"));
bnd = (t -> floor(t * rd));
write(f, "import Mathlib.Basic.Real.Basic\nimport Mathlib.Data.Fin.VecNotation\n\n/-!\n# The targets of Local against the frame (generated)\n\nWritten by tie_map.gp (PARI/GP) from tie_targets.txt, the file of targets that the program\nreads. For each target configuration `c`: the frame `C3` (`true`) or\n`C1`, the element of `D` by its index in `[1, ρ, ρ², τ, ρτ, ρ²τ]`, and `σ`: point `i` of `c` is the\nimage under that element of point `σ i` of the frame. `ptMid k l` is the midpoint of the data for\ncoordinate `l` of the frame point `k` (the order of `Attained.ptN`). The enclosures `ul2 ≤ uR ≤ uh2`,\n`bl2 ≤ bR ≤ bh2` have widths `1e-60` and `3e-48`.\n-/\n\nnamespace Tammes15.PaperSteps\n");
write(f, "/-- The frame of each target configuration: `true` for `C3`, `false` for `C1`. -/");
write(f, Str("def tieX : Fin 8 → Bool := ![", strjoin(vector(8, cc, if (cf[cc][1] == 2, "true", "false")), ", "), "]\n"));
write(f, "/-- The element of `D` of each target configuration, by its index in `[1, ρ, ρ², τ, ρτ, ρ²τ]`. -/");
write(f, Str("def tieG : Fin 8 → Fin 6 := ![", strjoin(vector(8, cc, Str(cf[cc][2] - 1)), ", "), "]\n"));
write(f, "/-- `σ` of each target configuration. -/");
write(f, Str("def tieSigma : Fin 8 → Fin 15 → Fin 15 := ![\n  ", strjoin(vector(8, cc, Str("![", strjoin(apply(t -> Str(t), cf[cc][3]), ", "), "]")), ",\n  "), "]\n"));
write(f, "/-- The frame index of each point of each target configuration. -/");
write(f, Str("def tieIdx : Fin 8 → Fin 15 → Fin 18 := ![\n  ", strjoin(vector(8, cc, Str("![", strjoin(apply(t -> Str(t), cf[cc][4]), ", "), "]")), ",\n  "), "]\n"));
write(f, "/-- The data midpoint of each coordinate of each frame point. -/");
write(f, Str("def ptMid : Fin 18 → Fin 3 → ℝ := ![\n  ", strjoin(vector(18, k, vrow(pm[k])), ",\n  "), "]\n"));
write(f, "/-- Enclosure of `u`, width `1e-60`. -/");
write(f, Str("def ul2 : ℝ := 0.", floor(u * 10^60), "\n"));
write(f, "/-- Enclosure of `u`, width `1e-60`. -/");
write(f, Str("def uh2 : ℝ := 0.", floor(u * 10^60) + 1, "\n"));
write(f, "/-- Enclosure of `b`, width `3e-48`, with `b` at least `1e-48` inside. -/");
write(f, Str("def bl2 : ℝ := 0.", floor(b * 10^48) - 1, "\n"));
write(f, "/-- Enclosure of `b`, width `3e-48`, with `b` at least `1e-48` inside. -/");
write(f, Str("def bh2 : ℝ := 0.", floor(b * 10^48) + 2, "\n"));
write(f, "end Tammes15.PaperSteps");
printf("wrote %s\n", f);
}
