\\ The rooted-map check of plantri's unrestricted list: reads the outputs of plantri_ms -p -G -u n r/m
\\ (files in $MS_FILES, one per part), checks that the parts are 0..m-1 of one modulus and that each
\\ part's cells add up to its totals and to plantri's own count, then for each face count F sums
\\ 4E/nbtot exactly (E = n + F - 2) and compares with T(F-1, n-1). Expected totals in $MS_GRAPHS
\\ (A000944) and $MS_CLASS (the recorded class count). Everything runs in main(), so an error stops
\\ the whole check before its verdict and its END line. Run: see check.sh.
read("formula.gp");
main() =
{
  my(n = eval(getenv("MS_N")), files = strsplit(getenv("MS_FILES"), " "));
  my(cnt = Map(), cls = Map(), parts = [], M = 0, G = 0, C = 0, ok = 1);
  my(K, nonint = 0, neq = 0, ncell = 0, SG, ST, eg, ec);
  for (f = 1, #files,
    my(L = readstr(files[f]), tot = 0, pg = -1, sg = 0, sc = 0, r, m);
    for (i = 1, #L, my(v = strsplit(L[i], " "));
      if (#v == 6 && v[1] == "cell",
        my(nn = eval(v[2]), F = eval(v[3]), a = eval(v[4]), g = eval(v[5]), c = eval(v[6]), key = [F, a]);
        if (nn != n, error("n = ", nn, " in ", files[f]));
        mapput(cnt, key, if (mapisdefined(cnt, key), mapget(cnt, key), 0) + g);
        mapput(cls, key, if (mapisdefined(cls, key), mapget(cls, key), 0) + c);
        sg += g; sc += c);
      if (#v == 6 && v[1] == "total",
        if (tot, error("two total lines in ", files[f]));
        tot = 1; r = eval(v[3]); m = eval(v[4]);
        if (eval(v[2]) != n || eval(v[5]) != sg || eval(v[6]) != sc, error("part totals in ", files[f])));
      if (#v >= 3 && v[2] == "polytopes" && v[3] == "generated;", pg = eval(v[1])));
    if (!tot || pg != sg, error("missing total, or plantri count ", pg, " != ", sg, " in ", files[f]));
    if (M && m != M, error("two moduli"));
    M = m; parts = concat(parts, r); G += sg; C += sc;
    printf("part %d/%d: graphs %d, class %d, plantri count %d\n", r, m, sg, sc, pg));
  if (vecsort(parts) != [0 .. M - 1], error("parts ", vecsort(parts), " are not 0..", M - 1));
  printf("n = %d, %d parts of modulus %d: graphs %d, class %d\n", n, #parts, M, G, C);
  printf("\n%3s %3s %3s %20s %20s %6s %12s %12s\n", "n", "F", "E", "sum 4E/|Aut|", "T(F-1,n-1)", "equal", "graphs", "class");
  K = Mat(cnt)[, 1];
  for (F = 4, 2*n - 4,
    my(E = n + F - 2, S = 0, g = 0, c = 0, t = T(F - 1, n - 1));
    for (i = 1, #K, if (K[i][1] == F, my(a = K[i][2], x = mapget(cnt, K[i]));
      if ((4*E) % a, nonint++);
      S += x * 4*E / a; g += x; c += mapget(cls, K[i])));
    if (S == 0 && t == 0, next);
    ncell++; if (S == t, neq++, ok = 0);
    printf("%3d %3d %3d %20d %20d %6s %12d %12d\n", n, F, E, S, t, if (S == t, "yes", "NO"), g, c));
  if (#select(k -> k[1] < 4 || k[1] > 2*n - 4, K), ok = 0; print("cells with F outside 4..2n-4"));
  if (nonint, ok = 0; printf("%d keys with nbtot not dividing 4E\n", nonint));
  SG = sum(i = 1, #K, mapget(cnt, K[i]) * 4*(n + K[i][1] - 2) / K[i][2]);
  ST = sum(F = 4, 2*n - 4, T(F - 1, n - 1));
  printf("\ncells equal: %d of %d; total rooted maps %d, formula %d\n", neq, ncell, SG, ST);
  eg = getenv("MS_GRAPHS"); ec = getenv("MS_CLASS");
  if (type(eg) == "t_STR" && eg != "",
    printf("graphs %d, A000944(%d) = %s: %s\n", G, n, eg, if (G == eval(eg), "equal", "DIFFER")); if (G != eval(eg), ok = 0));
  if (type(ec) == "t_STR" && ec != "",
    printf("class %d, recorded %s: %s\n", C, ec, if (C == eval(ec), "equal", "DIFFER")); if (C != eval(ec), ok = 0));
  print(if (ok, "CHECK PASS", "CHECK FAIL"), " n = ", n);
  print("END");
}
main();
quit
