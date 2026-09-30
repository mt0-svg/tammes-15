\\ Proposition 2.1 in a PARI number field tower (frame_field.gp), and the data files checked against it: the targets of Local (data/tie_targets.txt, Section 5.4), the coordinates data/bk15_c1.txt, bk15_c3.txt and the entry of Sloane's table.
\\ run: gp -q --default parisizemax=2000000000 --default nbthreads=1 tie_targets_check.gp > tie_targets_check.out
read("frame_field.gp");
read("tie_targets.gp");
base = [1,2,3,4,5,6,13,14,15,16,17,18]; pairs = [[7,12],[8,10],[9,11]];
confs = vector(8); cnames = vector(8); k0 = 0;
{ forvec(ch = [[0,1],[0,1],[0,1]], k0++; confs[k0] = vecsort(concat(base, vector(3, m, pairs[m][ch[m]+1]))); cnames[k0] = Str("frame", ch[1], ch[2], ch[3])); }
num(keep) = vector(15, i, vector(3, m, encl(F[keep[i]][m])[1] * 1.)~);
\\ 1. tie_targets.txt against the rigorous enclosures, and its contact lists against exact contacts
{ for(k = 1, 8, my(keep = confs[k], worst = -1, cont = [], okc);
  for(i = 1, 15, for(m = 1, 3, my(e = encl(F[keep[i]][m]), mid = TT_pts[k][i][2*m-1], rad = TT_pts[k][i][2*m]);
    worst = max(worst, abs(mid - e[1]) + e[2] - rad)));
  for(i = 1, 15, for(j = i+1, 15, if(ipE(F[keep[i]], F[keep[j]]) == uE, cont = concat(cont, [[i-1, j-1]]))));
  okc = (cont == TT_cont[k]);
  printf("tie_targets conf %d (%s = %s, labelled %s): max(|mid - exact| + our radius - file radius) = %.3e (<= 0 means the file balls contain the exact values); contact list identical: %d\n", k, TT_name[k], cnames[k], TT_type[k], worst, okc)); }
\\ 2. congruences: X ~ Y iff O x_i = y_pi(i) for an orthogonal O and a permutation pi
congr(X, Y, tol) = { my(B = matconcat([X[1], X[2], X[3]]), Bi = B^-1, G = matrix(15, 15, i, j, X[i]~ * X[j]), H = matrix(15, 15, i, j, Y[i]~ * Y[j]), found = []);
  for(a = 1, 15, for(b = 1, 15, if(b != a && abs(H[a,b] - G[1,2]) < tol, for(c = 1, 15, if(c != a && c != b && abs(H[a,c] - G[1,3]) < tol && abs(H[b,c] - G[2,3]) < tol,
    my(Om = matconcat([Y[a], Y[b], Y[c]]) * Bi, pm = vector(15), ok = 1);
    if(normlp(Vec(Om~ * Om - matid(3))) > tol, next);
    for(i = 1, 15, my(z = Om * X[i], jj = 0); for(j = 1, 15, if(normlp(Vec(z - Y[j])) < tol, jj = j)); if(jj == 0, ok = 0; break); pm[i] = jj);
    if(ok && #Set(pm) == 15, found = concat(found, [[sign(matdet(Om)), pm]])))))));
  found; }
X3 = num(confs[1]); X1 = num(confs[2]);
{ for(k = 1, 8, my(Xk = num(confs[k]), f3 = congr(Xk, X3, 1e-40), f1 = congr(Xk, X1, 1e-40));
  printf("%s: isometries onto C3: %d (dets %s); onto C1: %d (dets %s)\n", cnames[k], #f3, Set(vector(#f3, q, f3[q][1])), #f1, Set(vector(#f1, q, f1[q][1])))); }
\\ 3. Sloane's table (data/pack.3.15.txt, double precision) against C1 and C3
sv = readvec("../../data/pack.3.15.txt");
S15 = vector(15, i, [sv[3*i-2], sv[3*i-1], sv[3*i]]~);
S15 = vector(15, i, S15[i] / sqrt(S15[i]~ * S15[i]));
f1s = congr(X1, S15, 1e-6); f3s = congr(X3, S15, 1e-6);
printf("Sloane 15-point packing: isometries from C1 within 1e-6: %d (dets %s); from C3: %d\n", #f1s, Set(vector(#f1s, q, f1s[q][1])), #f3s);
if(#f1s, pp = f1s[1][2]; Om = matconcat([S15[pp[1]], S15[pp[2]], S15[pp[3]]]) * matconcat([X1[1], X1[2], X1[3]])^-1; printf("   max |O x_i - s_pi(i)| with O from the first triple: %.3e\n", vecmax(vector(15, i, normlp(Vec(Om * X1[i] - S15[pp[i]]))))));
\\ 4. data/bk15_c1.txt, data/bk15_c3.txt (25 digits) against the exact points
rdpts(fn) = { my(ls = readstr(fn)); vector(#ls, i, my(w = select(s -> #s > 0, strsplit(ls[i], " "))); vector(3, m, eval(w[m]))); }
c1v = rdpts("../../data/bk15_c1.txt"); c3v = rdpts("../../data/bk15_c3.txt");
printf("bk15_c1.txt (%d points) vs frame001: max coordinate error %.3e; bk15_c3.txt (%d points) vs frame000: %.3e\n", #c1v, vecmax(vector(15, i, vecmax(vector(3, m, abs(c1v[i][m] - X1[i][m]))))), #c3v, vecmax(vector(15, i, vecmax(vector(3, m, abs(c3v[i][m] - X3[i][m]))))));
\\ 5. exact congruence: the Gram matrices agree exactly in the field under the permutation found above
\\ (equal Gram matrices of two spanning 15-tuples give an orthogonal map; its determinant sign is read numerically)
{ for(k = 1, 8, my(Xk = num(confs[k]), ref = if(#congr(Xk, X3, 1e-40), 1, 2), f = congr(Xk, if(ref == 1, X3, X1), 1e-40)[1], pm = f[2], ok = 1);
  for(i = 1, 15, for(j = i+1, 15, if(ipE(F[confs[k][i]], F[confs[k][j]]) != ipE(F[confs[ref][pm[i]]], F[confs[ref][pm[j]]]), ok = 0)));
  printf("%s -> %s: exact Gram equality under the permutation: %d, det sign %d\n", cnames[k], if(ref == 1, "C3", "C1"), ok, f[1])); }
\\ 6. Proposition 2.1 in this tower: the 30 contacts of each configuration are identities in the field, and every
\\ other pair has inner product below u by a rigorous margin (upper end of the rational enclosure of <p_i,p_j> - u)
{ for(k = 1, 8, my(keep = confs[k], nc = 0, oth = -1);
  for(i = 1, 15, for(j = i+1, 15, my(g = ipE(F[keep[i]], F[keep[j]]));
    if(g == uE, nc++, my(e = encl(g - uE)); if(e[1] + e[2] >= 0, error("non-contact not separated")); oth = max(oth, e[1] + e[2]))));
  printf("%s: exact contacts %d, max over the other pairs of <p_i,p_j> - u <= %.10f\n", cnames[k], nc, oth)); }
