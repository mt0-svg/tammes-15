\\ Known-answer tests of formula.gp, and negative controls. Run: sh kat.sh
read("formula.gp");
ok = 1;
chk(name, got, want) = my(e = (got == want)); if (!e, ok = 0); printf("%-58s %s\n", name, if (e, "ok", Str("FAIL got ", got, " want ", want)));
printf("parisizemax %d, nbthreads %d\n", default(parisizemax), default(nbthreads));
\\ 1. By hand: the sum of 4E/|Aut| over the polyhedra of the cell.
chk("T(3,3) = 1: tetrahedron, 24/24", T(3,3), 1);
chk("T(4,4) = 4: square pyramid, 32/8", T(4,4), 4);
chk("T(4,5) = 3: triangular prism (5 faces, 6 vertices), 36/12", T(4,5), 3);
chk("T(5,4) = 3: triangular bipyramid (6 faces, 5 vertices), 36/12", T(5,4), 3);
\\ 8 faces, 6 vertices: the octahedron, 48/48, and the triangulation made by putting a vertex w in the face
\\ axy of the bipyramid with apexes a, b and equator x, y, z; its group is {1, (xy), (az)(bw), (xy)(az)(bw)}
\\ (degrees 5: x, y; 4: a, z; 3: b, w), so 48/4. By duality the cube and its partner give the same.
chk("T(7,5) = 13: octahedron 48/48 + one triangulation 48/4", T(7,5), 13);
chk("T(5,7) = 13: the duals (cube, cubic graph with group of order 4)", T(5,7), 13);
\\ 2. The b-file of A290326 (G. Coserea), rows 1 to 30, flattened: row n has max(n, 2n-3) terms. The formula
\\ is stated for n, k >= 3; the entries with n <= 2 or k <= 2 are listed apart.
b = readstr("ref/b290326_rows1-30.txt");
pos = 0; nbad = 0; nent = 0; nout = 0; badout = [];
for (n = 1, 30, for (k = 1, max(n, 2*n - 3), pos++; my(v = strsplit(b[pos], " ")); \
  if (eval(v[1]) != pos, error("b-file index ", pos)); \
  if (n >= 3 && k >= 3, nent++; if (T(n,k) != eval(v[2]), nbad++), nout++; if (T(n,k) != eval(v[2]), badout = concat(badout, [[n, k]])))));
chk(Str("b-file rows 1..30, n, k >= 3: ", nent, " entries, mismatches"), [nent, nbad, pos == #b], [784, 0, 1]);
printf("b-file entries outside n, k >= 3: %d, of which the formula differs at %d, all with k = 1: %d\n", nout, #badout, #badout == #select(x -> x[2] == 1, badout));
\\ 3. Duality T(n,k) = T(k,n), and T(n,k) = 0 for k > 2n - 3 (n >= 3), for n, k <= 40.
nsym = 0; nzero = 0;
for (n = 3, 40, for (k = 3, 40, if (T(n,k) != T(k,n), nsym++); if (k > 2*n - 3 && T(n,k) != 0, nzero++)));
chk("duality and vanishing for 3 <= n, k <= 40: violations", [nsym, nzero], [0, 0]);
\\ 4. Row sums against A106651 (c-nets on V vertices, a(V), offset 3): V = 4..15.
a106651 = [1, 7, 73, 879, 11713, 167423, 2519937, 39458047, 637446145, 10561615871, 178683815937, 3076487458815];
chk("sum over F of T(F-1, V-1) = A106651(V), V = 4..15", vector(12, i, my(V = i + 3); sum(F = 4, 2*V - 4, T(F-1, V-1))), a106651);
\\ 5. Reference values recorded before this check was written: V = 15, F = 10..26; and the three cells
\\ where the printed 1968 table is wrong (A290326, comment of S. A. Irvine).
r15 = [121095, 7580040, 155282400, 1614234960, 10224817515, 43494961404, 131631305718, 293695935764, 493664301900, \
  632245743360, 618627319508, 459709747416, 255271793013, 102695772540, 28295250870, 4779753924, 373537388];
chk("V = 15, F = 10..26: the 17 reference cells", vector(17, i, T(i + 8, 14)), r15);
chk("T(14,14), T(15,13), T(15,14) by the formula", [T(14,14), T(15,13), T(15,14)], [43494961404, 21697730835, 131631305718]);
\\ Negative controls: the printed 1968 values must differ, a shifted index must differ.
nc1 = [T(14,14), T(15,13), T(15,14)] != [43494961412, 21697730849, 131631305614];
nc2 = vector(17, i, T(i + 8, 15)) != r15;
nc3 = vector(17, i, T(i + 9, 14)) != r15;
chk("negative controls (1968 table, V shifted, F shifted) differ", [nc1, nc2, nc3], [1, 1, 1]);
print(if (ok, "KAT PASS", "KAT FAIL"));
print("END");
quit
