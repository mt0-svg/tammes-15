\\ The d range of the D3 program encloses the range [dlo, dhi] of the Lean reduction.
\\
\\ Lean (Tammes15/Trigrows/Margins.lean): dlo = 5365785/100000 * (pi/180),
\\ dhi = 566716/10000 * (pi/180).
\\ Program: the decimals `dlo`, `dhi` of data/params15ft.txt, read by `read_drange`
\\ of code/impl1/rust/src/deep.rs through `parse_dn`, `parse_up` of code/impl1/rust/src/iv.rs:
\\ `s.parse::<f64>()` (the binary64 nearest to the decimal, ties to even), then one ulp outward
\\ (`next_down` for dlo, `next_up` for dhi).
\\
\\ Checked, with margins printed in radians:
\\   (1) decimal dlo <= Lean dlo and decimal dhi >= Lean dhi;
\\   (2) the parsed binary64 bounds of the program enclose Lean's range, in two models of the parse:
\\       (a) the program's own (nearest binary64, then one ulp outward), and
\\       (b) the directed roundings (largest binary64 <= decimal dlo, smallest >= decimal dhi),
\\       which are the tightest outward parse and so the weaker case.
\\ The decimals and the binary64 values are exact rationals; only pi is approximated, at 100
\\ digits, so every margin is certified when it exceeds 1e-90 (checked).

default(realprecision, 100);

DDLO = 93650615204123937289 / 10^20;   \\ params15ft.txt, line "dlo"
DDHI = 98910601237321848052 / 10^20;   \\ params15ft.txt, line "dhi"
LDLO = 5365785 / 100000 * (Pi / 180);
LDHI = 566716 / 10000 * (Pi / 180);

\\ The binade exponent of a positive rational x: 2^e <= x < 2^(e+1).
bexp(x) = my(e = logint(floor(x * 2^1100), 2) - 1100); while (2^(e + 1) <= x, e++); while (2^e > x, e--); e;
\\ The ulp of the normal binary64 numbers of the binade of x.
ulp(x) = 2^(bexp(x) - 52);

\\ Nearest binary64, ties to even (asserts that no tie occurs, so the tie rule is not used).
nearest(x) = {
  my(u = ulp(x), m = x / u, r = floor(m));
  if (m - r == 1/2, error("tie"));
  if (m - r > 1/2, r++);
  r * u;
}
\\ Next binary64 below and above a positive binary64 f (the ulp below a power of two is half).
nextdown(f) = my(u = ulp(f)); if (f == 2^bexp(f), f - u / 2, f - u);
nextup(f) = f + ulp(f);
\\ Directed roundings to binary64.
floor64(x) = my(u = ulp(x)); floor(x / u) * u;
ceil64(x) = my(u = ulp(x)); ceil(x / u) * u;

ok = 1;
chk(name, m) = {
  printf("%-58s %.6e rad%s\n", name, m, if (m > 1e-90, "", "   FAIL"));
  if (m <= 1e-90, ok = 0);
}

print("Lean dlo = ", LDLO);
print("Lean dhi = ", LDHI);
print("params15ft.txt: dlo ", DDLO * 1.0, ", dhi ", DDHI * 1.0);
print();
print("(1) decimals of params15ft.txt against Lean");
chk("Lean dlo - decimal dlo", LDLO - DDLO);
chk("decimal dhi - Lean dhi", DDHI - LDHI);
print();

nlo = nearest(DDLO); nhi = nearest(DDHI);
plo = nextdown(nlo); phi = nextup(nhi);
print("(2a) program parse: nearest binary64, then one ulp outward");
printf("  ulp at dlo, dhi: 2^%d, 2^%d\n", bexp(DDLO) - 52, bexp(DDHI) - 52);
printf("  nearest(dlo) - decimal dlo = %.6e, nearest(dhi) - decimal dhi = %.6e\n", nlo - DDLO, nhi - DDHI);
printf("  parse_dn(dlo) = %d * 2^%d\n", plo / ulp(plo), bexp(plo) - 52);
printf("  parse_up(dhi) = %d * 2^%d\n", phi / ulp(phi), bexp(phi) - 52);
chk("Lean dlo - parse_dn(dlo)", LDLO - plo);
chk("parse_up(dhi) - Lean dhi", phi - LDHI);
print();

flo = floor64(DDLO); chi = ceil64(DDHI);
print("(2b) directed roundings: largest binary64 <= dlo, smallest binary64 >= dhi");
chk("Lean dlo - floor64(dlo)", LDLO - flo);
chk("ceil64(dhi) - Lean dhi", chi - LDHI);
print();

if (ok, print("END OK"), print("END FAIL"));
quit;
