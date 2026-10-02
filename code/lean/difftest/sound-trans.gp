\\ High-precision check of the logged transcendental calls against Rnd.Sound (Section 10.4 of the paper,
\\ Tammes15/Contractors/Arith.lean). A numerical check, not a proof: PARI's transcendental functions are
\\ accurate, not certified.
\\
\\ A call of op (4 cos, 5 sin, 6 acos, 7 asin, 8 atan, 9 tan, the codes of dtlog.rs) on the interval
\\ I = [a, b] with result K = [c, d] (binary64 bits; ends read as Lean reads Fl: an extended
\\ rational, or NaN) is an instance of the field of Rnd.Sound for op:
\\   cos, sin, atan: K contains f(x) for every real x in I;
\\   acos, asin:     the same for every real x in I with -1 <= x <= 1;
\\   tan:            the same for every real x in I with -pi/2 < x < pi/2.
\\ I.Mem x is false when an end of I is NaN, so the set D of these x is empty when a or b is NaN,
\\ or a > b, or I misses the domain: the instance then holds vacuously. Otherwise it holds iff c
\\ and d are not NaN, c <= inf_D f and sup_D f <= d (extended reals: an infinite inf or sup asks
\\ for the infinite end). The inf and sup are computed at 320 bits plus the binary exponent of the
\\ ends: f at the ends of D, and +-1 for sin and cos when D contains a maximum or minimum point
\\ (sin: pi/2 + 2k pi and -pi/2 + 2k pi; cos: 2k pi and pi + 2k pi) or is unbounded; acos, asin,
\\ atan and tan are monotone on their domains. The values that are rational are taken exactly
\\ (f(0) for sin, tan, asin, atan; cos(0) = 1; acos(1) = 0; the bounds +-1); every other value
\\ f(x) at a rational x != 0 is irrational (Lindemann), so it is never equal to an end.
\\ Verdict: contained (holds), vacuous (holds, D empty), violated (fails), or undecided. A comparison
\\ is near when an end is within 2^-200 (relative) of the value it is compared with, or an end of D
\\ is within 2^-200 2 pi of a critical point of sin or cos, or within 2^-200 (relative) of pi/2 or
\\ -pi/2 for tan. A call with a near comparison is counted NEAR and checked again at twice the
\\ precision p, with the band 2^-(p - 120 - e), e the binary exponent of the ends (0 when below 1),
\\ up to 16384 bits; it is undecided when a
\\ comparison is still in the band there. (Near calls are the ends next to f(x) at a tiny x: sin x,
\\ tan x, atan x, asin x within x^3 of x, cos x within x^2 of 1.)
\\
\\ Input: lines k(op, a, b, c, d, n) (bits as 0x literals, n the number of calls with these
\\ arguments and result), and p(piLo, piHi, twoPiLo, twoPiHi) for the constants of iv.rs (also
\\ checked: piLo <= pi <= piHi, twoPiLo <= 2 pi <= twoPiHi). Usage: gp -q sound-trans.gp, then
\\ run(file) per input file and report() at the end.

NAN = "nan";
OPS = ["cos", "sin", "acos", "asin", "atan", "tan"];
\\ counts[op - 3][v]: v = 1 contained, 2 vacuous, 3 violated, 4 undecided; calls and distinct calls
CNT = matrix(6, 4); DST = matrix(6, 4);
\\ calls and distinct calls within the band 2^-200 at the first precision (decided at a higher one, or undecided)
NEAR = vector(6); DNEAR = vector(6);
SHOWN = 0;
BAND = 200;
PMAX = 16384;

\\ A binary64 value from its bits: an exact rational, +oo, -oo, or NAN.
fl(x) =
{
  my(s = shift(x, -63), e = bitand(shift(x, -52), 2047), m = bitand(x, 2^52 - 1), v);
  if (e == 2047, return (if (m, NAN, if (s, -oo, +oo))));
  v = if (e, (m + 2^52) * 2^(e - 1075), m * 2^(-1074));
  if (s, -v, v);
}
isnan(x) = type(x) == "t_STR";
isinf(x) = type(x) == "t_INFINITY";

\\ min and max of an exact value and a computed one (t_REAL): when they are equal at the working
\\ precision, the computed one, so that a comparison with it is near and is refined (the exact one
\\ would hide a true value just beside it, as cos x < 1 = cos 0 at a tiny x < 0).
emin(u, v) = if (u < v, u, if (v < u, v, if (type(u) == "t_REAL", u, v)));
emax(u, v) = if (u > v, u, if (v > u, v, if (type(u) == "t_REAL", u, v)));

\\ Working precision for finite ends u, v: 320 bits plus their binary exponent.
wp(u, v) =
{
  my(e = 0);
  if (!isinf(u) && u, e = max(e, exponent(u)));
  if (!isinf(v) && v, e = max(e, exponent(v)));
  320 + e;
}

\\ Sign of q - w for q exact (rational or infinite) and w exact or a t_REAL; "U" when w is a t_REAL
\\ and q is within 2^-BAND (relative) of it.
cmpb(q, w) =
{
  my(t);
  if (isinf(q) || isinf(w) || type(w) != "t_REAL", return (if (q < w, -1, if (q > w, 1, 0))));
  t = q - w;
  if (abs(t) <= 2.^-BAND * abs(w), return ("U"));
  sign(t);
}

\\ 1 when the closed interval [u, v] (finite exact ends) contains a point c0 + k per (k an integer),
\\ 0 when not, "U" when an end is within 2^-BAND per of such a point. The one rational such point,
\\ 0 (c0 = 0, k = 0), is decided exactly. Called at the precision of the caller.
hits(u, v, c0, per) =
{
  my(x = (u - c0) / per, y = (v - c0) / per, tol = 2.^-BAND, m, k1, k2);
  m = round(x);
  if (abs(x - m) <= tol,
    if (c0 == 0 && m == 0, k1 = if (u <= 0, 0, 1), return ("U"))
  , k1 = ceil(x));
  m = round(y);
  if (abs(y - m) <= tol,
    if (c0 == 0 && m == 0, k2 = if (v >= 0, 0, -1), return ("U"))
  , k2 = floor(y));
  k2 >= k1;
}

\\ [inf, sup] of op over D, or 0 when D is empty, or "U" when an end of D is undecided. Called at
\\ the precision wp(a, b) of the caller.
range(op, a, b) =
{
  my(h1, h2, u, v, w);
  if (isnan(a) || isnan(b) || a > b || a == +oo || b == -oo, return (0));
  if (op == 4 || op == 5,
    if (isinf(a) || isinf(b), return ([-1, 1]));
    w = cmpb(b - a, 2 * Pi);
    if (w === "U", return ("U"));
    if (w >= 0, return ([-1, 1]));
    if (op == 5,
      u = if (a, sin(a), 0); v = if (b, sin(b), 0);
      h1 = hits(a, b, Pi / 2, 2 * Pi); h2 = hits(a, b, -Pi / 2, 2 * Pi)
    ,
      u = if (a, cos(a), 1); v = if (b, cos(b), 1);
      h1 = hits(a, b, 0, 2 * Pi); h2 = hits(a, b, Pi, 2 * Pi)
    );
    if (h1 === "U" || h2 === "U", return ("U"));
    return ([if (h2, -1, emin(u, v)), if (h1, 1, emax(u, v))])
  );
  if (op == 6 || op == 7,
    if (a > 1 || b < -1, return (0));
    u = max(a, -1); v = min(b, 1);
    if (op == 6,
      return ([if (v == 1, 0, acos(v)), if (u == 1, 0, acos(u))])
    ,
      return ([if (u, asin(u), 0), if (v, asin(v), 0)])
    )
  );
  if (op == 8,
    return ([if (a == -oo, -Pi / 2, if (a, atan(a), 0)), if (b == +oo, Pi / 2, if (b, atan(b), 0))])
  );
  if (op == 9,
    h1 = cmpb(a, Pi / 2); h2 = cmpb(b, -Pi / 2);
    if (h1 === "U" || h2 === "U", return ("U"));
    if (h1 >= 0 || h2 <= 0, return (0));
    h1 = cmpb(a, -Pi / 2); h2 = cmpb(b, Pi / 2);
    if (h1 === "U" || h2 === "U", return ("U"));
    return ([if (h1 <= 0, -oo, if (a, tan(a), 0)), if (h2 >= 0, +oo, if (b, tan(b), 0))])
  );
  error("op ", op);
}

\\ The verdict of one call: 1 contained, 2 vacuous, 3 violated, 4 undecided.
verdict(op, a, b, c, d, pr) =
{
  my(r, s, t);
  localbitprec(pr);
  r = range(op, a, b);
  if (r === 0, return (2));
  if (r === "U", return (4));
  if (isnan(c) || isnan(d), return (3));
  s = cmpb(c, r[1]); t = cmpb(d, r[2]);
  if ((!(s === "U") && s > 0) || (!(t === "U") && t < 0), return (3));
  if (s === "U" || t === "U", return (4));
  1;
}

k(op, A, B, C, D, n) =
{
  my(a = fl(A), b = fl(B), c = fl(C), d = fl(D), pr, e0, v);
  if (isnan(a) || isnan(b), CNT[op - 3, 2] += n; DST[op - 3, 2]++; return);
  pr = wp(a, b); e0 = pr - 320; BAND = 200;
  v = verdict(op, a, b, c, d, pr);
  if (v == 4,
    NEAR[op - 3] += n; DNEAR[op - 3]++;
    while (v == 4 && 2 * pr <= PMAX, pr *= 2; BAND = pr - 120 - e0; v = verdict(op, a, b, c, d, pr)));
  CNT[op - 3, v] += n; DST[op - 3, v]++;
  if (v >= 3 && SHOWN < 1000,
    SHOWN++;
    printf("%s %s %016x %016x %016x %016x calls %d\n", if (v == 3, "VIOLATED", "UNDECIDED"),
      OPS[op - 3], A, B, C, D, n));
}

p(A, B, C, D) =
{
  my(v = [fl(A), fl(B), fl(C), fl(D)]);
  localbitprec(320);
  printf("CONST piLo %s piHi %s twoPiLo %s twoPiHi %s\n",
    if (v[1] <= Pi, "holds", "FAILS"), if (Pi <= v[2], "holds", "FAILS"),
    if (v[3] <= 2 * Pi, "holds", "FAILS"), if (2 * Pi <= v[4], "holds", "FAILS"));
}

run(f) = read(f);

report() =
{
  print("# op calls contained vacuous violated undecided | distinct contained vacuous violated undecided");
  for (i = 1, 6,
    printf("T %s %d %d %d %d %d | %d %d %d %d %d\n", OPS[i], vecsum(CNT[i, ]), CNT[i, 1], CNT[i, 2],
      CNT[i, 3], CNT[i, 4], vecsum(DST[i, ]), DST[i, 1], DST[i, 2], DST[i, 3], DST[i, 4]));
  printf("NEAR calls %d distinct %d (within 2^-200 at the first precision; decided at a higher one unless undecided)\n", vecsum(NEAR), vecsum(DNEAR));
  printf("TOTAL calls %d contained %d vacuous %d violated %d undecided %d\n", vecsum(concat(Vec(CNT))),
    vecsum(CNT[, 1]), vecsum(CNT[, 2]), vecsum(CNT[, 3]), vecsum(CNT[, 4]));
}
