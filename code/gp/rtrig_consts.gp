\\ Constants of code/impl1/rust/src/rtrig.rs (rigorous elementary functions), 200 digits.
\\ For a real v > 0: dlo(v), dhi(v) = the largest double <= v and the smallest double >= v,
\\ printed as IEEE bit patterns (hex). Cody-Waite split of pi/2: P1 = floor(pi/2 2^31)/2^31,
\\ P2 = floor((pi/2 - P1) 2^63)/2^63 (each has <= 32 significant bits), P3 = pi/2 - P1 - P2
\\ (enclosed by doubles). A_j = atan(j/8), j = 1..8.
default(realprecision, 200);
bits(x) = { \\ x a positive dyadic rational representable as a normal double
  my(e = floor(log(x)/log(2)), m);
  if (2^e > x, e--); if (2^(e+1) <= x, e++);
  m = x / 2^(e-52);
  if (denominator(m) != 1 || m < 2^52 || m >= 2^53, error("not a double"));
  (e + 1023) * 2^52 + (m - 2^52);
}
dlo(v) = { my(e = floor(log(v)/log(2))); if (2^e > v, e--); if (2^(e+1) <= v, e++); floor(v / 2^(e-52)) * 2^(e-52) };
dhi(v) = { my(e = floor(log(v)/log(2))); if (2^e > v, e--); if (2^(e+1) <= v, e++); ceil(v / 2^(e-52)) * 2^(e-52) };
hx(x) = Str("0x", strjoin([Str(c) | c <- Vec(Strprintf("%016x", bits(x)))], ""));
h = Pi/2;
P1 = floor(h * 2^31) / 2^31;
P2 = floor((h - P1) * 2^63) / 2^63;
P3 = h - P1 - P2;
print("P1 ", hx(P1), " exact ", P1);
print("P2 ", hx(P2), " exact ", P2);
print("P3 lo ", hx(dlo(P3)), " hi ", hx(dhi(P3)), " P3 = ", P3);
print("PI lo ", hx(dlo(Pi)), " hi ", hx(dhi(Pi)));
for (j = 1, 8, my(a = atan(j/8)); print("A", j, " lo ", hx(dlo(a)), " hi ", hx(dhi(a)), "  ", a));
\\ sanity: P1, P2 have at most 32 significant bits
print("P1 bits ", #binary(numerator(P1)), "  P2 bits ", #binary(numerator(P2)));
\\ remainder bounds used in rtrig.rs
print("cos rem 0.8^22/22! = ", 0.8^22/22!, "   sin rem 0.8^23/23! = ", 0.8^23/23!);
print("atan rem (1/16)^15/15 = ", (1/16.)^15/15);
