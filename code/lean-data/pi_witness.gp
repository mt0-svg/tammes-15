\\ pi_witness.gp: the witness of `pi_upper_bound` (Mathlib, Mathlib/Analysis/Real/Pi/Bounds.lean) for
\\ pi < a = 3.141592653589793238463 with n = 38 steps: l_1 <= sqrt 2, l_(i+1) <= sqrt (2 + l_i) (each l_i the
\\ root rounded down to 50 decimals, by integer square roots), and 2 - ((a - 1/4^n) / 2^(n+1))^2 <= l_n.
\\ Prints the conditions checked in exact arithmetic, then the list for the Lean tactic.
\\ Usage, from the repository root: gp -q code/lean-data/pi_witness.gp > code/lean-data/pi_witness.out (code/lean-data/regen.sh
\\ checks that the list is the one of Tammes15/Params/Pi.lean)
a = 3141592653589793238463 / 10^21; n = 38; D = 10^50;
L = vector(n); cur = 0;
for (i = 1, n, m = sqrtint(floor((2 + cur) * D^2)); L[i] = m / D; cur = L[i]);
okc = 1; prev = 0;
for (i = 1, n, if (!(L[i]^2 <= 2 + prev), okc = 0; print("step ", i, " FAILS")); prev = L[i]);
fin = 2 - ((a - 1/4^n) / 2^(n+1))^2;
print("steps l_(i+1)^2 <= 2 + l_i: ", if(okc, "OK", "FAIL"));
print("final 2 - ((a - 1/4^n)/2^(n+1))^2 <= l_n: ", if(fin <= L[n], "OK", "FAIL"), ", slack ", (L[n] - fin) * 1.);
print("1/4^n <= a: ", if(1/4^n <= a, "OK", "FAIL"));
print("LIST");
s = ""; for (i = 1, n, s = concat(s, Str(numerator(L[i]), "/", denominator(L[i]))); if (i < n, s = concat(s, ", ")));
print(s);
quit;
