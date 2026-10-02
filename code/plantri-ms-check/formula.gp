\\ T(n,k) of OEIS A290326 (Mullin and Schellenberg 1968): the number of flag-rooted 3-connected
\\ plane maps (c-nets) with n+1 faces and k+1 vertices, by the closed formula of the entry.
T(n,k) = sum(i = 0, k - 1, sum(j = 0, n - 1, (-1)^(i + j + 1) * (i + j + 2)! / (2 * i! * j!) \
  * (binomial(2*n, k-i-1) * binomial(2*k, n-j-1) - 4 * binomial(2*n-1, k-i-2) * binomial(2*k-1, n-j-2))));
