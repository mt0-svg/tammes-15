\\ Proposition 4.6 of the paper by an inscribed polygon: the polygon with the two common tangent points of each
\\ side and k + 1 points on each outer arc has perimeter
\\ perHex(l, h, k) = 2 L + 2 k acos(cos(h)^2 + sin(h)^2 cos((2 Pi - 2 g)/k)), cos L = (cos l - sin^2 h)/cos^2 h,
\\ cos g = -tan h tan(l/2), l = d, h = hrad(d). L increases with l and h; g increases with l and h, so the
\\ arc step decreases; the chord term increases with h and with the step. Worst-end bound on a whole
\\ interval [a, b]: 2 L(a, h(a)) + 2 k chord(h(a), step(b, h(b))) - 6 b. Floating point, 60 digits.
default(realprecision, 60);
deg = Pi/180; dlo = 5365785/100000*deg; dhi = 566716/10000*deg;
hrad(d) = acos(cos(d)/cos(d/2));
Lt(l, h) = acos((cos(l) - sin(h)^2)/cos(h)^2);
gt(l, h) = acos(-tan(h)*tan(l/2));
ch(h, s) = acos(cos(h)^2 + sin(h)^2*cos(s));
perHex(l, h, k) = 2*Lt(l, h) + 2*k*ch(h, (2*Pi - 2*gt(l, h))/k);
for(k = 4, 4, print("k = ", k, ": perHex - 6d at dlo, dhi: ", (perHex(dlo, hrad(dlo), k) - 6*dlo)/deg, ", ", (perHex(dhi, hrad(dhi), k) - 6*dhi)/deg));
worst(a, b, k) = 2*Lt(a, hrad(a)) + 2*k*ch(hrad(a), (2*Pi - 2*gt(b, hrad(b)))/k) - 6*b;
for(k = 4, 8, if(k == 4 || k == 8, print("k = ", k, ": worst-end bound on [dlo, dhi]: ", worst(dlo, dhi, k)/deg, " deg")));
for(k = 4, 8, if(k == 4 || k == 8, for(n = 1, 4, my(m = 1e9); for(i = 0, n - 1, my(a = dlo + (dhi - dlo)*i/n, b = dlo + (dhi - dlo)*(i + 1)/n); m = min(m, worst(a, b, k))); print("k = ", k, ", ", n, " pieces: min worst-end bound ", m/deg, " deg"))));
for(n = 5, 40, my(m = 1e9); for(i = 0, n - 1, my(a = dlo + (dhi - dlo)*i/n, b = dlo + (dhi - dlo)*(i + 1)/n); m = min(m, worst(a, b, 4))); if(m > 0, print("k = 4: first positive at ", n, " equal pieces, min worst-end bound ", m/deg, " deg"); break));
for(n = 5, 40, my(m = 1e9); for(i = 0, n - 1, my(a = dlo + (dhi - dlo)*i/n, b = dlo + (dhi - dlo)*(i + 1)/n); m = min(m, worst(a, b, 4))); if(n == 10 || n == 20 || n == 40, print("k = 4, ", n, " pieces: min worst-end bound ", m/deg, " deg")));
\\ The ten pieces of the Lean statements hex_piece_i (Rattlers/HexPoly.lean): dpt(i) = (10731570 + 60275 i)/200000 deg.
dpt(i) = (10731570 + 60275*i)/200000*deg;
print("dpt(0) = dlo: ", dpt(0) == dlo, ", dpt(10) = dhi: ", dpt(10) == dhi);
for(i = 0, 9, my(a = dpt(i), b = dpt(i + 1)); print("piece ", i, ": 2 L(a) + 8 chord - 6 b = ", worst(a, b, 4)/deg, " deg; 2 L(a) = ", 2*Lt(a, hrad(a))/deg, ", 8 chord = ", 8*ch(hrad(a), (2*Pi - 2*gt(b, hrad(b)))/4)/deg, ", 6 b = ", 6*b/deg));
\\ Hint data for hex_piece_i: rho_a = cos a / cos(a/2) = cos(hrad a); Y1 = (cos a - 1 + rho_a^2)/rho_a^2 (so
\\ tanLen a (hrad a) = acos Y1); X_b = tan(hrad b) tan(b/2); Y2 = rho_a^2 + (1 - rho_a^2) sqrt((1 + X_b)/2) (so the
\\ chord is acos Y2); targets t1, t2 in degrees (multiples of 1/100) with 2 t1 + 8 t2 > 6 b, Y1 < cos t1, Y2 < cos t2.
hintdata() = {
  for(i = 0, 9,
    my(a = dpt(i), b = dpt(i + 1), ra = cos(a)/cos(a/2), rb = cos(b)/cos(b/2), Y1, X, Y2, m, t1, t2);
    Y1 = (cos(a) - 1 + ra^2)/ra^2; X = sqrt(1 - rb^2)/rb*tan(b/2); Y2 = ra^2 + (1 - ra^2)*sqrt((1 + X)/2);
    m = (2*acos(Y1) + 8*acos(Y2) - 6*b)/deg;
    t1 = floor((acos(Y1)/deg - m/8)*100)/100; t2 = floor((acos(Y2)/deg - m/32)*100)/100;
    printf("piece %d: a = %.6f deg, b = %.6f deg, rho_a = %.10f, Y1 = %.10f, X_b = %.10f, Y2 = %.10f, acos Y1 = %.8f deg, acos Y2 = %.8f deg, margin %.4f deg; targets t1 = %s deg, t2 = %s deg: 2 t1 + 8 t2 - 6 b = %.6f deg, cos t1 - Y1 = %.8f, cos t2 - Y2 = %.8f\n",
      i, a/deg, b/deg, ra, Y1, X, Y2, acos(Y1)/deg, acos(Y2)/deg, m, t1, t2, 2*t1 + 8*t2 - 6*b/deg, cos(t1*deg) - Y1, cos(t2*deg) - Y2));
}
hintdata();
quit
