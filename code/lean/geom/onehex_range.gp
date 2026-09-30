\\ The margins of Proposition onehex outside [dlo, dhi]. hexPoly(d, h(d)) - 6d (perimeter
\\ margin, k = 4 chords per arc), E(d) (extreme chord against the other disc) and alpha(d), for d from 51 to 64
\\ degrees; then the minimum of the perimeter margin over [dlo, dhi] for k = 1 to 5 chords per arc.
\\ Floating point, 40 digits: numerical evidence only.
default(realprecision, 40);
hrad(d) = acos(cos(d)/cos(d/2));
tanLen(l,h) = acos((cos(l) - sin(h)^2)/cos(h)^2);
tanAng(l,h) = acos(-tan(h)*tan(l/2));
chordC(h,s) = acos(cos(h)^2 + sin(h)^2*cos(s));
hexPoly(l,h) = 2*tanLen(l,h) + 8*chordC(h, (2*Pi - 2*tanAng(l,h))/4);
alpha(d) = acos(cos(d)/(1+cos(d)));
Echord(d) = my(h = hrad(d), g = tanAng(d, h), s = (Pi - g)/2, m = 3*s/2); cos(h)*sin(d)*cos(m) + sin(h)*cos(s/2)*cos(d) - sin(h)*sqrt(cos(h)^2 + sin(h)^2*cos(s/2)^2);
forstep(deg = 51.0, 64.0, 0.5, my(d = deg*Pi/180, h = hrad(d)); printf("d = %5.2f deg: hexPoly - 6d = %9.6f, E = %9.6f, alpha = %7.3f deg\n", deg, hexPoly(d,h) - 6*d, Echord(d), alpha(d)*180/Pi));
printf("2pi/7 = %.4f deg; alpha = 72 deg at d = %.4f deg\n", 360/7., solve(x = 0.9, 1.2, alpha(x) - 2*Pi/5)*180/Pi);
polyk(l,h,k) = 2*tanLen(l,h) + 2*k*chordC(h, (2*Pi - 2*tanAng(l,h))/k);
dlo = 53.65785*Pi/180; dhi = 56.6716*Pi/180;
for(k = 1, 5, my(mn = 10); for(i = 0, 200, my(d = dlo + i*(dhi-dlo)/200, h = hrad(d)); mn = min(mn, polyk(d,h,k) - 6*d)); printf("k = %d chords per arc: min (perim - 6d) over [dlo, dhi] = %.6f\n", k, mn));
\q
