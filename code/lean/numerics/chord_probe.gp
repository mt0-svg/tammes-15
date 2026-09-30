\\ Feasibility of the worst-end bound for onehex_chord_margin on the ten pieces [dpt i, dpt (i+1)]
\\ (floating point, 60 digits; the certified version is chord.gp). E(d) = cos h sin d cos(3s/2) + sin h cos(s/2) cos d
\\ - sin h sqrt(cos^2 h + sin^2 h cos^2(s/2)), h = hrad d, s = (Pi - tanAng d h)/2. Worst end on [a, b]:
\\ cos h(b) sin a cos(3 s(a)/2) + sin h(a) cos(s(a)/2) cos b - sin h(b) sqrt(1 - sin^2 h(a) sin^2 (s(b)/2)).
default(realprecision, 60);
hrad(d) = acos(cos(d)/cos(d/2));
gt(l, h) = acos(-tan(h)*tan(l/2));
sofd(d) = (Pi - gt(d, hrad(d)))/2;
E(d) = my(h = hrad(d), s = sofd(d)); cos(h)*sin(d)*cos(3*s/2) + sin(h)*cos(s/2)*cos(d) - sin(h)*sqrt(cos(h)^2 + sin(h)^2*cos(s/2)^2);
W(a, b) = my(ha = hrad(a), hb = hrad(b), sa = sofd(a), sb = sofd(b)); cos(hb)*sin(a)*cos(3*sa/2) + sin(ha)*cos(sa/2)*cos(b) - sin(hb)*sqrt(1 - sin(ha)^2*sin(sb/2)^2);
qd(j) = (10731570 + 60275*j)/36000000;
for(i = 0, 9, my(a = qd(i)*Pi, b = qd(i+1)*Pi); printf("piece %d: E(a) = %.6f, E(b) = %.6f, worst-end bound %.6f\n", i, E(a), E(b), W(a, b)));
for(n = 1, 10, my(m = 1); for(i = 0, n - 1, my(a = qd(10*i/n)*Pi, b = qd(10*(i+1)/n)*Pi); m = min(m, W(a, b))); printf("%d equal pieces: min worst-end bound %.6f\n", n, m));
quit
