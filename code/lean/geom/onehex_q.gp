\\ The ten vertex polygon Q of Proposition onehex (paper Section 3, Proposition onehex).
\\ Two circles of radius h = h(d) about C and R, sdist(C, R) = d; frame (T, F, C) right handed at C with
\\ T pointing away from R, so R = cos d C - sin d T. Circle points S(psi) = cos h C + sin h (cos psi T + sin psi F)
\\ about C; about R the frame (T', F', R) with T' = -(cos d T + sin d C) pointing away from C and F' = -F.
\\ gamma = tanAng(d, h) = acos(-tan h tan(d/2)), s = (pi - gamma)/2; S_j = S(-(pi - gamma) + j s), R_j likewise.
\\ Checks (floating point, 60 digits, numerical evidence): strict support of Q (all 80 triples), the extreme
\\ chord condition E(d) > 0 on [dlo, dhi], tangency of the two connecting sides, perimeter = hexPoly(d, h).
default(realprecision, 60);
cross(a,b) = [a[2]*b[3]-a[3]*b[2], a[3]*b[1]-a[1]*b[3], a[1]*b[2]-a[2]*b[1]];
dot(a,b) = sum(i=1,3,a[i]*b[i]);
tri(a,b,c) = dot(cross(a,b),c);
hrad(d) = acos(cos(d)/cos(d/2));
tanLen(l,h) = acos((cos(l) - sin(h)^2)/cos(h)^2);
tanAng(l,h) = acos(-tan(h)*tan(l/2));
chordC(h,s) = acos(cos(h)^2 + sin(h)^2*cos(s));
hexPoly(l,h) = 2*tanLen(l,h) + 8*chordC(h, (2*Pi - 2*tanAng(l,h))/4);
dlo = 53.65785*Pi/180; dhi = 56.6716*Pi/180;
\\ coordinates: C = e3, T = e1, F = e2
poly(d) =
{
  my(h = hrad(d), g = tanAng(d, h), s = (Pi - g)/2, C = [0,0,1], T = [1,0,0], F = [0,1,0], R, Tp, Fp, Q = vector(10));
  R = cos(d)*C - sin(d)*T; Tp = -(cos(d)*T + sin(d)*C); Fp = -F;
  \\ Tp: unit tangent at R pointing away from C (derivative of cos(t) C - sin(t) T at t = d is -sin d C - cos d T)
  for(j = 0, 4, my(p = -(Pi - g) + j*s); Q[j+1] = cos(h)*C + sin(h)*(cos(p)*T + sin(p)*F));
  for(j = 0, 4, my(p = -(Pi - g) + j*s); Q[j+6] = cos(h)*R + sin(h)*(cos(p)*Tp + sin(p)*Fp));
  [Q, h, g, s, C, R];
}
support(d) =
{
  my(P = poly(d), Q = P[1], mn = 10, arg = 0);
  for(i = 0, 9, for(k = 2, 9,
    my(v = tri(Q[i+1], Q[(i+1)%10+1], Q[(i+k)%10+1]));
    if(v < mn, mn = v; arg = [i, k])));
  [mn, arg];
}
\\ E(d): the extreme chord (S_3, S_4) of the circle about C against the disc about R: cos h sin d cos m + sin h cos(s/2) cos d
\\ - sin h sqrt(cos^2 h + sin^2 h cos^2(s/2)) with m = 3s/2 its midpoint angle; E > 0 puts the whole disc about R
\\ strictly inside the half space of the chord (the middle chords, |m| = s/2, have a larger cos m)
Echord(d) =
{
  my(h = hrad(d), g = tanAng(d, h), s = (Pi - g)/2, m = 3*s/2);
  cos(h)*sin(d)*cos(m) + sin(h)*cos(s/2)*cos(d) - sin(h)*sqrt(cos(h)^2 + sin(h)^2*cos(s/2)^2);
}
perim(d) = my(Q = poly(d)[1]); sum(i = 0, 9, acos(dot(Q[i+1], Q[(i+1)%10+1])));
tangency(d) =
{
  my(P = poly(d), Q = P[1], h = P[2], C = P[5], R = P[6], n1, n2);
  n1 = cross(Q[5], Q[6]); n1 = n1/sqrt(dot(n1,n1));
  n2 = cross(Q[10], Q[1]); n2 = n2/sqrt(dot(n2,n2));
  [dot(n1, C) - sin(h), dot(n1, R) - sin(h), dot(n2, C) - sin(h), dot(n2, R) - sin(h)];
}
{
  for(k = 0, 10,
    my(d = dlo + k*(dhi - dlo)/10, sp = support(d));
    printf("d = %.6f deg: min triple = %.6e at [i,k] = %s, E(d) = %.6e, perim - hexPoly = %.3e, tangency residuals %s\n",
      d*180/Pi, sp[1], sp[2], Echord(d), perim(d) - hexPoly(d, hrad(d)), apply(x -> round(x*10^50)/10^50*1., tangency(d))));
  my(mn = 10, am = 0);
  for(k = 0, 3000, my(d = dlo + k*(dhi - dlo)/3000, e = Echord(d)); if(e < mn, mn = e; am = d));
  printf("min of E over 3001 points of [dlo, dhi]: %.10f at d = %.6f deg\n", mn, am*180/Pi);
  my(mn = 10);
  for(k = 0, 300, my(d = dlo + k*(dhi - dlo)/300, e = support(d)[1]); if(e < mn, mn = e));
  printf("min strict support triple over 301 points: %.10f\n", mn);
}
\q
