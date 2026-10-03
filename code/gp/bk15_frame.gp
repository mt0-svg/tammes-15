\\ The Buddenhagen-Kottwitz construction of the 18-point frame and of C3, C1 (Section 3), in floating point at 60 digits; read by bk15_c3_coords.gp.
default(realprecision, 60);
pu = 13*x^5 - x^4 + 6*x^3 + 2*x^2 - 3*x - 1;
print("pu irreducible over Q: ", polisirreducible(pu));
rts = polroots(pu); print("roots: ", rts);
u = real(select(z -> abs(imag(z)) < 1e-40 && real(z) > 0.5 && real(z) < 0.7, rts)[1]);
print("u = ", u, "   d15 = acos(u) deg = ", acos(u)*180/Pi);
qb = 9*(4*u^2-u-1)*(3*u+1)^2*y^2 + 2*u*(62*u^4-155*u^3-37*u^2+51*u+15)*y + u^2*(4*u^2-u-1)*(5*u-1)^2;
bb = polroots(qb); print("b^2 roots: ", bb);
b = sqrt(real(bb[1])); if(abs(b-0.1714903098)>1e-6, b = sqrt(real(bb[2])));
c = b*(27*b^2*u^2+18*b^2*u+29*u^3+3*b^2-18*u^2-11*u)/((3*u+1)*(9*b^2*u+3*b^2-5*u^2+u));
a = (u - b*c)/(b+c);
print("a,b,c = ", [a,b,c]);
print("check a^2+b^2+c^2-1 = ", a^2+b^2+c^2-1, "  ab+bc+ca-u = ", a*c+b*a+c*b-u);
dd = ((2*a-b+2*c)*u-b)/(u+1); ee = ((2*a+2*b-c)*u-c)/(u+1); ff = ((-a+2*b+2*c)*u-a)/(u+1);
r = ((6*a-2*c+3*b)*u^2+2*(a-b-c)*u-b)/(u+1)^2;
s = ((6*b-2*a+3*c)*u^2+2*(b-c-a)*u-c)/(u+1)^2;
t = ((6*c-2*b+3*a)*u^2+2*(c-a-b)*u-a)/(u+1)^2;
L = {[["V1",[a,b,c]],["V2",[c,a,b]],["V3",[b,c,a]],      ["V12",[dd,ee,ff]],["V23",[ff,dd,ee]],["V31",[ee,ff,dd]],      ["P",[r,s,t]],["I",[t,r,s]],["A",[s,t,r]],      ["Q",[-t,-s,-r]],["J",[-r,-t,-s]],["B",[-s,-r,-t]],      ["W12",[-ff,-ee,-dd]],["W23",[-ee,-dd,-ff]],["W31",[-dd,-ff,-ee]],      ["W1",[-c,-b,-a]],["W2",[-b,-a,-c]],["W3",[-a,-c,-b]]]};
print("max |norm-1| over 18 points: ", vecmax(vector(18,i,abs(L[i][2]*L[i][2]~-1))));
analyse(keep) = {   my(n=#keep, X=vector(n,i,L[keep[i]][2]), G, m, deg=vector(n), E=0, nm=[]);   G = matrix(n,n,i,j, if(i==j,-2, X[i]*X[j]~));   m = vecmax(concat(vector(n,i,vecmax(G[i,]))));   for(i=1,n, for(j=i+1,n, if(G[i,j] > m - 1e-40, E++; deg[i]++; deg[j]++)));   print("  max inner product - u = ", m-u, "; min angle deg = ", acos(m)*180/Pi);   print("  contacts (|<x,y>-max|<1e-40): ", E, "; degree histogram 0..5: ", vector(6,k,#select(z->z==k-1,deg)));   print("  names/degrees: ", vector(n,i,[L[keep[i]][1],deg[i]]));   my(s2 = vecsort(concat(vector(n,i,vector(n-i,j,G[i,i+j]))),,4));   print("  second largest inner product gap: ", m - select(z->z < m-1e-30, s2)[1]); };
all18 = vector(18,i,i);
print("18-point frame:"); analyse(all18);
print("C3 candidate: drop Q,J,B"); analyse([1,2,3,4,5,6,7,8,9,13,14,15,16,17,18]);
print("C1 candidate: drop Q,J,A"); analyse([1,2,3,4,5,6,7,8,12,13,14,15,16,17,18]);
print("angle P-Q deg: ", acos(L[7][2]*L[10][2]~)*180/Pi);
{ for(i=7,9, for(j=10,12, print(L[i][1],"-",L[j][1]," angle deg: ", acos(L[i][2]*L[j][2]~)*180/Pi))); }
print("C1 candidate: keep P,I and the partner-free one of Q,J,B");
{ for(j=10,12, my(ok=1); for(i=7,8, if(acos(L[i][2]*L[j][2]~)*180/Pi < 50, ok=0)); if(ok, print(" keep P,I,",L[j][1]); analyse([1,2,3,4,5,6,7,8,j,13,14,15,16,17,18]))); }
faces(keep) = {   my(n=#keep, X=vector(n,i,L[keep[i]][2]), G, m, nb=vector(n,i,List()), rot, F=List(), used=Map(), sz=vector(8));   G = matrix(n,n,i,j, if(i==j,-2, X[i]*X[j]~));   m = vecmax(concat(vector(n,i,vecmax(G[i,]))));   for(i=1,n, for(j=1,n, if(j!=i && G[i,j] > m-1e-40, listput(nb[i], j))));   rot = vector(n, i, my(p=X[i], e1, e2, w, ang);        w = X[nb[i][1]] - (X[nb[i][1]]*p~)*p; e1 = w/sqrt(w*w~);       e2 = [p[2]*e1[3]-p[3]*e1[2], p[3]*e1[1]-p[1]*e1[3], p[1]*e1[2]-p[2]*e1[1]];       ang = vector(#nb[i], k, my(q=X[nb[i][k]]); atan2(q*e2~, q*e1~));        my(perm = vecsort(ang,,1)); vector(#perm, k, nb[i][perm[k]]));   for(i=1,n, for(k=1,#rot[i], my(j=rot[i][k]);      if(!mapisdefined(used,[i,j]), my(f=List(), a=i, b=j);         while(!mapisdefined(used,[a,b]), mapput(used,[a,b],1); listput(f,a);            my(r=rot[b], pos=0); for(t=1,#r, if(r[t]==a, pos=t));            my(c = r[if(pos==1, #r, pos-1)]); a=b; b=c);         listput(F, Vec(f)))));   for(k=1,#F, sz[#F[k]]++);   print("  #faces = ", #F, "; face size histogram (3..7): ", vector(5,k,sz[k+2]));   print("  non-triangular faces: ", select(f->#f>3, Vec(F))); };
atan2(y,x) = arg(x + I*y);
print("C3 faces:"); faces([1,2,3,4,5,6,7,8,9,13,14,15,16,17,18]);
print("C1 faces:"); faces([1,2,3,4,5,6,7,8,11,13,14,15,16,17,18]);
deg5adj(keep) = { my(n=#keep, X=vector(n,i,L[keep[i]][2]), G=matrix(n,n,i,j, if(i==j,-2, X[i]*X[j]~)), dg, D5, E5=0); dg=vector(n,i,#select(z->z>u-1e-40, G[i,])); D5=select(z->dg[z]==5, vector(n,i,i)); for(a=1,#D5, for(b=a+1,#D5, if(G[D5[a],D5[b]]>u-1e-40, E5++))); print("  degree-5 vertices: ", vector(#D5,k,L[keep[D5[k]]][1]), "; edges among them: ", E5); };
print("C3:"); deg5adj([1,2,3,4,5,6,7,8,9,13,14,15,16,17,18]);
print("C1:"); deg5adj([1,2,3,4,5,6,7,8,11,13,14,15,16,17,18]);
\\ 3-connectivity check: removing any two vertices leaves the contact graph connected (plantri -p only generates 3-connected graphs)
conn3(keep) = { my(n=#keep, X=vector(n,i,L[keep[i]][2]), A=matrix(n,n,i,j, i!=j && X[i]*X[j]~ > u-1e-40), bad=0); for(a=1,n, for(b=a+1,n, my(alive=vector(n,i,i!=a&&i!=b), seen=vector(n), st=List(), s0=if(a!=1&&b!=1,1,if(a!=2&&b!=2,2,3)), cnt=1); seen[s0]=1; listput(st,s0); while(#st, my(v=st[#st]); listpop(st); for(w=1,n, if(alive[w] && !seen[w] && A[v,w], seen[w]=1; cnt++; listput(st,w)))); if(cnt < n-2, bad++))); print("  vertex pairs whose removal disconnects: ", bad, " (0 means 3-connected)"); };
print("C3 3-connectivity:"); conn3([1,2,3,4,5,6,7,8,9,13,14,15,16,17,18]);
print("C1 3-connectivity:"); conn3([1,2,3,4,5,6,7,8,11,13,14,15,16,17,18]);
