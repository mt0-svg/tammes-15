\\ Coordinates of the C3 (and C1) conjectured optimal 15-point codes of Buddenhagen-Kottwitz,
\\ from bk15_frame.gp (18-point frame L), written in the format of Sloane's table (3 numbers per line)
\\ to data/bk15_c3.txt and data/bk15_c1.txt, read by contact_graphs.gp and ../paper/figure1.gp. Run from code/gp.
default(parisizemax, 200000000); default(nbthreads, 1);
\r bk15_frame.gp
dump(keep, file) = { system(concat("rm -f ", file)); for(i=1, #keep, my(x = L[keep[i]][2]); write(file, Strprintf("%.25f %.25f %.25f", x[1], x[2], x[3]))); };
dump([1,2,3,4,5,6,7,8,9,13,14,15,16,17,18], "../../data/bk15_c3.txt");
dump([1,2,3,4,5,6,7,8,11,13,14,15,16,17,18], "../../data/bk15_c1.txt");
