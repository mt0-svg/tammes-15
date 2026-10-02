# plantri against the formula of Mullin and Schellenberg

The check (b) of Section 6.1 of the paper, second part.

## What is checked

A 3-connected plane graph G with E edges gives 4E/|Aut G| rooted maps, where Aut G is its automorphism group, reflections included. Over the list `plantri -p n` (the 3-connected planar graphs on n vertices, one per isomorphism class), the sum of 4E/|Aut G| over the graphs with F faces must therefore equal T(F-1, n-1) of OEIS A290326, the closed formula of Mullin and Schellenberg (J. Combin. Theory 4 (1968), 259 to 276) for the rooted 3-connected maps with n vertices and F faces. The formula is evaluated as stated in the entry; some values of the table printed in 1968 differ from it (`out/kat.out`, negative controls).

|Aut G| is the value that plantri passes to a filter plugin (`nbtot`), exact with the switch `-G` (`code/impl1/enum/plantri-guide.txt`). In the same pass the plugin counts the graphs of the class (maximum degree at most 5, faces of size at most 6), and the check compares this count with the counts of the enumeration (`code/impl1/out/filtercheck_n4_13.txt`, `filtercheck_n14.txt`, `filtercheck_n15.txt`).

A missing graph lowers one sum and a repeated graph raises one. An error that cancels within one (vertices, faces) value is not seen: `out/negctl/` shows such an error passing the comparison of the sums, caught only by the total number of graphs.

## Files

| file | role |
| --- | --- |
| `plantri_ms.c` | the plugin: counts per (F, nbtot) and the class members among them; with `-DMS_CHECK` it also walks the faces of every graph and stops unless their number is E - n + 2, every degree is at least 3 and every face has at least 3 edges |
| `build.sh` | builds `plantri_ms` and `plantri_ms_chk` from the plantri 5.8 tarball (sha256 checked) with `cc -O3`, as `code/impl1/enum/build_plantri.sh` builds `plantri_md5` |
| `formula.gp` | T(n,k) by the closed formula of A290326 |
| `kat.gp`, `kat.sh` | known-answer tests of the formula (hand values, the b-file of A290326 on rows 1 to 30, duality, row sums against A106651) and negative controls (the values printed in 1968, shifted indices), output `out/kat.out` |
| `run.sh` | one part `plantri_ms -p -G -u n res/mod`, output `out/n<n>/part_<res>of<mod>.txt` (command, sha256 of the binary, the sums, the count of plantri, times) |
| `parts.sh` | runs the missing parts of one modulus, J at a time, one core each |
| `check.gp`, `check.sh` | the comparison, output `out/check_n<n>.out` |
| `negctl.sh` | negative controls of the comparison on edited copies of the output at n = 12, outputs in `out/negctl/` |
| `times.sh` | core and wall times per n, output `out/times.txt` |
| `ref/` | the first 843 lines (rows 1 to 30) of the b-file of A290326 |

`out/build.txt` records the build used for every run and a second build from the same sources, byte for byte equal; every part file records the sha256 of the binary that wrote it. `out/chk/` holds the runs of `plantri_ms_chk` for n = 4 to 13 and their comparison with `plantri_ms` (`out/chk/compare.out`: the same sums, so the number of faces by Euler's formula is the number of faces that plantri's embedding has).

## Rerun

From this folder, with the tarball downloaded or given by `PLANTRI_TGZ`:

```sh
sh build.sh
sh kat.sh
for n in 4 5 6 7 8 9 10 11 12 13; do sh run.sh $n 0 1; done
sh parts.sh 14 4 2
sh parts.sh 15 16 2
for n in 4 5 6 7 8 9 10 11 12 13 14 15; do sh check.sh $n; done
sh negctl.sh > out/negctl/negctl.out
sh times.sh
```

## Result

| n | parts | graphs (A000944) | values of F equal | rooted maps | class | core time |
| --- | --- | --- | --- | --- | --- | --- |
| 12 | 1 | 6,384,634 | 13 of 13 | 637,446,145 | 606,838 | 2.7 s |
| 13 | 1 | 96,262,938 | 14 of 14 | 10,561,615,871 | 5,447,863 | 40.9 s |
| 14 | 4 | 1,496,225,352 | 16 of 16 | 178,683,815,937 | 49,661,857 | 616.5 s |
| 15 | 16 | 23,833,988,129 | 17 of 17 | 3,076,487,458,815 | 457,548,213 | 9,399.4 s |

For n = 4 to 11 every value is equal as well (`out/check_n<n>.out`). At n = 15 the 16 parts ran two at a time, from 543 to 672 s each (`out/times.txt`).
