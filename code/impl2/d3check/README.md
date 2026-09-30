# d3check: can the second program check the Lean hypothesis D3 as stated?

D3 is `Killed L F` of Tammes15/Hyps/Computations.lean: for every graph of the list, every choice of k hexagons and every assignment with d in [dlo, dhi] that satisfies the relation system `RelSys` (Tammes15/Hyps/Case.lean), some valid gluing fires Pair or Local. A program checks D3 as stated only if every relation it uses is a field of `RelSys` or follows from one by an identity, and its only tests on a glued configuration are Pair and Local.

Line numbers are those of the sources in code/impl2. The scripts read their inputs, and the recorded runs they compare with, from the data directory `$T15` of the development (the paths are in the scripts); these runs are not repeated by the continuous integration.

## 1. Relations of the second program against `RelSys`

vlevel1 (src/level1.rs, stage A):

| row                                                                                        | where       | status                                                                 |
| ------------------------------------------------------------------------------------------ | ----------- | ---------------------------------------------------------------------- |
| a in [alpha(dlo), alpha(dhi)], triangle corners = a                                        | l.44        | `tri` with `alpha` increasing (row (1), `alpha_strictMonoOn`)          |
| rhombus x, y in [a, 2a], x + y >= 3a, x + y \<= S(dhi)                                     | l.61 to 72  | `rhombus` with `corner_mem` (row (2), `rhombus_rows` of Trigrows)      |
| pentagon and hexagon corners in [a, pi]                                                    | l.78, 80    | `corner_mem` (row (3))                                                 |
| vertex sums = 2 pi                                                                         | l.92 to 106 | `vertex_sum` (row (4))                                                 |
| **Girard rows**: corners of a pentagon sum to at least 3 pi, of a hexagon to at least 4 pi | l.83 to 86  | **outside `RelSys`**; on by default, off with `--noarea` or `--relsys` |

vkill (src/model.rs builds the system, src/faces.rs evaluates each family):

| relation                                                                                                                          | model.rs                    | faces.rs     | status                                                                                                      |
| --------------------------------------------------------------------------------------------------------------------------------- | --------------------------- | ------------ | ----------------------------------------------------------------------------------------------------------- |
| domains: d in [dlo, dhi], corners in [alpha(dlo), pi], rhombus in [alpha(dlo), 2 alpha(dhi)], r in [dlo, 3 dhi], theta in [0, pi] | l.69, 74, 91, 103, 213, 221 |              | implied (the program allows the corner pi, `RelSys` asks for less than pi: weaker)                          |
| Alpha a = alpha(d), AlphaInv d = acos(cos a / (1 - cos a))                                                                        | l.113, 114                  | l.129 to 138 | `tri` and the definition of `alpha` (T3, `alpha_inverse`)                                                   |
| vertex sums                                                                                                                       | l.116 to 128                |              | `vertex_sum`                                                                                                |
| RhoY y = rho_d(x) and x = rho_d(y), RhoD d = acos(cot(x/2) cot(y/2))                                                              | l.137 to 139                | l.139 to 150 | `rhombus` (T4: `rho_rho`, `cot_mul_cot_rho`, corners below pi)                                              |
| rhombus rows                                                                                                                      | l.141 to 147                |              | row (2), `rhombus_rows`                                                                                     |
| corner >= a (pentagon, hexagon)                                                                                                   | l.151, 170                  |              | `corner_mem`                                                                                                |
| **PentSplit** (5 per pentagon)                                                                                                    | l.154 to 159                | l.151 to 162 | **outside `RelSys`**                                                                                        |
| PentFan (5 per pentagon)                                                                                                          | l.160 to 165                | l.163 to 171 | `pent` at every dart (T5): the same three equations and the same three arc cosines                          |
| HexAlt (2 parities)                                                                                                               | l.173 to 178                | l.172 to 181 | `hex` at every dart (T6): a rotation by 2 gives the same equations                                          |
| **HexChain5** (6 per hexagon)                                                                                                     | l.181 to 186                | l.182 to 194 | **outside `RelSys`**                                                                                        |
| **HexC4Iso** (12 per hexagon)                                                                                                     | l.188 to 193                | l.195 to 209 | **outside `RelSys`**                                                                                        |
| HexLong (12 per hexagon), u\_\{i+2s} >= L(u\_\{i+s})                                                                              | l.195 to 200                | l.210 to 216 | `hexDiag` at every dart (T7, `longDiag`)                                                                    |
| wheel rows d \<= r_i \<= 3d                                                                                                       | l.229, 230                  |              | `wheel` (T8)                                                                                                |
| WCorner u_i = gam(r\_\{i+1}; r_i, d) + gam(r\_\{i-1}; r_i, d)                                                                     | l.231                       | l.217 to 225 | `wheel`                                                                                                     |
| WTheta theta_i = gam(d; r_i, r\_\{i+1}), sum theta_i = 2 pi                                                                       | l.232, 237                  | l.226 to 232 | `wheel`                                                                                                     |
| WBack r\_\{i+1} from d, r\_\{i-1}, r_i, u_i                                                                                       | l.233, 234                  | l.233 to 242 | `wheel` with the law of cosines (T9): cos of gam is eta once eta is in [-1, 1], and r\_\{i+1} is in (0, pi) |

The three families hold for a convex equilateral polygon, but they follow from `pent`, `hex` and `hexDiag` only through a realisability lemma of the face (a solution of the `RelSys` relations of a face is the corner tuple of a convex polygon), which is stated nowhere. They are listed in `OUTSIDE_RELSYS` (src/model.rs).

Tests on a glued configuration (src/glue.rs):

| test                                                                        | where                    | status                                                                                                                                                                           |
| --------------------------------------------------------------------------- | ------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Pair: a non-edge with sup of the chord below 2 sin(d_lo / 2)                | l.304 to 313             | `PairFires`                                                                                                                                                                      |
| Local: injective matching of the 15 points into a target within 1.04e-3     | l.335 to 339, 343 to 369 | `LocalFires`                                                                                                                                                                     |
| **Edge**: an edge or a wheel radius whose chord enclosure misses 2 sin(d/2) | l.314 to 333             | **not a test of D3**; off by default, on in every recorded run (run_l2.sh, run_cases.sh, run_samples.sh, vbulk/pass2.sh pass `--edge`); it fired in none of them (edge_count.sh) |

The rest of the search (mean value forms, monotonicity, Newton steps, 3B shaving, `--lp`) are contractions of the same relations; with fewer relations they contract less, never more.

## 2. Flags

- `vlevel1 --relsys`, the same as the existing `--noarea`: no Girard rows; the summary line ends with `rows relsys`.
- `vkill --relsys`: drops the three families (`Model::restrict_to_relsys`, which asserts that none is left), refuses `--edge`, and prints `relsys: families [PentSplit, HexChain5, HexC4Iso] dropped, Edge off` on stderr.
- `vtest --relsys`: the same model, Edge off.

Without the flag every binary behaves as before (section 4 checks it).

## 3. Binaries and known-answer tests

- build.sh, build.out: vkill, vlevel1, vtest built twice from the sources of code/impl2 (two directories, two target dirs; the sha256 of the sources is the first line of build.out): equal sha256 (vkill a518bbb9af0f183f, vlevel1 080b6d6dbca7a878, vtest 3130163e74819a0a). Every run below uses these binaries (`$T15/verify/bin_d3`).
- Unit test `model::tests::relsys_drops_exactly_the_three_families` (prisms over a pentagon and a hexagon, with and without a free point): `restrict_to_relsys` removes the 10 PentSplit, 12 HexChain5 and 24 HexC4Iso relations and leaves every other count unchanged.
- vtest_relsys.sh, vtest_relsys.out (outputs in out/vtest/): with `--relsys`, on the 84 + 146 realised subgraphs of C1 and the 80 + 144 of C3 the boxes around the true values are neither refuted nor lose the truth and Local fires on every truth box (failures 0, the same lines as the recorded default run); the search without Local over [dlo, dhi] (300 nodes) on the 37 + 37 realised subgraphs with at most two contacts deleted ends BUDGET or UNRESOLVED, never KILLED: the relsys pipeline keeps the known solutions. The FAIL path of vtest is not exercised by a planted error here.

## 4. Default behaviour unchanged

- stageA_probe.out: on 12 sampled parts the default vlevel1 survivors are byte-identical to the recorded independent stage A (`$T15/stageA2`), including parts 1, 127 and 1023 where the Girard rows kill graphs.
- compare_pass1.out: the default vkill rerun on the pass-1 samples repeats the recorded bulk pass 1 line for line (verdict, cases, nodes, face counts, per-case counters) except where the 5 s wall clock limit decided: 46 of 1417 lines differ, each with BUDGET on one side (the machine was loaded, load 40 to 48 on 24 cores). A planted change of one node count is found in each class (negative control). det_check.out: the 5 of those graphs that the recorded run KILLED, rerun with the node budget alone, give lines equal to the recorded ones.

## 5. Timed probe (relsys)

All runs with a memory limit of 3 GB and two processors, 2026-09-30 between 03:15 and 04:20, machine load 40 to 48 on 24 cores; seconds are user CPU or the per-graph wall times vkill prints.

Stage A (stageA_probe.out): on 12 parts (k = 0 parts 0, 1, 127, 500, 1000, 1023, 1500, 1999 of 2000; k = 1 parts 0, 20 of 40; k = 2 and k = 3 whole, 10,437,407 graphs) `vlevel1 --relsys` keeps exactly the first program's stage-A survivors (byte-identical to `$T15/n15full/k<k>_<r>.pc`; 3,638 survivors). In particular the graphs the Girard rows kill are kept, as by tfilter. One run of the default vlevel1 on the k = 2 part panicked on a corrupted planar code and passed on the rerun.

vkill pass 1 (compare_pass1.out; options of the recorded bulk pass 1, `--nodes 30000 --maxsec 5`), relsys and default side by side on stride samples of the first program's stage-A survivors:

| sample                        | graphs | default KILLED | relsys KILLED | killed by default, not by relsys | seconds default, relsys |
| ----------------------------- | ------ | -------------- | ------------- | -------------------------------- | ----------------------- |
| k = 0, every 145th of in_k0_0 | 1001   | 999            | 1001          | none                             | 22.1, 14.4              |
| k = 1, every 10th of in9_k1_0 | 300    | 290            | 294           | none                             | 105.2, 79.9             |
| k = 2, every 4th of stageA_k2 | 111    | 82             | 83            | none                             | 193.6, 178.0            |
| k = 3, all                    | 5      | 0              | 0             | none                             | 25.0, 25.0              |

Without the three families a node is cheaper, so relsys explores more nodes in the same time (k = 0: 10,097 against 8,126 nodes) and kills a few graphs the default leaves at the time limit.

vkill pass 2 (compare_pass2.out; options of the recorded pass 2, `--shave 8 --incr --maxsec 60 --nodes 1000000`) on the 39 sampled graphs relsys left: 35 KILLED, 4 BUDGET (k = 1 #360, k = 2 #72, k = 3 #0, #2 of stageA_k3), and the recorded pass 2 of the default mode left the same four; relsys kills k = 2 #248, #404 and k = 3 #1, #4, which the recorded pass 2 left.

Hard cases (hard_compare.out; `--shave 8 --incr` with a time limit, the options of the recorded killing pass without Edge and without the families): all 11 KILLED, in 3.3 s to 564 s per case (k3 #0 in 299.4 s of its 300 s limit; k1 #1 in 2801 nodes and 564 s, where the recorded run needed 2135 nodes and 621 s with every family and stayed BUDGET at 600 s with HexC4Iso and HexChain5 dropped), with node counts close to the recorded ones.

## 6. Extrapolation and decision

extrapolate.out (heuristic, from the samples): stage A about 14,700 core s (plantri alone is 9,192 s of recorded CPU), pass 1 about 11,400, pass 2 about 13,200, the per-case residue at least 8,600 (the 42 recorded residue graphs took 7,865 s in their killing passes; the attempts that failed are not counted, and the slices of k1 #68 near psi\* with relsys were not probed): about 48,000 core s, 13.3 core hours, 6.7 hours at 2 cores. That is far over the 30 minutes of the brief, so the full run was not started; it is a solver decision. No sampled graph or case survived the relsys check in the end. Of the 4 graphs the pass-2 probe left at BUDGET (the recorded default pass 2 left the same four), two are hard cases the relsys probe killed (k = 1 #360 of in9_k1_0 is k1 #1 of b_k1, stageA_k3 #0 is k3 #0); k = 2 #72 (k2 #3 of b_k2) and stageA_k3 #2 were not run per case with relsys.
