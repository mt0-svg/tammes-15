<h1 align="center">The Tammes problem for fifteen points</h1>

<p align="center">
  <a href="https://zenodo.org/records/23063365/files/tammes-15.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23058956"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23058956.svg"></a>
  <a href="https://github.com/mt0-svg/tammes-15/actions/workflows/ci.yml"><img alt="CI" src="https://github.com/mt0-svg/tammes-15/actions/workflows/ci.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We prove that the largest possible minimal angular distance between fifteen points on the unit sphere is $`\arccos u\approx 53.6578501^\circ`$, where $`u`$ is the root in $`(1/2,7/10)`$ of $`13u^5-u^4+6u^3+2u^2-3u-1`$. This value is attained by two configurations described by Buddenhagen and Kottwitz, and their contact graphs are not isomorphic, so the optimal arrangement of fifteen points is not unique. The proof follows the method Musin and Tarasov used for thirteen and fourteen points: a written reduction to plane graphs with at most fifteen vertices, and an interval computation that rules out each such graph except near the two known optima, where a local rigidity estimate concludes. The computation records certificates, and a second program written independently confirms it. The written reduction is formalized in Lean 4, together with the slightly weaker form of the upper bound of Fejes Tóth that it uses; the four finite computations it rests on enter the formal proof as named hypotheses.

Corollary 1.2 of the paper answers in the negative, for $`N=15`$, Question 2 of Section 6 of Musin and Tarasov, *Extremal problems of circle packings on a sphere and irreducible contact graphs*, Proc. Steklov Inst. Math. 288 (2015), 117–131 ([doi:10.1134/S0081543815010095](https://doi.org/10.1134/S0081543815010095)), numbered as in its Russian version [arXiv:1410.0744](https://arxiv.org/abs/1410.0744): is the contact graph of a maximal configuration of $`N>5`$ points unique up to isomorphism?

```lean
theorem Tammes15.reduction (L : Set Tammes15.PlaneGraph) (F : Set Tammes15.Frame)
    (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L F) (h4 : Tammes15.AttainedHyp F) : Tammes15.Conjecture

theorem Tammes15.fejesToth_bound : Tammes15.FejesTothBound
```

`Tammes15.Conjecture` (`Tammes15/Statement.lean`, Mathlib definitions only) says that $`\arccos u`$ is the greatest $`d`$ such that some fifteen points of the unit sphere are pairwise at angular distance at least $`d`$. `Tammes15.FejesTothBound` (`Tammes15/Hyps/Computations.lean`) says that if fifteen points of the unit sphere are pairwise at angular distance at least $`d`$, then $`d \le 56.6716^\circ`$.

## What is checked

- **Lean 4**: `Tammes15.reduction` proves `Tammes15.Conjecture`, the value of $`d_{15}`$ without the names of the two optima, with Mathlib and only the axioms `propext`, `Classical.choice` and `Quot.sound`, from four named hypotheses (`Tammes15/Hyps/Computations.lean`), the finite statements D1 to D4 (`KappaHyp`, the rigidity bound of the two optima; `EnumComplete`, the completeness of the list of plane graphs; `Killed`, the refutation of every graph of the list; `AttainedHyp`, the attainment). The proof contains the structure theorem of the paper, its local optimality theorem without the equality case, from D1, and the bound $`d_{15} \le 56.6716^\circ`$ (`Tammes15.fejesToth_bound`, slightly weaker than that of Fejes Tóth), with no hypothesis (`Tammes15/FejesToth/`, by a triangle lemma on the convex hull of a saturated set). `code/lean/check.sh` builds the package from source and checks the axioms, the sources and every constant (output `code/lean/check.out`); the CI also runs Comparator, which checks the two theorems against their statements in `Tammes15/Challenge.lean`, written again over copies of the definition modules, in the Lean kernel and in nanoda.
- **Computation**: D1 to D4 are checked by computation; the programs are not verified in Lean. D1, the rigidity bound, and D4, the attainment, in exact and ball arithmetic in SageMath, each repeated in PARI/GP. D2 by plantri alone, with consistency checks. D3 by the linear filter and the interval search of the first program, whose certificates (search trees) the repository replays. To guard against a bug in the search, a second program, written separately, with relations that are not fields of the relation system of D3 and without certificates, reaches the same conclusion on all 462,703 graphs left by the filter. It is thus a second computation of the theorem, and D3 as stated has the first program as its only check. `code/README.md` maps each computational claim of the paper to its script and recorded output.
- **On paper**: the steps of Section 8.2 of the paper by which the outputs of the programs give D2 and D3: the step from the output of plantri to D2, by Whitney's theorem; the soundness of the search (Proposition 5.3) and of the first level; the reflection between the gluing of the program and `glueY`; the relabelling from the choices of hexagons of the program to every `HexChoice`; and the containment of the points of the eight frame configurations in the 960 target balls. Also the equality case of the local optimality theorem, and the non-isomorphism of the two contact graphs.

The workflow `ci.yml` runs on GitHub's runners at each push that touches the Lean package, the code or the data, and when started by hand. Its first job reads the files of the pushed commits: the Lean jobs run when they touch a Lean source, the Lake files, `config.json` or `code/lean/`, the computation jobs when they touch `code/` outside `code/lean/`, `data/` or `ASSETS.md`; a change of `ci.yml`, a new branch, a pull request and a run by hand run every job. The Lean jobs run `code/lean/check.sh` (the build of the package, compiling only what changed since the last build, restored from the cache or from the latest release; every target up to date; a scan of the sources for the constructs that can bypass the kernel; `#print axioms` of the theorems of `code/lean/axioms.lean`, `Tammes15.reduction` among them; the types of the interfaces; an audit of every constant of the package), a scan for `sorry`, `admit` and `native_decide`, and Comparator with the Lean kernel and nanoda. The computation jobs rerun the computations of `code/README.md` marked CI and compare each output with the recorded one: the enumeration and the first level of both programs on every part, the replay of a sample of certificates, the second program on a sample, on the graphs left by its bulk passes and on the realised subgraphs of the two optima, and the SageMath and PARI/GP checks; when a release holds the data tarballs of `ASSETS.md`, it also runs the checks that read them. On a tag, `release.yml` takes the green `ci.yml` run started by hand on the tagged commit and attaches the PDF, the outputs of its checks and the build that Comparator checked to the release; it compiles nothing but the PDF.

## Layout

| Path             | Content                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| ---------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Tammes15/`      | the Lean proof (Lean and Mathlib `v4.34.1`), one library per part (`lakefile.toml`): `Statement.lean`, the statement; `Hyps/`, the four hypotheses, the interfaces and `Reduction.lean`, the main theorem; `FejesToth/`, the weaker form of the bound of Fejes Tóth; `Vendor/EM8/`, the eight-point development of Kryvonos, Liehr and Taylor; `Challenge.lean` with `Challenge/`, the statements with `sorry`, and `Solution.lean`, for Comparator |
| `config.json`    | the Comparator configuration                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `paper/`         | the TeX source                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `code/`          | the two programs of the computation, the PARI/GP and SageMath checks, the checks of the Lean package and of the vendored code, each with its recorded output; `code/README.md` maps each claim of the paper to its check                                                                                                                                                                                                                            |
| `data/`          | coordinates of the two optima and the exact frame, the parameters of the runs, the targets of Local, the survivors of the first level, the inputs of the hardest cases, the realised subgraphs of the optima, the replay sample with its trees                                                                                                                                                                                                      |
| `ASSETS.md`      | the data tarballs of the release (inputs, certificates, run records) with their sha256 sums                                                                                                                                                                                                                                                                                                                                                         |
| `THIRD_PARTY.md` | the vendored Lean code, its source and every change made to it                                                                                                                                                                                                                                                                                                                                                                                      |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -rf .lake/build/lib/lean/Tammes15/Challenge .lake/build/lib/lean/Tammes15/Challenge.* \
  .lake/build/ir/Tammes15/Challenge .lake/build/ir/Tammes15/Challenge.*
# then Comparator, as .github/workflows/ci.yml runs it
```

Full check, from source (the build took 648 s with `LEAN_NUM_THREADS=3`, `code/lean/check.out`):

```sh
lake exe cache get && code/lean/check.sh
```

Comparator on that build, with the tools of the job `comparator` of `ci.yml` (paths in `COMPARATOR`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA`): `code/lean/comparator.sh pass`, and the controls `code/lean/comparator.sh fejestoth` and `code/lean/comparator.sh oldstatement`, which must fail (`code/lean/comparator.out`, `code/lean/comparator-fejestoth.out`, `code/lean/comparator-oldstatement.out`: PASS in 177 s, and FAIL as expected).

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "tammes-15"
git = "https://github.com/mt0-svg/tammes-15"
rev = "v1.1.0"
```

then `lake update tammes-15`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The computations: `code/rerun.sh --list` prints the names of the checks, and `code/rerun.sh NAME ...` reruns them and compares each output with the recorded one. `code/README.md` gives the script, recorded output and running time of each check, and the commands of those that CI leaves out, among them the replay of every certificate from the data tarballs (`code/impl1/fetch_assets.sh DIR` downloads them).

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- The eight-point Lean development of Kryvonos, Liehr and Taylor ([arXiv:2609.22077](https://arxiv.org/abs/2609.22077)), [Energy-Minimization-8-Points](https://github.com/lukasliehr/Energy-Minimization-8-Points) at commit `50d14bc06bd41f61573eb6a36eedb8d00759af8f`, which carries no licence file: the 140 files of `Tammes15/Vendor/EM8/`, the modules that its `BestPacking.lean` imports, with the changes listed in `THIRD_PARTY.md`.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export), [landrun](https://github.com/zouuup/landrun) and [nanoda_lib](https://github.com/ammkrn/nanoda_lib): the check of the statement in CI.
- [plantri](https://users.cecs.anu.edu.au/~bdm/plantri/) 5.8 (Brinkmann and McKay, Apache 2.0): the enumeration of 3-connected plane graphs; not included, `code/impl1/enum/build_plantri.sh` downloads it and checks its sha256.
- [PARI/GP](https://pari.math.u-bordeaux.fr/) and [SageMath](https://github.com/sagemath/sage), with [GLPK](https://www.gnu.org/software/glpk/): the attainment, the constants, the rigidity bound and an exact check of the first level.
- [MPFR](https://www.mpfr.org/): the tables of the second program and the reference tests of the elementary functions.
- The 15-point packing of the tables of [Hardin, Sloane and Smith](http://neilsloane.com/packings/dim3/) (`data/pack.3.15.txt`): a cross-check of the two optima in `code/gp/tie_targets_check.gp`.

## Citation

```bibtex
@misc{tammes-15,
  title     = {The {T}ammes problem for fifteen points},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23058956},
  url       = {https://doi.org/10.5281/zenodo.23058956}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/tammes-15/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`) for the package. The files of `Tammes15/Vendor/EM8/` are the work of their authors, credited in `THIRD_PARTY.md` and `NOTICE`.
