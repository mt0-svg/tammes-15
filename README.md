<h1 align="center">The Tammes problem for fifteen points</h1>

<p align="center">
  <a href="https://zenodo.org/records/23101300/files/tammes-15.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23058956"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23058956.svg"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We prove that the largest possible minimal angular distance between fifteen points on the unit sphere is $`\arccos u\approx 53.65785^\circ`$, where $`u`$ is the root in $`(1/2,7/10)`$ of $`13u^5-u^4+6u^3+2u^2-3u-1`$. This value is attained by two configurations described by Buddenhagen and Kottwitz, whose contact graphs are not isomorphic, so the optimum is not unique. As Musin and Tarasov did for thirteen and fourteen points, a written reduction leads to plane graphs with at most fifteen vertices, and an interval computation rules out each of them except near the two known optima, where a local rigidity estimate concludes. The computation records certificates, and a second program written independently confirms it. Lean 4 proves every step except the enumeration of the plane graphs and their refutation by the program, which enter the formal proof as hypotheses.

Corollary 1.2 of the paper answers in the negative, for $`N=15`$, Question 2 of Section 6 of Musin and Tarasov, *Extremal problems of circle packings on a sphere and irreducible contact graphs*, Proc. Steklov Inst. Math. 288 (2015), 117–131 ([doi:10.1134/S0081543815010095](https://doi.org/10.1134/S0081543815010095)), numbered as in its Russian version [arXiv:1410.0744](https://arxiv.org/abs/1410.0744): is the contact graph of a maximal configuration of $`N>5`$ points unique up to isomorphism?

## What is checked

- **Lean 4**: `Tammes15.conjecture_of_enum_progTreesDom` (Theorem B.9) proves the value of $`d_{15}`$ and `Tammes15.nonunique_of_enum_progTreesDom` proves Corollary 1.2, from three hypotheses: D2 (Definition 7.1), the trees that the replays of the first program accept, and interval procedures computed by the program in the sense of Definition B.1. `Tammes15.conjecture_of_enum_killed` and `Tammes15.nonunique_of_enum_killed` (Theorem B.8) prove the same from D2 and D3 (Definitions 7.1 and 7.3). Each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, with Mathlib. Comparator checks these four theorems, with eleven more, against the statements of `Tammes15/Challenge.lean`.
- **Computation**: D2 and the trees are checked by programs that are not verified in Lean: D2 by plantri, which is checked against the counts of its authors, against the formula of Mullin and Schellenberg for its weighted counts, and against a second enumerator on the graphs a gap could hide; the trees by the first level of the first program and the replay of its certificates, both of which the CI reruns in full. A second program, written separately, refutes all 462,703 graphs left by the filter with relations outside D3 and without certificates: it checks the theorem again, and D3 as stated has the first program as its only check.
- **Outside Lean**: Section 9.7 of the paper lists the four statements about the programs that stay outside the formal proof: D2 read from the description of plantri, the soundness of the arithmetic of the first program, the agreement of its narrowings with the primitive steps of the formalization, and the acceptance of the trees by its first level and its replay. A differential test of the formal primitive steps against the program on 3,000,000 inputs tests the third, and an exact check of the 80 million basic operations that it recorded tests the second, with a high-precision check, not a proof, of its 44,854,205 calls of the elementary functions.

[`STATEMENTS.md`](STATEMENTS.md) states the main theorems with their hypotheses and maps each numbered statement of the paper to its Lean declarations, or to its scripts and their recorded outputs. [`code/README.md`](code/README.md) gives the script, recorded output and running time of each check, and says which checks the CI reruns.

The workflow `ci.yml` builds the Lean package, prints the axioms and runs Comparator in nanoda, with seven controls that must fail; it reruns the computations that fit a runner, replays every certificate in three parallel jobs, and compares each output with the recorded one. The badges give the results of the latest run by hand on `main` and link to that run. A release publishes the PDF, the outputs of every check of the green run by hand on the tagged commit, and the Lake build archive that Comparator checked.

## Layout

| Path | Content |
|---|---|
| `Tammes15/` | the Lean proof (Lean and Mathlib `v4.34.1`), one library per part; `Tammes15/Challenge.lean` holds the statements that Comparator checks, configured by `config.json` |
| `paper/` | the TeX source |
| `code/` | the two programs of the computation, the PARI/GP and SageMath checks, the checks of the Lean package, each with its recorded output |
| `data/` | the two optima, the parameters of the runs, the targets of Local, the inputs of the hardest cases |
| `STATEMENTS.md` | the statement map |
| `ASSETS.md` | the data tarballs of the release, with their sha256 sums |
| `THIRD_PARTY.md` | the vendored Lean code and every change made to it |

## Check and reuse

Fast check, in a clone at the tag, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -rf .lake/build/lib/lean/Tammes15/Challenge .lake/build/lib/lean/Tammes15/Challenge.* \
  .lake/build/ir/Tammes15/Challenge .lake/build/ir/Tammes15/Challenge.*
# then Comparator, as the job comparator of .github/workflows/ci.yml runs it
```

Comparator trusts the challenge module, which holds the statements: the `rm` line has it compiled again from its source in Comparator's sandbox.

Full check, from source: `lake exe cache get && code/lean/check.sh` (the build took 1360 s with `LEAN_NUM_THREADS=3`; output `code/lean/check.out`), then `code/lean/comparator.sh pass` and its seven controls (`code/README.md`). The record `code/lean/comparator.out` is a pass on the workstation of the paper, with nanoda alone, in 250 s.

As a dependency, in a package on Lean `v4.34.1` that requires Mathlib at `rev = "v4.34.1"`:

```toml
[[require]]
name = "tammes-15"
git = "https://github.com/mt0-svg/tammes-15"
rev = "v1.2.0"
```

then `lake update tammes-15`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The computations: `code/rerun.sh --list` prints the names of the checks, and `code/rerun.sh NAME ...` reruns them and compares each output with the recorded one. `code/README.md` gives the commands of the checks that the CI leaves out, among them the replay of every certificate from the data tarballs (`code/impl1/fetch_assets.sh DIR` downloads them).

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- The eight-point Lean development of Kryvonos, Liehr and Taylor ([arXiv:2609.22077](https://arxiv.org/abs/2609.22077)), [Energy-Minimization-8-Points](https://github.com/lukasliehr/Energy-Minimization-8-Points) at commit `50d14bc06bd41f61573eb6a36eedb8d00759af8f`, which carries no licence file: the 140 files of `Tammes15/Vendor/EM8/`, the modules that its `BestPacking.lean` imports, with the changes listed in `THIRD_PARTY.md`.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export), [landrun](https://github.com/zouuup/landrun) and [nanoda_lib](https://github.com/ammkrn/nanoda_lib): the check of the statement in CI.
- [plantri](https://users.cecs.anu.edu.au/~bdm/plantri/) 5.8 (Brinkmann and McKay, Apache 2.0): the enumeration of 3-connected plane graphs; `code/impl1/enum/build_plantri.sh` and `code/plantri-ms-check/build.sh` download it, check its sha256 and compile it with an output plugin of this repository. Its guide, on which Proposition B.3 of the paper rests, is included unchanged as `code/impl1/enum/plantri-guide.txt`.
- [PARI/GP](https://pari.math.u-bordeaux.fr/) and [SageMath](https://github.com/sagemath/sage), with [GLPK](https://www.gnu.org/software/glpk/): the constants, the exact data of the two optima, the certificate data of the Lean proofs of D1 and D4, and an exact check of the first level.
- The b-file of [OEIS A290326](https://oeis.org/A290326) (CC BY-SA 4.0), rows 1 to 30 in `code/plantri-ms-check/ref/`: known-answer tests of the formula of Mullin and Schellenberg.
- [MPFR](https://www.mpfr.org/): the tables of the second program and the reference tests of the elementary functions.

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

Apache 2.0 (`LICENSE`, `NOTICE`) for the package. The files of `Tammes15/Vendor/EM8/` are the work of their authors, credited in `THIRD_PARTY.md` and `NOTICE`; `code/impl1/enum/plantri-guide.txt` is the guide of plantri 5.8, Copyright Brinkmann and McKay, Apache 2.0; `code/plantri-ms-check/ref/b290326_rows1-30.txt` is an excerpt of the OEIS, CC BY-SA 4.0.
