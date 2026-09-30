<h1 align="center">The Tammes problem for fifteen points</h1>

<p align="center">
  <a href="https://zenodo.org/records/23058957/files/tammes-15.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23058956"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23058956.svg"></a>
  <a href="https://github.com/mt0-svg/tammes-15/actions/workflows/ci.yml"><img alt="CI" src="https://github.com/mt0-svg/tammes-15/actions/workflows/ci.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

The largest possible minimal angular distance between fifteen points on the unit sphere is $`\arccos u \approx 53.6578501^\circ`$, where $`u`$ is the root in $`(1/2, 7/10)`$ of

```math
13u^5 - u^4 + 6u^3 + 2u^2 - 3u - 1.
```

This value is attained by two configurations described by Buddenhagen and Kottwitz, and their contact graphs are not isomorphic, so the optimal arrangement of fifteen points is not unique. The proof follows the method of Musin and Tarasov for thirteen and fourteen points: a written reduction to plane graphs with at most fifteen vertices, enumerated by plantri, and an interval computation that refutes each graph except near the two optima, where a local rigidity estimate concludes.

```lean
theorem Tammes15.reduction (L : Set Tammes15.PlaneGraph) (F : Set Tammes15.Frame)
    (h0 : Tammes15.FejesTothBound) (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L F) (h4 : Tammes15.AttainedHyp F) : Tammes15.Conjecture
```

`Tammes15.Conjecture` (`Tammes15/Statement.lean`, Mathlib definitions only) says that $`\arccos u`$ is the greatest $`d`$ such that some fifteen points of the unit sphere are pairwise at angular distance at least $`d`$.

## What is checked

- **Lean 4**: `Tammes15.reduction` proves `Tammes15.Conjecture`, the value of $`d_{15}`$ (not the naming of the two optima), with Mathlib and only the axioms `propext`, `Classical.choice` and `Quot.sound`, from five named hypotheses (`Tammes15/Hyps/Computations.lean`): the finite statements D1 to D4 (`KappaHyp`, the rigidity bound of the two optima; `EnumComplete`, the completeness of the list of plane graphs; `Killed`, the refutation of every graph of the list; `AttainedHyp`, the attainment) and the bound $`d_{15} \le 56.6716^\circ`$ of Fejes Tóth (`FejesTothBound`), taken from the literature and not proved in Lean. The proof contains the structure theorem of the paper, and its local optimality theorem without the equality case, from D1. `code/lean/check.sh` builds the package from source and checks the axioms, the sources and every constant (output `code/lean/check.out`); the CI also runs Comparator, which checks the theorem against the statement of `Tammes15/Challenge.lean`, written again over copies of the definition modules, in the Lean kernel and in nanoda.
- **Computation**: D1 to D4 are checked by computation; the programs are not verified in Lean. D1, the rigidity bound, and D4, the attainment, in exact and ball arithmetic in SageMath, each repeated in PARI/GP. D2 by plantri alone, with consistency checks. D3 by the linear filter and the interval search of the first program, whose certificates (search trees) the repository replays. To guard against a bug in the search, a second program, written separately, with relations that are not fields of the relation system of D3 and without certificates, reaches the same conclusion on all 462,703 graphs left by the filter; it is a second computation of the theorem, not a check of D3. `code/README.md` maps each computational claim of the paper to its script and recorded output.
- **On paper**: that the verdicts of the first program give D3 (the soundness of the first level and of the search), the step from the output of plantri to D2 by Whitney's theorem, the equality case of the local optimality theorem, and the non-isomorphism of the two contact graphs.

The workflow `ci.yml` runs on GitHub's runners at each push that touches the Lean package, the code or the data. It runs `code/lean/check.sh` (the build of the package, compiling only what changed since the last build, restored from the cache or from the latest release; every target up to date; a scan of the sources for the constructs that can bypass the kernel; `#print axioms` of the theorems of `code/lean/axioms.lean`, `Tammes15.reduction` among them; the types of the interfaces; an audit of every constant of the package), a scan for `sorry`, `admit` and `native_decide`, and Comparator with the Lean kernel and nanoda. It reruns the computations of `code/README.md` marked CI and compares each output with the recorded one: the enumeration and the first level of both programs on every part, the replay of a sample of certificates, the second program on a sample, on the graphs left by its bulk passes and on the realised subgraphs of the two optima, and the SageMath and PARI/GP checks; when a release holds the data tarballs of `ASSETS.md`, it also runs the checks that read them. On a tag, `release.yml` takes the green `ci.yml` run of the tagged commit and attaches the PDF, the outputs of its checks and the build that Comparator checked to the release; it compiles nothing but the PDF.

## Layout

| Path             | Content                                                                                                                                                                                                                                                                                                                                                                                  |
| ---------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Tammes15/`      | the Lean proof (Lean and Mathlib `v4.34.1`), one library per part (`lakefile.toml`): `Statement.lean`, the statement; `Hyps/`, the five hypotheses, the interfaces and `Reduction.lean`, the main theorem; `Vendor/EM8/`, the eight-point development of Kryvonos, Liehr and Taylor; `Challenge.lean` with `Challenge/`, the statement with `sorry`, and `Solution.lean`, for Comparator |
| `config.json`    | the Comparator configuration                                                                                                                                                                                                                                                                                                                                                             |
| `paper/`         | the TeX source                                                                                                                                                                                                                                                                                                                                                                           |
| `code/`          | the two programs of the computation, the PARI/GP and SageMath checks, the checks of the Lean package and of the vendored code, each with its recorded output; `code/README.md` maps each claim of the paper to its check                                                                                                                                                                 |
| `data/`          | coordinates of the two optima and the exact frame, the parameters of the runs, the targets of Local, the survivors of the first level, the inputs of the hardest cases, the realised subgraphs of the optima, the replay sample with its trees                                                                                                                                           |
| `ASSETS.md`      | the data tarballs of the release (inputs, certificates, run records) with their sha256 sums                                                                                                                                                                                                                                                                                              |
| `THIRD_PARTY.md` | the vendored Lean code, its source and every change made to it                                                                                                                                                                                                                                                                                                                           |

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

Full check, from source (the build took 623 s with `LEAN_NUM_THREADS=3`, `code/lean/check.out`):

```sh
lake exe cache get && code/lean/check.sh
```

Comparator on that build, with the tools of the job `comparator` of `ci.yml` (paths in `COMPARATOR`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA`): `code/lean/comparator.sh pass`, and the control `code/lean/comparator.sh fejestoth`, which must fail (`code/lean/comparator.out`, `code/lean/comparator-fejestoth.out`: PASS in 173 s, and FAIL as expected).

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "tammes-15"
git = "https://github.com/mt0-svg/tammes-15"
rev = "v1.0.0"
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
