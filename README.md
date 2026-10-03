<h1 align="center">The Tammes problem for fifteen points</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/tammes-15/releases/latest/download/tammes-15.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23058956"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23058956.svg"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/tammes-15/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Ftammes-15%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We prove that the largest possible minimal angular distance between fifteen points on the unit sphere is $`\arccos u\approx 53.65785^\circ`$, where $`u`$ is the root in $`(1/2,7/10)`$ of $`13u^5-u^4+6u^3+2u^2-3u-1`$. This value is attained by two configurations described by Buddenhagen and Kottwitz, whose contact graphs are not isomorphic, so the optimum is not unique. As Musin and Tarasov did for thirteen and fourteen points, a written reduction leads to plane graphs with at most fifteen vertices, and an interval computation rules out each of them except near the two known optima, where a local rigidity estimate concludes. The computation records its search trees as certificates, which are replayed. Lean 4 proves every step except the enumeration of the plane graphs and their refutation by the program, which enter the formal proof as hypotheses.

Corollary 1.2 of the paper answers in the negative, for $`N=15`$, Question 2 of Section 6 of Musin and Tarasov, *Extremal problems of circle packings on a sphere and irreducible contact graphs*, Proc. Steklov Inst. Math. 288 (2015), 117–131 ([doi:10.1134/S0081543815010095](https://doi.org/10.1134/S0081543815010095); [arXiv:1410.0744](https://arxiv.org/abs/1410.0744)): is the contact graph of a maximal configuration of $`N>5`$ points unique up to isomorphism?

```lean
theorem Tammes15.conjecture_of_enum_progTreesDom (L : Set Tammes15.PlaneGraph) (N : Tammes15.PaperSteps.Procs)
    (h2 : Tammes15.EnumComplete L) (h3 : Tammes15.Contractors.ProgTreesDom L N) (hN : Tammes15.Contractors.Impl N) :
    Tammes15.Conjecture

theorem Tammes15.nonunique_of_enum_progTreesDom (L : Set Tammes15.PlaneGraph) (N : Tammes15.PaperSteps.Procs)
    (h2 : Tammes15.EnumComplete L) (h3 : Tammes15.Contractors.ProgTreesDom L N) (hN : Tammes15.Contractors.Impl N) :
    ∃ d : ℝ, IsGreatest {d | Tammes15.Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (X i) (X j)) ∧
        (∀ i j, i ≠ j → d ≤ InnerProductGeometry.angle (Y i) (Y j)) ∧
        IsEmpty
          (Tammes15.Nonunique.contactGraph X (Real.cos d) ≃g Tammes15.Nonunique.contactGraph Y (Real.cos d))

theorem Tammes15.conjecture_of_enum_killed (L : Set Tammes15.PlaneGraph) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L {Tammes15.Attained.frameC1, Tammes15.Attained.frameC3}) :
    Tammes15.Conjecture
```

## What is checked

- **Lean 4**: `Tammes15.conjecture_of_enum_progTreesDom` (Theorem B.9) proves the value of $`d_{15}`$ and `Tammes15.nonunique_of_enum_progTreesDom` proves Corollary 1.2, from three hypotheses: D2 for a set of plane graphs (Definition 7.1); for each of its graphs and each choice of hexagons, a choice in the same faces such that each $`d`$ in $`[d_{lo}, d_{hi}]`$ lies in a range on which a family of interval procedures accepts a search tree for it from a box in the domain that contains the root box; and that these procedures are computed by the program in the sense of Definition B.1(5). `Tammes15.conjecture_of_enum_killed` and `Tammes15.nonunique_of_enum_killed` (Theorem B.8) prove the same from D2 and D3 (Definitions 7.1 and 7.3). Each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, with Mathlib. Comparator checks these four theorems, with eleven more, against the statements of `Tammes15/Challenge.lean`.
- **Computation**: D2 for the list given by plantri and an output filter, and the trees by the first level of the program and the replay of its certificates, both of which the CI reruns in full. The proof assumes that plantri, with the options of Computation 7.4, meets its description and that the filter keeps exactly the graphs of maximum degree at most 5, and that the program meets its model in the sense of Definition B.1(6) (Section 9.6 of the paper).

[`STATEMENTS.md`](STATEMENTS.md) states the main theorems with their hypotheses and maps each numbered statement of the paper to its Lean declarations, or to its scripts and their recorded outputs. [`code/README.md`](code/README.md) gives the script, recorded output and running time of each check, and says which checks the CI reruns.

The workflow `ci.yml` builds the Lean package, prints the axioms and runs Comparator in nanoda; it reruns the computations that fit a runner, replays every certificate in three parallel jobs, and compares each output with the recorded one. The badges give the results of the latest run by hand on `main` and link to that run. A release publishes the PDF, the outputs of every check of the green run by hand on the tagged commit, and the Lake build archive that Comparator checked.

## Layout

| Path | Content |
|---|---|
| `Tammes15/` | the Lean proof (Lean and Mathlib `v4.34.1`), one library per part; `Tammes15/Challenge.lean` holds the statements that Comparator checks, configured by `config.json` |
| `paper/` | the TeX source |
| `code/` | the program of the computation and the output filter of plantri, the PARI/GP and SageMath scripts, the generators of the Lean data, the checks of the Lean package, each with its recorded output |
| `data/` | the two optima, the parameters of the runs, the targets of Local |
| `STATEMENTS.md` | the statement map |
| `ASSETS.md` | the data tarballs of the release, with their sha256 sums |
| `THIRD_PARTY.md` | the vendored Lean code and every change made to it |

## Check and reuse

Fast check, in a clone at the tag, with the build of the release (times measured on the workstation of the paper, with other work running):

```sh
lake exe cache get          # Mathlib, from its cache: 234 s with an empty cache
lake build :release         # this package, from the release archive (113 MB): 3 s once downloaded
lake build --no-build       # nothing left to build: 5 s
rm -rf .lake/build/lib/lean/Tammes15/Challenge .lake/build/lib/lean/Tammes15/Challenge.* \
  .lake/build/ir/Tammes15/Challenge .lake/build/ir/Tammes15/Challenge.*
# then Comparator, as the job comparator of .github/workflows/ci.yml runs it: 281 s with nanoda
```

Comparator trusts the challenge module, which holds the statements: the `rm` line has it compiled again from its source in Comparator's sandbox.

Full check, from source: `lake exe cache get && code/lean/check.sh` (the build took 1446 s with `LEAN_NUM_THREADS=3`; output `code/lean/check.out`), then `code/lean/comparator.sh pass` (`code/README.md`). The record `code/lean/comparator.out` is a pass on the workstation of the paper, with nanoda alone, in 281 s.

As a dependency, in a package on Lean `v4.34.1` that requires Mathlib at `rev = "v4.34.1"`:

```toml
[[require]]
name = "tammes-15"
git = "https://github.com/mt0-svg/tammes-15"
rev = "v1.3.0"
```

then `lake update tammes-15`, `lake exe cache get` and `lake build`, which downloads the build archive of the release and compiles none of its modules: a file that imports `Tammes15.Solution` and prints the axioms of the fifteen theorems of `config.json` built in 74 s once Mathlib was in place.

The computations: `code/rerun.sh --list` prints the names of the checks, and `code/rerun.sh NAME ...` reruns them and compares each output with the recorded one; `code/README.md` gives the running time of each, and the commands of the replay of every certificate from the data tarballs (`code/impl1/fetch_assets.sh DIR` downloads them) and of the steps that the CI leaves out.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- The eight-point Lean development of Kryvonos, Liehr and Taylor ([arXiv:2609.22077](https://arxiv.org/abs/2609.22077)), [Energy-Minimization-8-Points](https://github.com/lukasliehr/Energy-Minimization-8-Points) at commit `50d14bc06bd41f61573eb6a36eedb8d00759af8f`, which carries no licence file: the 140 files of `Tammes15/Vendor/EM8/`, the modules that its `BestPacking.lean` imports, with the changes listed in `THIRD_PARTY.md`.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export), [landrun](https://github.com/zouuup/landrun) and [nanoda_lib](https://github.com/ammkrn/nanoda_lib): the check of the statement in CI.
- [plantri](https://users.cecs.anu.edu.au/~bdm/plantri/) 5.8 (Brinkmann and McKay, Apache 2.0): the enumeration of 3-connected plane graphs; `code/impl1/enum/build_plantri.sh` downloads it, checks its sha256 and compiles it with the output filter of this repository. Its guide, on which Proposition B.3 of the paper rests, is included unchanged as `code/impl1/enum/plantri-guide.txt`.
- [PARI/GP](https://pari.math.u-bordeaux.fr/) and [SageMath](https://github.com/sagemath/sage): the constants, the exact data of the two optima, the certificate data of the Lean proofs of D1 and D4.

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

Apache 2.0 (`LICENSE`, `NOTICE`) for the package. The files of `Tammes15/Vendor/EM8/` are the work of their authors, credited in `THIRD_PARTY.md` and `NOTICE`; `code/impl1/enum/plantri-guide.txt` is the guide of plantri 5.8, Copyright Brinkmann and McKay, Apache 2.0.
