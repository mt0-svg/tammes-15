import Tammes15.Challenge.Hyps.Computations

/-!
# Challenge

The statements of `Tammes15.reduction` and `Tammes15.fejesToth_bound`, for Comparator (`config.json`). The
modules `Tammes15.Challenge.*` are copies of the 13 modules that hold the definitions the statements reach
(the import closure of `Tammes15.Hyps.Computations`), with their imports renamed and nothing else
changed. Nothing in the package imports this file. Its two warnings, that the declarations use `sorry`, are
expected: the proofs are in `Tammes15.Hyps.Reduction` and `Tammes15.FejesToth.Bound`, which Comparator checks
against these statements.
-/

theorem Tammes15.reduction (L : Set Tammes15.PlaneGraph) (F : Set Tammes15.Frame)
    (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L F) (h4 : Tammes15.AttainedHyp F) : Tammes15.Conjecture := sorry

theorem Tammes15.fejesToth_bound : Tammes15.FejesTothBound := sorry
