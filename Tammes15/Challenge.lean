import Tammes15.Challenge.Hyps.Computations

/-!
# Challenge

The statement of `Tammes15.reduction`, for Comparator (`config.json`). The modules
`Tammes15.Challenge.*` are copies of the 13 modules that hold the definitions the statement reaches
(the import closure of `Tammes15.Hyps.Computations`), with their imports renamed and nothing else
changed. Nothing in the package imports this file. Its one warning, that the declaration uses `sorry`, is
expected: the proof is `Tammes15.Hyps.Reduction`, which Comparator checks against this statement.
-/

theorem Tammes15.reduction (L : Set Tammes15.PlaneGraph) (F : Set Tammes15.Frame)
    (h0 : Tammes15.FejesTothBound) (h1 : Tammes15.KappaHyp F) (h2 : Tammes15.EnumComplete L)
    (h3 : Tammes15.Killed L F) (h4 : Tammes15.AttainedHyp F) : Tammes15.Conjecture := sorry
