import Tammes15.Hyps.Reduction
import Tammes15.Attained.Final
import Tammes15.Nonunique.Corollary
import Tammes15.PaperSteps.MainSearch
import Tammes15.PaperSteps.Optima
import Tammes15.PaperSteps.Isometric
import Tammes15.Contractors.Main

/-!
# Solution

`Tammes15.reduction` is proved in `Tammes15/Hyps/Reduction.lean` and `Tammes15.fejesToth_bound` in
`Tammes15/FejesToth/Bound.lean`, which the first imports, from the definitions of `Tammes15/Statement.lean` and
`Tammes15/Hyps/Computations.lean`. `Tammes15.conjecture_of_enum_killed` is proved in
`Tammes15/Attained/Final.lean`, from `Tammes15.reduction` with D4 (`Tammes15.Attained.attained`) and D1
(`Tammes15.Kappa.kappaHyp`) for the frames of `Tammes15/Attained/Data.lean`. `Tammes15.nonunique_of_enum_killed` is
proved in `Tammes15/Nonunique/Corollary.lean`, from `Tammes15.conjecture_of_enum_killed` and the contact graphs of the
two frames, with `contactGraph` of `Tammes15/Nonunique/Defs.lean`.

`Tammes15.PaperSteps.killed_of_progKilled` is proved in `Tammes15/PaperSteps/Main.lean`, from the relabelling of
`Tammes15/PaperSteps/Relabel.lean`, the reflection of `Tammes15/PaperSteps/Reflect.lean` and the target balls of
`Tammes15/PaperSteps/Targets.lean`, and `Tammes15.conjecture_of_enum_progKilled` in the same module, from it and
`Tammes15.conjecture_of_enum_killed`. `Tammes15.PaperSteps.progKilled_of_progTrees` is proved in
`Tammes15/PaperSteps/Search.lean`, from the soundness of search trees of `Tammes15/PaperSteps/SearchTree.lean`, and
`Tammes15.conjecture_of_enum_progTrees` in `Tammes15/PaperSteps/MainSearch.lean`, from the two. The definitions of
these statements are those of `Tammes15/PaperSteps/Defs.lean`, `Tammes15/PaperSteps/TieData.lean`,
`Tammes15/PaperSteps/SearchTree.lean` and `Tammes15/PaperSteps/SearchDefs.lean`.
`Tammes15.PaperSteps.local_optimality_frame` is proved in `Tammes15/PaperSteps/LocalEq.lean` and
`Tammes15.PaperSteps.optima_four` in `Tammes15/PaperSteps/Optima.lean`, with the definitions of
`Tammes15/PaperSteps/FrameDefs.lean`; `Tammes15.PaperSteps.frames_not_isometric` and
`Tammes15.PaperSteps.frames_not_distance_preserving` are proved in `Tammes15/PaperSteps/Isometric.lean`.

`Tammes15.conjecture_of_enum_progTreesDom` is proved in `Tammes15/Contractors/Statement.lean`, from
`Tammes15.conjecture_of_enum_progTrees` and the soundness of the procedures of the program on the domain
(`Tammes15.Contractors.Impl.onDom_sound`), and `Tammes15.Contractors.killed_of_progTreesDom` and
`Tammes15.nonunique_of_enum_progTreesDom` in `Tammes15/Contractors/Main.lean`. The definitions of these statements
are those of `Tammes15/Contractors/Defs.lean`, `Tammes15/Contractors/Prims.lean` and `Tammes15/Contractors/Arith.lean`.
-/
