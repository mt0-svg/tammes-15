import Tammes15.PaperSteps.Main
import Tammes15.PaperSteps.Search

/-!
# The main theorem from D2 and the replayed trees

`conjecture_of_enum_progTrees`: `Tammes15.Conjecture` from D2 (`EnumComplete L`), the trees that the
replays of the program accept on `L` (`PaperSteps.ProgTrees L N`) and the soundness of the
interval procedures `N` of the program (`PaperSteps.Procs.Sound N`).
-/

namespace Tammes15

/-- `Tammes15.Conjecture` from `EnumComplete L` (D2), the replayed trees of the program on `L`,
and the soundness of its interval procedures. -/
theorem conjecture_of_enum_progTrees (L : Set PlaneGraph) (N : PaperSteps.Procs)
    (h2 : EnumComplete L) (h3 : PaperSteps.ProgTrees L N) (hN : N.Sound) : Conjecture :=
  conjecture_of_enum_progKilled L h2 (PaperSteps.progKilled_of_progTrees h3 hN)

end Tammes15
