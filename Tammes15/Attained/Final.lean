import Tammes15.Attained.Capstone
import Tammes15.Kappa.Assembly

/-!
# The capstone with D1 and D4 discharged

`Tammes15.reduction` with `F = {frameC1, frameC3}`: D4 is `Attained.attained` and D1 is `Kappa.kappaHyp`, so the
conjecture follows from D2 and D3 alone.
-/

namespace Tammes15

/-- `Tammes15.Conjecture` from `EnumComplete L` (D2) and `Killed L {frameC1, frameC3}` (D3). -/
theorem conjecture_of_enum_killed (L : Set PlaneGraph) (h2 : EnumComplete L)
    (h3 : Killed L {Attained.frameC1, Attained.frameC3}) : Conjecture :=
  conjecture_of_frames L Kappa.kappaHyp h2 h3

end Tammes15
