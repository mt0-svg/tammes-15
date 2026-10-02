import Tammes15.Attained.Frames
import Tammes15.Hyps.Reduction

/-!
# The capstone with D4 discharged

`Tammes15.reduction` with `F = {frameC1, frameC3}` and `AttainedHyp F` proved (`attained`): the
conjecture follows from D1, D2 and D3 for these two frames.
-/

namespace Tammes15

/-- `Tammes15.Conjecture` from `KappaHyp F` (D1), `EnumComplete L` (D2) and `Killed L F` (D3) for
`F = {frameC1, frameC3}`; D4 is `Attained.attained`. -/
theorem conjecture_of_frames (L : Set PlaneGraph)
    (h1 : KappaHyp {Attained.frameC1, Attained.frameC3}) (h2 : EnumComplete L)
    (h3 : Killed L {Attained.frameC1, Attained.frameC3}) : Conjecture :=
  reduction L _ h1 h2 h3 Attained.attained

end Tammes15
