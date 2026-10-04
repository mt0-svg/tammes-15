import Tammes15.W1Filter.Defs
import Tammes15.Attained.Final
import Tammes15.W1Filter.Capstone

namespace Tammes15.W1Filter

open Tammes15 Tammes15.D3lp

theorem conjecture_of_plantri_run (S : Set (List ℕ)) (codes : Set GCode) (h1 : EnumCompletePC S)
    (h2 : RunW1 S codes) (h3 : Killed (LOf codes) {Attained.frameC1, Attained.frameC3}) :
    Conjecture :=
  conjecture_of_plantri_run_proof S codes h1 h2 h3

end Tammes15.W1Filter
