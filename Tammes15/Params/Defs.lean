/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
import Tammes15.Statement
import Tammes15.Trigrows.Margins

/-!
# The function of the parameter inequalities

`smax d = 4 atan (1 / √(cos d))`, the bound of the rhombus row `x + y ≤ shi`
(code/gp/consts.gp).
-/

open Real

namespace Tammes15.Params

/-- `smax d = 4 atan (1 / √(cos d))`. -/
noncomputable def smax (d : ℝ) : ℝ := 4 * arctan (1 / √(cos d))

end Tammes15.Params
