import Tammes15.Statement
import Tammes15.Trigrows.Margins

/-!
# The functions of params_check

`smax d = 4 atan (1 / √(cos d))`, the bound of the rhombus row `x + y ≤ shi`
(code/gp/consts.gp); `Pform l h`, the closed form of the perimeter of Section 3.4
(`P(l, h)` of the paper, margin [3.4]); `pa k`, the ends of the 40 subintervals of `[dlo, dhi]`
on which [3.4] is checked.
-/

open Real

namespace Tammes15.Params

/-- `smax d = 4 atan (1 / √(cos d))`. -/
noncomputable def smax (d : ℝ) : ℝ := 4 * arctan (1 / √(cos d))

/-- `P(l, h) = 2 arccos ((cos l - sin² h) / cos² h) + 2 sin h (π - 2 arcsin (tan h tan (l / 2)))`. -/
noncomputable def Pform (l h : ℝ) : ℝ :=
  2 * arccos ((cos l - sin h ^ 2) / cos h ^ 2) + 2 * sin h * (π - 2 * arcsin (tan h * tan (l / 2)))

/-- The ends of the 40 subintervals of `[dlo, dhi]`: `pa k = dlo + k (dhi - dlo) / 40`. -/
noncomputable def pa (k : ℕ) : ℝ := dlo + k * (dhi - dlo) / 40

end Tammes15.Params
