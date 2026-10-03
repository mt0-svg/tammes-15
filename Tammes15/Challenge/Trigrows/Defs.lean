import Mathlib

/-!
# Real functions of the rows and face relations

The functions of Sections 4 and 6 of the paper that the rows (6.1) and the face relations (6.2)
are written with. Statements about them: `Tammes15.Trigrows.Mono`.
-/

open Real

namespace Tammes15

/-- `α(d) = arccos (cos d / (1 + cos d))`, the least corner (Lemma A.1). -/
noncomputable def alpha (d : ℝ) : ℝ := arccos (cos d / (1 + cos d))

/-- The rattler radius `h(d) = arccos (cos d / cos (d/2))` (Lemma A.9). -/
noncomputable def hrad (d : ℝ) : ℝ := arccos (cos d / cos (d / 2))

/-- `ρ_d(x) = π - 2 arctan (cos d tan (x/2))`, the opposite corner of a rhombus. -/
noncomputable def rho (d x : ℝ) : ℝ := π - 2 * arctan (cos d * tan (x / 2))

/-- `S(d) = 4 arctan (1 / sqrt (cos d))`, the bound on the corner sum of a rhombus. -/
noncomputable def Ssum (d : ℝ) : ℝ := 4 * arctan (1 / Real.sqrt (cos d))

/-- Base of the isosceles triangle with legs `d` and apex angle `u`. -/
noncomputable def ebase (d u : ℝ) : ℝ := 2 * arcsin (sin d * sin (u / 2))

/-- Base angle of the isosceles triangle with legs `d` and apex angle `u`. -/
noncomputable def bangle (d u : ℝ) : ℝ := arctan (cos (u / 2) / (cos d * sin (u / 2)))

/-- `η(g; e, f) = (cos g - cos e cos f) / (sin e sin f)`, the cosine of the angle opposite the
side `g` in the triangle with sides `e, f, g`. -/
noncomputable def eta (g e f : ℝ) : ℝ := (cos g - cos e * cos f) / (sin e * sin f)

/-- `γ(g; e, f) = arccos η(g; e, f)`, the angle opposite `g`. -/
noncomputable def gam (g e f : ℝ) : ℝ := arccos (eta g e f)

end Tammes15
