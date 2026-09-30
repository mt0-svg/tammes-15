import Tammes15.Statement
import Tammes15.Trigrows.Defs

/-!
# Spherical distance and tangent directions

Points of `S²` are unit vectors of `E3` (`lean/Tammes15/Statement.lean`). The spherical distance is the
angle `arccos ⟪p, q⟫`; the corner at `v` between the arcs `v w₁` and `v w₂` is the angle between
the tangent directions `tdir v w₁` and `tdir v w₂`.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15

/-- Spherical distance of unit vectors. -/
noncomputable def sdist (p q : E3) : ℝ := arccos ⟪p, q⟫

/-- Tangent direction at `v` towards `w` (unnormalised): the component of `w` orthogonal to `v`. -/
noncomputable def tdir (v w : E3) : E3 := w - ⟪v, w⟫ • v

end Tammes15
