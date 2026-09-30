-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/CrossRotations.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8; see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.LocalRotations
import Tammes15.Vendor.EM8.SphericalTriangle

set_option maxHeartbeats 1000000
open Real
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Reflection in a nonzero axis is a half-turn, so it preserves the
oriented cross product in dimension three. -/
theorem lineReflection_cross (u x y : ℝ³) (hu : u ≠ 0) :
    crossVec (lineReflection u x) (lineReflection u y) = lineReflection u (crossVec x y) := by
  have hn : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hncoord : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_coordinate_sum]
    simp [Fin.sum_univ_succ, pow_two, add_assoc]
  ext i
  fin_cases i <;>
    simp [lineReflection_apply, crossVec, inner_coordinate_sum, Fin.sum_univ_succ] <;>
    field_simp [hn] <;> rw [hncoord] <;> ring

end Tammes15.Vendor.EM8.SquareAntiprismVerification
