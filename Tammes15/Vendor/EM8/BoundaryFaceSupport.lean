-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/BoundaryFaceSupport.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, hand changes marked below, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.InitialSupportingFace
import Tammes15.Vendor.EM8.BoundarySupportAssembly

set_option maxHeartbeats 1500000
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactBoundaryCycle

theorem weak_support_from_actual_face {Y : Fin nPts → ℝ³} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    -- tammes-15 port change: the face chain takes the two-connectivity of the contacts (ContactTwoConnected) instead of c ≤ aInf, the only use it made of that bound.
    (C : ContactBoundaryCycle Y c hY hc) (hconn : ContactTwoConnected Y c)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.WeakSupport := by
  -- tammes-15 port change: passes ContactTwoConnected instead of c ≤ aInf.
  obtain ⟨base, hbase, hbaseG, hinitial⟩ := initial_supporting_face Y c hY hc hconn hbound hirr (C.point 0)
  let D := contactFaceRegion Y c base
  have hall (i : Fin (C.size + 1)) : FaceSupportsDart Y c D (C.point i) := by
    refine Fin.induction ?_ ?_ i
    · exact hinitial
    · intro j ih
      -- tammes-15 port change: passes ContactTwoConnected instead of c ≤ aInf.
      have hh := face_supports_next_dart Y c hY hc hconn hbound hirr base hbase hbaseG
        (C.point j.castSucc) ih
      rw [C.step] at hh
      have heq : j.castSucc + 1 = j.succ := by
        apply Fin.ext
        have hj := j.isLt
        have hsize : 1 < C.size + 1 := by omega
        simp [Fin.val_add, Nat.mod_eq_of_lt hsize,
          Nat.mod_eq_of_lt (show j.val + 1 < C.size + 1 by omega)]
      rwa [heq] at hh
  have hvertices (j : Fin (C.size + 1)) : Y (C.vertex j) ∈ D := by
    have hh := (hall j).1 0 ⟨le_rfl, zero_le_one⟩
    change shortSphereArc (Y (C.vertex j)) (Y (C.point j).2.val) 0 ∈ D at hh
    rwa [shortSphereArc_zero _ _ (hY.1 _)] at hh
  intro i j
  rw [C.vertex_next]
  exact (hall i).2 _ (hvertices j)

end ContactBoundaryCycle

/-- The actual contact boundaries have strict support, with their regions,
local models, convexity, and boundary propagation all constructed above. -/
theorem irreducible_boundary_support : IrreducibleBoundarySupport := by
  intro Y c hY hc hcupper hbound hirr hnonempty C
  -- tammes-15 port change: the eight-point case supplies ContactTwoConnected from c ≤ aInf.
  exact C.strict_support_of_weak_support hirr hbound
    (C.weak_support_from_actual_face (contactTwoConnected_of_aInf Y c hY.1 hc.1 hcupper hirr) hbound hirr)

end Tammes15.Vendor.EM8.SquareAntiprismVerification
