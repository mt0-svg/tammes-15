-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/BoundarySupportAssembly.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8; see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.BoundaryAdjacency
import Tammes15.Vendor.EM8.GlobalPackingAssembly

noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The remaining geometric obligation: actual directed contact boundaries
must have every nonincident boundary vertex strictly to the left of every
edge. This names a proposition, not an axiom or an existence proof. -/
def IrreducibleBoundarySupport : Prop :=
  ∀ (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1), c ≤ aInf → PackingInnerBound c Y →
    PackingIrreducible c Y → (packingContacts c Y).Nonempty →
    ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport

/-- Coverage, face arrays, angle sums, Euler, and adjacency are all derived
from strict boundary support, rather than included as further assumptions. -/
theorem decomposition_of_boundary_support (hsupport : IrreducibleBoundarySupport) :
    IrreducibleContactDecomposition := by
  intro Y c hY hc hcupper hbound hirr hne
  let hcI : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩
  have hs := hsupport Y c hY hcI hcupper hbound hirr hne
  exact ⟨supportedContactTilingData Y c hY hcI hcupper hirr hbound hne hs,
    supported_tiling_boundary_adjacency Y c hY hcI hcupper hirr hbound hne hs⟩

theorem packing_rigidity_interface_of_boundary_support (hsupport : IrreducibleBoundarySupport)
    (Y : Fin 8 → ℝ³) (hY : ∀ i, Y i ∈ unitSphere)
    (hsep : ∀ i j, i ≠ j → tau ≤ ‖Y i - Y j‖ ^ 2) : Congruent Y P :=
  packing_rigidity_interface_of_decomposition (decomposition_of_boundary_support hsupport) Y hY hsep

end Tammes15.Vendor.EM8.SquareAntiprismVerification
