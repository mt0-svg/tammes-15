-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/BestPacking.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8; see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.PackingConstants
import Tammes15.Vendor.EM8.PackingEndgame
import Tammes15.Vendor.EM8.PackingReduction
import Tammes15.Vendor.EM8.PackingMaximum
import Tammes15.Vendor.EM8.ContactGeometryGlobal
import Tammes15.Vendor.EM8.ContactCovering
import Tammes15.Vendor.EM8.ContactDirections
import Tammes15.Vendor.EM8.RhombusConcavity
import Tammes15.Vendor.EM8.VertexConcavity
import Tammes15.Vendor.EM8.RhombusScalar
import Tammes15.Vendor.EM8.AreaSummation
import Tammes15.Vendor.EM8.OrbitClosure
import Tammes15.Vendor.EM8.ContactSeparation
import Tammes15.Vendor.EM8.RhombusBounds
import Tammes15.Vendor.EM8.EqualityReconstruction
import Tammes15.Vendor.EM8.GlobalPackingAssembly
import Tammes15.Vendor.EM8.ArcEmbedding
import Tammes15.Vendor.EM8.ContactComponents
import Tammes15.Vendor.EM8.RotationSystem
import Tammes15.Vendor.EM8.ContactBoundary
import Tammes15.Vendor.EM8.SphericalPolygon
import Tammes15.Vendor.EM8.TangentAngles
import Tammes15.Vendor.EM8.PolygonExcess
import Tammes15.Vendor.EM8.BoundaryPolygons
import Tammes15.Vendor.EM8.ComponentHemisphere
import Tammes15.Vendor.EM8.BoundaryPartition
import Tammes15.Vendor.EM8.ContactFaceRegions
import Tammes15.Vendor.EM8.BoundaryCoverage
import Tammes15.Vendor.EM8.PermutationFixedSpace
import Tammes15.Vendor.EM8.ContactEulerBound
import Tammes15.Vendor.EM8.BoundarySupportAssembly
import Tammes15.Vendor.EM8.ShortBoundaryCycles
import Tammes15.Vendor.EM8.ContactQuadrilateral
import Tammes15.Vendor.EM8.BoundaryFaceSupport

open Real
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Rigidity direction of the paper's eight-point best-packing theorem.
Actual complementary face regions supply strict support of their directed
boundaries. The checked contact-tiling and equality reconstruction then
give congruence to the optimal square antiprism. -/
theorem eight_point_best_packing_rigidity
    (Y : Fin 8 → ℝ³) (hY : ∀ i, Y i ∈ unitSphere)
    (hsep : ∀ i j, i ≠ j → tau ≤ ‖Y i - Y j‖ ^ 2) :
    Congruent Y P :=
  packing_rigidity_interface_of_boundary_support irreducible_boundary_support Y hY hsep

end Tammes15.Vendor.EM8.SquareAntiprismVerification
