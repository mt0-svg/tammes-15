-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/FaceIncidence.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.AreaSummation

noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification

def faceCornersAt {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (v : Fin nPts) :
    Finset (Fin g × Fin m) := Finset.univ.filter (fun p => V p.1 p.2 = v)

def faceCornerCount {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (v : Fin nPts) : ℕ :=
  (faceCornersAt V v).card

def faceIncidentSum {g m : ℕ} (V : Fin g → Fin m → Fin nPts)
    (f : Fin g → Fin m → ℝ) (v : Fin nPts) : ℝ :=
  ∑ p ∈ faceCornersAt V v, f p.1 p.2

lemma sum_faceIncidentSum {g m : ℕ} (V : Fin g → Fin m → Fin nPts)
    (f : Fin g → Fin m → ℝ) :
    ∑ v, faceIncidentSum V f v = ∑ i, ∑ j, f i j := by
  classical
  simp only [faceIncidentSum, faceCornersAt, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [Fintype.sum_prod_type]

lemma faceCornerCount_eq_sum_one {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (v : Fin nPts) :
    (faceCornerCount V v : ℝ) = faceIncidentSum V (fun _ _ => 1) v := by
  simp [faceCornerCount, faceIncidentSum]

lemma sum_faceCornerCount {g m : ℕ} (V : Fin g → Fin m → Fin nPts) :
    ∑ v, (faceCornerCount V v : ℝ) = (m : ℝ) * (g : ℝ) := by
  simp only [faceCornerCount_eq_sum_one]
  rw [sum_faceIncidentSum]
  simp [mul_comm]

lemma sum_faceIncidentArea {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (A : Fin g → ℝ) :
    ∑ v, faceIncidentSum V (fun i _ => A i) v = (m : ℝ) * ∑ i, A i := by
  rw [sum_faceIncidentSum]
  simp [Finset.mul_sum]

lemma faceIncidentSum_const {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (v : Fin nPts) (a : ℝ) :
    faceIncidentSum V (fun _ _ => a) v = (faceCornerCount V v : ℝ) * a := by
  simp [faceIncidentSum, faceCornerCount]

lemma faceIncidentSum_add {g m : ℕ} (V : Fin g → Fin m → Fin nPts)
    (f k : Fin g → Fin m → ℝ) (v : Fin nPts) :
    faceIncidentSum V (fun i j => f i j + k i j) v = faceIncidentSum V f v + faceIncidentSum V k v := by
  simp only [faceIncidentSum, Finset.sum_add_distrib]

lemma faceIncidentSum_eq_subtype_sum {g m : ℕ} (V : Fin g → Fin m → Fin nPts)
    (f : Fin g → Fin m → ℝ) (v : Fin nPts) :
    faceIncidentSum V f v = ∑ p : ↥(faceCornersAt V v), f p.val.1 p.val.2 := by
  simp [faceIncidentSum]
  exact (Finset.sum_attach _ _).symm

lemma faceCornerCount_eq_fintype_card {g m : ℕ} (V : Fin g → Fin m → Fin nPts) (v : Fin nPts) :
    faceCornerCount V v = Fintype.card ↥(faceCornersAt V v) := by
  simp [faceCornerCount]

end Tammes15.Vendor.EM8.SquareAntiprismVerification
