-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/RotationSystem.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.ContactOrder
import Tammes15.Vendor.EM8.ContactComponents

open Real
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev ContactNeighbor (Y : Fin nPts → ℝ³) (c : ℝ) (i : Fin nPts) :=
  {j : Fin nPts // j ≠ i ∧ inner ℝ (Y i) (Y j) = c}

/-- An oriented actual contact edge, with its base recorded first. -/
abbrev ContactDart (Y : Fin nPts → ℝ³) (c : ℝ) :=
  (i : Fin nPts) × ContactNeighbor Y c i

def contactReverse (Y : Fin nPts → ℝ³) (c : ℝ) : Equiv.Perm (ContactDart Y c) where
  toFun d := ⟨d.2.val, ⟨d.1, d.2.property.1.symm,
    (real_inner_comm (Y d.1) (Y d.2.val)).trans d.2.property.2⟩⟩
  invFun d := ⟨d.2.val, ⟨d.1, d.2.property.1.symm,
    (real_inner_comm (Y d.1) (Y d.2.val)).trans d.2.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def contactRotateAt (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (i : Fin nPts) :
    Equiv.Perm (ContactNeighbor Y c i) := by
  classical
  exact if hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c then
    (Classical.choice (contact_order_exists Y c i hY hc hne)).successor
  else Equiv.refl _

def contactRotate (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    Equiv.Perm (ContactDart Y c) where
  toFun d := ⟨d.1, contactRotateAt Y c hY hc d.1 d.2⟩
  invFun d := ⟨d.1, (contactRotateAt Y c hY hc d.1).symm d.2⟩
  left_inv d := by simp
  right_inv d := by simp

/-- Follow the edge, then take the immediately clockwise outgoing edge.
This is the boundary permutation for faces lying to the left of a walk. -/
def contactFaceNext (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    Equiv.Perm (ContactDart Y c) :=
  (contactReverse Y c).trans (contactRotate Y c hY hc).symm

@[simp] lemma contactFaceNext_base (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (d : ContactDart Y c) :
    (contactFaceNext Y c hY hc d).1 = d.2.val := rfl

theorem contactRotateAt_triple_pos (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin nPts) (j : ContactNeighbor Y c i) :
    0 < inner ℝ (crossVec (Y j) (Y (contactRotateAt Y c hY hc i j))) (Y i) := by
  classical
  have hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨j, j.property⟩
  unfold contactRotateAt
  rw [dif_pos hne]
  exact (Classical.choice (contact_order_exists Y c i hY hc hne)).successor_triple_pos
    hY.1 hc hirr j

theorem contactRotateAt_angle_sum (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin nPts)
    (hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    ∑ j : ContactNeighbor Y c i,
      contactAngle c (Y j) (Y (contactRotateAt Y c hY hc i j)) = 2 * Real.pi := by
  classical
  unfold contactRotateAt
  rw [dif_pos hne]
  let D := Classical.choice (contact_order_exists Y c i hY hc hne)
  change ∑ j : ContactNeighbor Y c i, contactAngle c (Y j) (Y (D.successor j)) = _
  rw [← Equiv.sum_comp D.labelEquiv]
  simpa only [D.successor_label, D.labelEquiv_val, ← D.gap_eq_contactAngle hY.1 hc hirr] using D.gap_sum

lemma contactFaceNext_ne_self (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (d : ContactDart Y c) : contactFaceNext Y c hY hc d ≠ d := by
  intro heq
  have hbase := congrArg Sigma.fst heq
  exact d.2.property.1 hbase

/-- Every corner of the boundary permutation has the strict, consistent
left-turn orientation required for a spherical face boundary. -/
theorem contactFaceNext_triple_pos (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (d : ContactDart Y c) :
    0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y (contactFaceNext Y c hY hc d).2.val) := by
  let e := contactFaceNext Y c hY hc d
  have he : contactRotateAt Y c hY hc d.2.val e.2 = (contactReverse Y c d).2 := by
    change contactRotateAt Y c hY hc d.2.val
      ((contactRotateAt Y c hY hc d.2.val).symm (contactReverse Y c d).2) = _
    exact (contactRotateAt Y c hY hc d.2.val).apply_symm_apply _
  have h := contactRotateAt_triple_pos Y c hY hc hirr d.2.val e.2
  rw [he] at h
  change 0 < inner ℝ (crossVec (Y e.2.val) (Y d.1)) (Y d.2.val) at h
  rw [triple_cyclic] at h
  exact h

lemma contactFaceNext_no_backtrack (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (d : ContactDart Y c) :
    (contactFaceNext Y c hY hc d).2.val ≠ d.1 := by
  intro heq
  have h := contactFaceNext_triple_pos Y c hY hc hirr d
  rw [heq, crossVec_inner_left] at h
  exact (lt_irrefl 0) h

end Tammes15.Vendor.EM8.SquareAntiprismVerification
