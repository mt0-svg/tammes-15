-- Vendored from github.com/lukasliehr/Energy-Minimization-8-Points, commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
-- file LeanCode/LargeS/Lean_Code/ContactBoundary.lean (Kryvonos, Liehr, Taylor, arXiv 2609.22077).
-- Changed for tammes-15: imports Lean_Code.* renamed Tammes15.Vendor.EM8.*, declarations moved under namespace Tammes15.Vendor.EM8, `Fin 8` generalized to `Fin nPts` (auto-bound); see THIRD_PARTY.md.
import Tammes15.Vendor.EM8.RotationSystem
import Tammes15.Vendor.EM8.FiniteCycles

open Real
noncomputable section
namespace Tammes15.Vendor.EM8.SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev ContactBoundaryCycle (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :=
  PermutationCycle (contactFaceNext Y c hY hc)

theorem contact_boundary_cycle_exists (Y : Fin nPts → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (d : ContactDart Y c) :
    ∃ C : ContactBoundaryCycle Y c hY hc, C.point 0 = d := by
  classical
  exact permutation_cycle_exists (contactFaceNext Y c hY hc) d

namespace ContactBoundaryCycle

variable {Y : Fin nPts → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

def vertex (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) : Fin nPts := (C.point i).1

lemma vertex_next (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    C.vertex (i + 1) = (C.point i).2.val :=
  (congrArg Sigma.fst (C.step i)).symm

lemma adjacent_ne (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    C.vertex i ≠ C.vertex (i + 1) := by
  rw [C.vertex_next]
  exact (C.point i).2.property.1.symm

lemma contact (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    inner ℝ (Y (C.vertex i)) (Y (C.vertex (i + 1))) = c := by
  rw [C.vertex_next]
  exact (C.point i).2.property.2

theorem strict_turn (C : ContactBoundaryCycle Y c hY hc) (hirr : PackingIrreducible c Y)
    (i : Fin (C.size + 1)) :
    0 < inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1))))
      (Y (C.vertex (i + 1 + 1))) := by
  have ht := contactFaceNext_triple_pos Y c hY hc hirr (C.point i)
  rw [C.step i] at ht
  rw [C.vertex_next (i + 1), C.vertex_next i]
  exact ht

lemma length_ge_three (C : ContactBoundaryCycle Y c hY hc) (hirr : PackingIrreducible c Y) :
    3 ≤ C.size + 1 := by
  by_contra h
  have hs : C.size ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hzero | hone
  · have hi : (0 : Fin (C.size + 1)) + 1 = 0 := by
      apply Fin.ext
      simp [Fin.val_add_one, Fin.ext_iff, hzero]
    have hstep := C.step 0
    rw [hi] at hstep
    exact contactFaceNext_ne_self Y c hY hc (C.point 0) hstep
  · have hi : (0 : Fin (C.size + 1)) + 1 + 1 = 0 := by
      apply Fin.ext
      norm_num [Fin.val_add_one, Fin.ext_iff, hone]
    have hstep : contactFaceNext Y c hY hc (contactFaceNext Y c hY hc (C.point 0)) = C.point 0 := by
      rw [C.step, C.step, hi]
    have hbase := congrArg Sigma.fst hstep
    exact contactFaceNext_no_backtrack Y c hY hc hirr (C.point 0) hbase

end ContactBoundaryCycle

end Tammes15.Vendor.EM8.SquareAntiprismVerification
