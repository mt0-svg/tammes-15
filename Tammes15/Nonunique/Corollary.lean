import Tammes15.Nonunique.Defs
import Tammes15.Nonunique.SepLt
import Tammes15.Attained.Final

/-!
# Corollary 1.2: the optimum is not unique

`Tammes15.nonunique_of_enum_killed`: under D2 (`EnumComplete L`) and D3 (`Killed L {frameC1, frameC3}`),
the conditions of `Tammes15.conjecture_of_enum_killed`, the maximum `d` of the achievable minimal
distances of 15 points is attained by two configurations whose contact graphs at `cos d` are not
isomorphic: the frames C1 and C3 of D4.

Unconditional parts: `frames_not_iso` (the contact graphs of C1 and C3 at `uR` are not isomorphic)
and the attainment of `arccos uR` by both frames (D4). The contacts are exact: the 30 listed pairs
are at inner product `uR` (`frameC1_contact`, `frameC3_contact`), every other pair is strictly below
(`frameC1_sep_lt`, `frameC3_sep_lt`, module `SepLt`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Nonunique

open Tammes15 Tammes15.Attained

theorem frameC1_S_eq : frameC1.S = S1 := rfl

theorem frameC3_S_eq : frameC3.S = S3 := rfl

/-- The contact graph of C1 at `uR` is the graph of its 30 listed contacts. -/
theorem contactGraph_C1 : contactGraph frameC1.p uR = listGraph S1 :=
  contactGraph_eq_listGraph _ _ _ S1_lt
    (fun ij h => (frameC1_contact ij (frameC1_S_eq ▸ h)).2) frameC1_sep_lt

/-- The contact graph of C3 at `uR` is the graph of its 30 listed contacts. -/
theorem contactGraph_C3 : contactGraph frameC3.p uR = listGraph S3 :=
  contactGraph_eq_listGraph _ _ _ S3_lt
    (fun ij h => (frameC3_contact ij (frameC3_S_eq ▸ h)).2) frameC3_sep_lt

/-- The contact graphs of C1 and C3 are not isomorphic. -/
theorem frames_not_iso : IsEmpty (contactGraph frameC1.p uR ≃g contactGraph frameC3.p uR) :=
  isEmpty_iso_congr contactGraph_C1 contactGraph_C3 listGraph_S1_not_iso

/-- Under the conjecture, `arccos u` is the maximum for the root `u` of the quintic. -/
theorem isGreatest_of_conjecture (u : ℝ) (hu : 1 / 2 < u ∧ u < 7 / 10 ∧ quintic u = 0)
    (h : Conjecture) : IsGreatest {d | Achievable 15 d} (arccos u) := by
  rcases h with ⟨v, hv⟩
  have h_eq : v = u := existsUnique_root.unique ⟨hv.1, hv.2.1, hv.2.2.1⟩ hu
  rw [h_eq] at hv
  exact hv.2.2.2

/-- Unit vectors with pairwise inner products at most `u` are pairwise at angle at least
`arccos u`. -/
theorem angle_ge_of_inner_le {N : ℕ} (X : Fin N → Tammes15.E3) (u : ℝ) (hX : ∀ i, ‖X i‖ = 1)
    (hsep : ∀ i j, i ≠ j → ⟪X i, X j⟫ ≤ u) : ∀ i j, i ≠ j → arccos u ≤ angle (X i) (X j) := by
  intro i j hne
  have hnorm_i : ‖X i‖ = 1 := hX i
  have hnorm_j : ‖X j‖ = 1 := hX j
  have hinner_le_u : ⟪X i, X j⟫ ≤ u := hsep i j hne
  have habs_inner : |⟪X i, X j⟫| ≤ ‖X i‖ * ‖X j‖ := abs_real_inner_le_norm (X i) (X j)
  rw [hnorm_i, hnorm_j, mul_one] at habs_inner
  have h_inner_ge_neg_one : -1 ≤ ⟪X i, X j⟫ := (abs_le.mp habs_inner).left
  have h_angle_eq : angle (X i) (X j) = arccos (⟪X i, X j⟫) := by
    rw [InnerProductGeometry.angle, hnorm_i, hnorm_j]
    simp
  rw [h_angle_eq]
  exact Real.arccos_le_arccos hinner_le_u

/-- The corollary from its parts, for any root `u` and any two configurations. -/
theorem nonunique_of_parts (u : ℝ) (hu : 1 / 2 < u ∧ u < 7 / 10 ∧ quintic u = 0)
    (h : Conjecture) (X Y : Fin 15 → Tammes15.E3) (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ i, ‖Y i‖ = 1)
    (hXs : ∀ i j, i ≠ j → ⟪X i, X j⟫ ≤ u) (hYs : ∀ i j, i ≠ j → ⟪Y i, Y j⟫ ≤ u)
    (hne : IsEmpty (contactGraph X u ≃g contactGraph Y u)) :
    ∃ d : ℝ, IsGreatest {d | Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ angle (X i) (X j)) ∧ (∀ i j, i ≠ j → d ≤ angle (Y i) (Y j)) ∧
        IsEmpty (contactGraph X (cos d) ≃g contactGraph Y (cos d)) := by
  refine ⟨arccos u, isGreatest_of_conjecture u hu h, X, Y, hX, hY,
    angle_ge_of_inner_le X u hX hXs, angle_ge_of_inner_le Y u hY hYs, ?_⟩
  have hu_low : -1 ≤ u := by linarith
  have hu_high : u ≤ 1 := by linarith
  rw [Real.cos_arccos hu_low hu_high]
  exact hne

/-- Corollary 1.2. Under D2 and D3, the maximum `d` of the minimal distance of 15 points is attained
by two configurations whose contact graphs at angle `d` are not isomorphic. -/
theorem _root_.Tammes15.nonunique_of_enum_killed (L : Set PlaneGraph) (h2 : EnumComplete L)
    (h3 : Killed L {frameC1, frameC3}) :
    ∃ d : ℝ, IsGreatest {d | Achievable 15 d} d ∧
      ∃ X Y : Fin 15 → Tammes15.E3, (∀ i, ‖X i‖ = 1) ∧ (∀ i, ‖Y i‖ = 1) ∧
        (∀ i j, i ≠ j → d ≤ angle (X i) (X j)) ∧ (∀ i j, i ≠ j → d ≤ angle (Y i) (Y j)) ∧
        IsEmpty (contactGraph X (cos d) ≃g contactGraph Y (cos d)) :=
  nonunique_of_parts uR ⟨(bounds_of_mem uR uR_spec.1).1, (bounds_of_mem uR uR_spec.1).2, uR_spec.2⟩
    (conjecture_of_enum_killed L h2 h3) frameC1.p frameC3.p frameC1_unit frameC3_unit frameC1_sep
    frameC3_sep frames_not_iso

end Tammes15.Nonunique
