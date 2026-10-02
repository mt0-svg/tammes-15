import Tammes15.Nonunique.Corollary

/-!
# The last sentence of Corollary 1.2: `C1` and `C3` are not isometric

For unit vectors `‖x - y‖² = 2 - 2⟪x, y⟫`, so a bijection of the points of `C1` with those of `C3`
that keeps the distances keeps the inner products, and would be an isomorphism of the contact
graphs at `uR`, against `Nonunique.frames_not_iso`.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-- No bijection of the points of `C1` with those of `C3` keeps the distances. -/
theorem frames_not_distance_preserving :
    ¬ ∃ σ : Fin 15 ≃ Fin 15, ∀ i j,
      ‖frameC3.p (σ i) - frameC3.p (σ j)‖ = ‖frameC1.p i - frameC1.p j‖ := by
  intro h
  rcases h with ⟨σ, h⟩
  have h_inner : ∀ i j, ⟪frameC3.p (σ i), frameC3.p (σ j)⟫ = ⟪frameC1.p i, frameC1.p j⟫ := by
    intro i j
    have hdist := h i j
    have hsq : ‖frameC3.p (σ i) - frameC3.p (σ j)‖ ^ 2 = ‖frameC1.p i - frameC1.p j‖ ^ 2 := by
      rw [hdist]
    rw [norm_sub_sq_real, norm_sub_sq_real] at hsq
    have hnorm1 : ∀ k, ‖frameC1.p k‖ ^ 2 = 1 := by
      intro k
      have hk := frameC1_unit k
      nlinarith
    have hnorm3 : ∀ k, ‖frameC3.p k‖ ^ 2 = 1 := by
      intro k
      have hk := frameC3_unit k
      nlinarith
    rw [hnorm3 (σ i), hnorm3 (σ j), hnorm1 i, hnorm1 j] at hsq
    nlinarith
  have hiso : Tammes15.Nonunique.contactGraph frameC1.p uR ≃g Tammes15.Nonunique.contactGraph frameC3.p uR := by
    refine
    { toEquiv := σ
      map_rel_iff' := ?_ }
    intro i j
    dsimp [Tammes15.Nonunique.contactGraph]
    have hne_iff : σ i ≠ σ j ↔ i ≠ j := by
      constructor
      · intro hne h_eq
        apply hne
        rw [h_eq]
      · intro hne h_eq
        apply hne
        apply σ.injective
        rw [h_eq]
    simp only [h_inner i j, hne_iff]
  exact Tammes15.Nonunique.frames_not_iso.false hiso

/-- `C1` and `C3` are not isometric: no isometry of space maps the one set onto the other. -/
theorem frames_not_isometric :
    ¬ ∃ O : E3 ≃ᵢ E3, O '' Set.range frameC1.p = Set.range frameC3.p := by
  intro h
  rcases h with ⟨O, hO⟩
  -- For each i, O (frameC1.p i) is in Set.range frameC3.p
  have h_exists : ∀ i, ∃ j, O (frameC1.p i) = frameC3.p j := by
    intro i
    have h_mem : O (frameC1.p i) ∈ O '' Set.range frameC1.p :=
      Set.mem_image_of_mem O ⟨i, rfl⟩
    rw [hO] at h_mem
    rcases h_mem with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  -- Define σ i as a j such that O (frameC1.p i) = frameC3.p (σ i)
  let σ : Fin 15 → Fin 15 := fun i => Classical.choose (h_exists i)
  have h_σ : ∀ i, O (frameC1.p i) = frameC3.p (σ i) := by
    intro i
    exact Classical.choose_spec (h_exists i)
  -- σ is injective: if σ i = σ j then O (frameC1.p i) = O (frameC1.p j),
  -- so frameC1.p i = frameC1.p j (O is injective), contradicting frameC1_sep + uR < 1
  have h_σ_inj : Function.Injective σ := by
    intro i j h
    by_contra hne
    have h_O_eq : O (frameC1.p i) = O (frameC1.p j) := by
      rw [h_σ i, h_σ j, h]
    have h_eq_frames : frameC1.p i = frameC1.p j := O.injective h_O_eq
    have h_inner_le_uR : ⟪frameC1.p i, frameC1.p j⟫ ≤ uR := frameC1_sep i j hne
    have h_inner_eq_one : ⟪frameC1.p i, frameC1.p j⟫ = (1 : ℝ) := by
      rw [h_eq_frames]
      have h_norm : ‖frameC1.p j‖ = 1 := frameC1_unit j
      have h_inner_sq : ⟪frameC1.p j, frameC1.p j⟫ = ‖frameC1.p j‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℝ) (frameC1.p j)
      calc
        ⟪frameC1.p j, frameC1.p j⟫ = ‖frameC1.p j‖ ^ 2 := h_inner_sq
        _ = (1 : ℝ) ^ 2 := by rw [h_norm]
        _ = (1 : ℝ) := by norm_num
    have h_one_le_uR : (1 : ℝ) ≤ uR := by
      linarith
    have h_uR_lt_one : uR < 1 := by
      have hmem : uR ∈ Set.Icc ul uh := uR_spec.1
      rcases bounds_of_mem uR hmem with ⟨_, h_lt⟩
      linarith
    linarith
  -- σ is bijective (injective on Fin 15 implies bijective)
  have h_σ_bijective : Function.Bijective σ :=
    (Finite.injective_iff_bijective (f := σ)).mp h_σ_inj
  let σ_equiv : Fin 15 ≃ Fin 15 := Equiv.ofBijective σ h_σ_bijective
  -- σ preserves distances
  have h_dist : ∀ i j, ‖frameC3.p (σ_equiv i) - frameC3.p (σ_equiv j)‖ = ‖frameC1.p i - frameC1.p j‖ := by
    intro i j
    have h1 : frameC3.p (σ_equiv i) = O (frameC1.p i) := (h_σ i).symm
    have h2 : frameC3.p (σ_equiv j) = O (frameC1.p j) := (h_σ j).symm
    rw [h1, h2, (dist_eq_norm _ _).symm, O.dist_eq, dist_eq_norm]
  -- This contradicts frames_not_distance_preserving
  apply frames_not_distance_preserving
  exact ⟨σ_equiv, h_dist⟩

end Tammes15.PaperSteps
