import Tammes15.Trigrows.Sdist

/-!
# Pair: the chord bound

`norm_sub_eq_two_sin`: the chord of an arc of length `θ` is `2 sin (θ/2)`;
`pair_core`: two points at spherical distance at least `d₋`, each within `ρ` of a centre,
have centres at chord distance at least `2 sin (d₋/2) - ρ₁ - ρ₂` (the soundness of Pair).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

theorem norm_sub_eq_two_sin (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ = 2 * sin (sdist p q / 2) := by
  have h_sq := norm_sub_sq_unit p q hp hq
  have h_sdist_low : 0 ≤ sdist p q := Real.arccos_nonneg _
  have h_sdist_high : sdist p q ≤ π := Real.arccos_le_pi _
  have h_sin_nonneg : 0 ≤ sin (sdist p q / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith
    · nlinarith [h_sdist_high]
  have h_trig : 2 - 2 * cos (sdist p q) = (2 * sin (sdist p q / 2)) ^ 2 := by
    have h := Real.sin_sq_eq_half_sub (sdist p q / 2)
    calc
      2 - 2 * cos (sdist p q) = 2 * (1 - cos (sdist p q)) := by ring
      _ = 2 * (2 * sin (sdist p q / 2) ^ 2) := by
        rw [h]
        have hcos : 2 * (sdist p q / 2) = sdist p q := by ring
        rw [hcos]
        ring
      _ = (2 * sin (sdist p q / 2)) ^ 2 := by ring
  have h_sq_eq : ‖p - q‖ ^ 2 = (2 * sin (sdist p q / 2)) ^ 2 := by
    nlinarith
  have h_norm_nonneg : 0 ≤ ‖p - q‖ := norm_nonneg _
  have h_rhs_nonneg : 0 ≤ 2 * sin (sdist p q / 2) := by nlinarith
  nlinarith [sq_eq_sq₀ h_norm_nonneg h_rhs_nonneg, h_sq_eq]

theorem pair_core (p q p' q' : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (dm ρ₁ ρ₂ : ℝ)
    (hdm : 0 ≤ dm ∧ dm ≤ π) (hpq : dm ≤ sdist p q) (h₁ : ‖p - p'‖ ≤ ρ₁) (h₂ : ‖q - q'‖ ≤ ρ₂) :
    2 * sin (dm / 2) ≤ ‖p' - q'‖ + ρ₁ + ρ₂ := by
  rcases hdm with ⟨hdm_left, hdm_right⟩
  have hsdist := Tammes15.sdist_mem_Icc p q
  rcases hsdist with ⟨hsdist_left, hsdist_right⟩
  have h_sin : 2 * sin (dm / 2) ≤ 2 * sin (sdist p q / 2) := by
    have h_nonneg_dm : 0 ≤ dm / 2 := by nlinarith
    have h_nonneg_sdist : 0 ≤ sdist p q / 2 := by nlinarith
    have h_le_pi_div_two_dm : dm / 2 ≤ π / 2 := by nlinarith
    have h_le_pi_div_two_sdist : sdist p q / 2 ≤ π / 2 := by nlinarith
    have hx₁ : -(π / 2) ≤ dm / 2 := by nlinarith
    have hxy : dm / 2 ≤ sdist p q / 2 := by nlinarith
    have hy₂ : sdist p q / 2 ≤ π / 2 := h_le_pi_div_two_sdist
    nlinarith [Real.sin_le_sin_of_le_of_le_pi_div_two hx₁ hy₂ hxy]
  have h_norm_sub : 2 * sin (sdist p q / 2) = ‖p - q‖ :=
    (Tammes15.norm_sub_eq_two_sin p q hp hq).symm
  have h_triangle : ‖p - q‖ ≤ ‖p - p'‖ + ‖p' - q'‖ + ‖q' - q‖ := by
    calc
      ‖p - q‖ = ‖(p - p') + (p' - q') + (q' - q)‖ := by
        congr 1
        abel
      _ ≤ ‖(p - p') + (p' - q')‖ + ‖q' - q‖ := norm_add_le _ _
      _ ≤ ‖p - p'‖ + ‖p' - q'‖ + ‖q' - q‖ := by nlinarith [norm_add_le (p - p') (p' - q')]
  have h_norm_symm : ‖q' - q‖ = ‖q - q'‖ := by
    rw [← norm_neg (q' - q), neg_sub]
  have h_bounds : ‖p - p'‖ + ‖p' - q'‖ + ‖q' - q‖ ≤ ρ₁ + ‖p' - q'‖ + ρ₂ := by
    nlinarith
  nlinarith

end Tammes15
