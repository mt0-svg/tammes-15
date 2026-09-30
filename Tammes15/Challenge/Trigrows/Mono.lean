import Tammes15.Challenge.Trigrows.Defs

/-!
# The monotonicity facts of Section 5

The monotonicity statements that Section 5 of the paper uses.
`gam_hasDerivAt_side` has the hypotheses
`0 < c < π` and `-1 < η < 1` (with `η ≠ ±1` alone it would be false where
`|η| > 1`, `arccos` being constant there); `rho_hasDerivAt_x` (for
`rho_concaveOn`) and `sine_rule_eta` (for `gam_hasDerivAt_side`) are steps of the proofs.
-/

open Real

namespace Tammes15

theorem rho_strictMonoOn_d (x : ℝ) (hx : 0 < x ∧ x < π) :
    StrictMonoOn (fun d => rho d x) (Set.Ioo 0 (π / 2)) := by
  rcases hx with ⟨hx_left, hx_right⟩
  have ht_pos : 0 < tan (x / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  intro d₁ hd₁ d₂ hd₂ hlt
  rcases hd₁ with ⟨hd₁_left, hd₁_right⟩
  rcases hd₂ with ⟨hd₂_left, hd₂_right⟩
  have hd₁_mem : d₁ ∈ Set.Icc (0 : ℝ) π := by
    constructor <;> linarith
  have hd₂_mem : d₂ ∈ Set.Icc (0 : ℝ) π := by
    constructor <;> linarith
  have hcos : cos d₂ < cos d₁ :=
    Real.strictAntiOn_cos hd₁_mem hd₂_mem hlt
  have hprod : cos d₂ * tan (x / 2) < cos d₁ * tan (x / 2) := by
    nlinarith
  have harctan : arctan (cos d₂ * tan (x / 2)) < arctan (cos d₁ * tan (x / 2)) :=
    Real.arctan_strictMono hprod
  dsimp [rho]
  linarith

theorem rho_strictAntiOn_x (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    StrictAntiOn (rho d) (Set.Ioo 0 π) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hcos_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  intro x hx y hy hxy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have hx2_div : x / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have hy2_div : y / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith
  have htan_lt : tan (x / 2) < tan (y / 2) :=
    Real.strictMonoOn_tan hx2_div hy2_div (by nlinarith)
  have h_mul_lt : cos d * tan (x / 2) < cos d * tan (y / 2) := by
    nlinarith
  have harctan_lt : arctan (cos d * tan (x / 2)) < arctan (cos d * tan (y / 2)) :=
    Real.arctan_strictMono h_mul_lt
  dsimp [rho]
  nlinarith

theorem rho_hasDerivAt_x (d x : ℝ) (hx : 0 < x ∧ x < π) :
    HasDerivAt (rho d) (-(cos d) / (cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2)) x := by
  rcases hx with ⟨hx_left, hx_right⟩
  have hcos_ne_zero : cos (x / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have h_tan_deriv : HasDerivAt (fun (x : ℝ) => tan (x / 2)) (1 / (2 * cos (x / 2) ^ 2)) x := by
    have h_tan_at : HasDerivAt tan (1 / cos (x / 2) ^ 2) (x / 2) := Real.hasDerivAt_tan hcos_ne_zero
    have h_half : HasDerivAt (fun (x : ℝ) => x / 2) (1/2) x := by
      have := hasDerivAt_id x
      simpa using this.div_const (2 : ℝ)
    have h_comp := HasDerivAt.comp x h_tan_at h_half
    convert h_comp using 1
    · ext y; simp
    · ring
  have h_g_deriv : HasDerivAt (fun (x : ℝ) => cos d * tan (x / 2)) (cos d * (1 / (2 * cos (x / 2) ^ 2))) x := by
    exact HasDerivAt.const_mul (cos d) h_tan_deriv
  have h_arctan_deriv : HasDerivAt (fun (x : ℝ) => arctan (cos d * tan (x / 2)))
      ((1 / (1 + (cos d * tan (x / 2)) ^ 2)) * (cos d * (1 / (2 * cos (x / 2) ^ 2)))) x := by
    have h_arctan_at : HasDerivAt arctan (1 / (1 + (cos d * tan (x / 2)) ^ 2)) (cos d * tan (x / 2)) :=
      Real.hasDerivAt_arctan _
    exact HasDerivAt.comp x h_arctan_at h_g_deriv
  have h_two_arctan : HasDerivAt (fun (x : ℝ) => (2 : ℝ) * arctan (cos d * tan (x / 2)))
      ((2 : ℝ) * ((1 / (1 + (cos d * tan (x / 2)) ^ 2)) * (cos d * (1 / (2 * cos (x / 2) ^ 2))))) x := by
    exact HasDerivAt.const_mul (2 : ℝ) h_arctan_deriv
  have h_const : HasDerivAt (fun (_ : ℝ) => π) 0 x := hasDerivAt_const _ _
  have h_sub : HasDerivAt (fun (x : ℝ) => π - (2 : ℝ) * arctan (cos d * tan (x / 2)))
      (0 - ((2 : ℝ) * ((1 / (1 + (cos d * tan (x / 2)) ^ 2)) * (cos d * (1 / (2 * cos (x / 2) ^ 2)))))) x :=
    HasDerivAt.sub h_const h_two_arctan
  have h_simplify : (0 - ((2 : ℝ) * ((1 / (1 + (cos d * tan (x / 2)) ^ 2)) * (cos d * (1 / (2 * cos (x / 2) ^ 2)))))) =
      -(cos d) / (cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2) := by
    rw [Real.tan_eq_sin_div_cos (x / 2)]
    field_simp [hcos_ne_zero]
    ring
  convert h_sub using 1
  · ext y; rfl
  · rw [h_simplify]

theorem rho_concaveOn (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    ConcaveOn ℝ (Set.Ioo 0 π) (rho d) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hc_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc_lt_one : cos d < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hd_pos
    simpa [Real.cos_zero] using this
  have h_one_minus_c_sq_pos : 0 < 1 - cos d ^ 2 := by nlinarith
  -- derivative formula on (0, π)
  have h_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) π, deriv (rho d) x = -(cos d) / (cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2) := by
    intro x hx
    have h_hasDeriv := rho_hasDerivAt_x d x ⟨hx.1, hx.2⟩
    rw [h_hasDeriv.deriv]
  -- denominator is positive on (0, π)
  have h_den_pos : ∀ x ∈ Set.Ioo (0 : ℝ) π, 0 < cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2 := by
    intro x hx
    rcases hx with ⟨hx_left, hx_right⟩
    have hx2_left : -(π / 2) < x / 2 := by linarith
    have hx2_right : x / 2 < π / 2 := by linarith
    have hcos_pos : 0 < cos (x / 2) := Real.cos_pos_of_mem_Ioo ⟨hx2_left, hx2_right⟩
    have hcos_sq_pos : 0 < cos (x / 2) ^ 2 := pow_pos hcos_pos 2
    have hsin_sq_nonneg : 0 ≤ sin (x / 2) ^ 2 := pow_two_nonneg _
    have hc_sq_nonneg : 0 ≤ cos d ^ 2 := pow_two_nonneg _
    nlinarith
  -- denominator is antitone on (0, π)
  have h_den_anti : AntitoneOn (fun x => cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2) (Set.Ioo (0 : ℝ) π) := by
    intro x hx y hy hxy
    rcases hx with ⟨hx_left, hx_right⟩
    rcases hy with ⟨hy_left, hy_right⟩
    have hx2_mem : x / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    have hy2_mem : y / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    have hx2_le_y2 : x / 2 ≤ y / 2 := by linarith
    have hsin_mono : MonotoneOn sin (Set.Icc (-(π / 2)) (π / 2)) :=
      Real.strictMonoOn_sin.monotoneOn
    have hsin_xy : sin (x / 2) ≤ sin (y / 2) := hsin_mono hx2_mem hy2_mem hx2_le_y2
    have hsin_nonneg_x : 0 ≤ sin (x / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin_nonneg_y : 0 ≤ sin (y / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin_sq_xy : sin (x / 2) ^ 2 ≤ sin (y / 2) ^ 2 := by
      have hneg : -sin (y / 2) ≤ sin (x / 2) := by linarith
      exact sq_le_sq' hneg hsin_xy
    have h_denom_eq : ∀ z : ℝ, cos (z / 2) ^ 2 + cos d ^ 2 * sin (z / 2) ^ 2 = 1 - (1 - cos d ^ 2) * sin (z / 2) ^ 2 := by
      intro z
      have h := Real.sin_sq_add_cos_sq (z / 2)
      nlinarith
    simp
    rw [h_denom_eq x, h_denom_eq y]
    nlinarith
  -- derivative is antitone on (0, π)
  have h_deriv_anti : AntitoneOn (deriv (rho d)) (Set.Ioo (0 : ℝ) π) := by
    intro x hx y hy hxy
    rw [h_deriv x hx, h_deriv y hy]
    have hDx_pos : 0 < cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2 := h_den_pos x hx
    have hDy_pos : 0 < cos (y / 2) ^ 2 + cos d ^ 2 * sin (y / 2) ^ 2 := h_den_pos y hy
    have hD_anti : cos (y / 2) ^ 2 + cos d ^ 2 * sin (y / 2) ^ 2 ≤ cos (x / 2) ^ 2 + cos d ^ 2 * sin (x / 2) ^ 2 :=
      h_den_anti hx hy hxy
    have h_neg_cos : -(cos d) < 0 := by linarith
    field_simp [hDx_pos.ne.symm, hDy_pos.ne.symm]
    nlinarith
  -- apply AntitoneOn.concaveOn_of_deriv
  have h_deriv_anti_interior : AntitoneOn (deriv (rho d)) (interior (Set.Ioo 0 π)) := by
    rw [interior_Ioo]
    exact h_deriv_anti
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioo 0 π) ?_ ?_ h_deriv_anti_interior
  · -- ContinuousOn (rho d) (Set.Ioo 0 π)
    have h_diff : DifferentiableOn ℝ (rho d) (Set.Ioo 0 π) := by
      intro x hx
      have h_hasDeriv := rho_hasDerivAt_x d x ⟨hx.1, hx.2⟩
      exact h_hasDeriv.differentiableAt.differentiableWithinAt
    exact h_diff.continuousOn
  · -- DifferentiableOn ℝ (rho d) (interior (Set.Ioo 0 π))
    rw [interior_Ioo]
    intro x hx
    have h_hasDeriv := rho_hasDerivAt_x d x ⟨hx.1, hx.2⟩
    exact h_hasDeriv.differentiableAt.differentiableWithinAt

theorem rho_rho (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    rho d (rho d x) = x := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hx with ⟨hx_pos, hx_lt⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hx2_lt_pi_div_two : x / 2 < π / 2 := by linarith
  have hc_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  have ht_pos : 0 < tan (x / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hx2_pos hx2_lt_pi_div_two
  have hct_pos : 0 < cos d * tan (x / 2) := mul_pos hc_pos ht_pos
  calc
    rho d (rho d x) = π - 2 * arctan (cos d * tan ((rho d x) / 2)) := rfl
    _ = π - 2 * arctan (cos d * tan ((π - 2 * arctan (cos d * tan (x / 2))) / 2)) := rfl
    _ = π - 2 * arctan (cos d * tan (π / 2 - arctan (cos d * tan (x / 2)))) := by ring
    _ = π - 2 * arctan (cos d * ((tan (arctan (cos d * tan (x / 2))))⁻¹)) := by
      rw [Real.tan_pi_div_two_sub]
    _ = π - 2 * arctan (cos d * ((cos d * tan (x / 2))⁻¹)) := by
      rw [Real.tan_arctan]
    _ = π - 2 * arctan (cos d * (1 / (cos d * tan (x / 2)))) := by ring
    _ = π - 2 * arctan (cos d / (cos d * tan (x / 2))) := by ring
    _ = π - 2 * arctan (1 / tan (x / 2)) := by
      field_simp [ne_of_gt hc_pos]
    _ = π - 2 * arctan ((tan (x / 2))⁻¹) := by ring
    _ = π - 2 * (π / 2 - arctan (tan (x / 2))) := by
      rw [Real.arctan_inv_of_pos ht_pos]
    _ = π - (π - 2 * arctan (tan (x / 2))) := by ring
    _ = 2 * arctan (tan (x / 2)) := by ring
    _ = 2 * (x / 2) := by rw [Real.arctan_tan (by linarith) hx2_lt_pi_div_two]
    _ = x := by ring

theorem rho_alpha (d : ℝ) (hd : 0 < d ∧ d < π / 2) : rho d (alpha d) = 2 * alpha d := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hcos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, hdlt⟩
  have hcos_lt_one : cos d < 1 := by
    have hcos_lt : cos d < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hdpos
    simpa using hcos_lt
  have h_one_plus_cos_pos : 0 < 1 + cos d := by linarith
  have h_cos_div_pos : 0 < cos d / (1 + cos d) := div_pos hcos_pos h_one_plus_cos_pos
  have h_cos_div_lt_one : cos d / (1 + cos d) < 1 := by
    refine (div_lt_one ?_).mpr ?_
    · linarith
    · linarith
  have h_cos_div_gt_neg_one : -1 < cos d / (1 + cos d) := by
    linarith [h_cos_div_pos]
  set c := cos d with hc
  set α := alpha d with hα
  have hcos_α : cos α = c / (1 + c) := by
    rw [hα, alpha, Real.cos_arccos (by linarith) (by linarith)]
  have hsin_α_pos : 0 < sin α := by
    rw [hα, alpha, Real.sin_arccos]
    refine Real.sqrt_pos.mpr ?_
    have h : c / (1 + c) < 1 := by
      simpa [hc] using h_cos_div_lt_one
    have hsq : (c / (1 + c)) ^ 2 < 1 := by
      nlinarith
    linarith
  have hsin_α_ne_zero : sin α ≠ 0 := by linarith
  -- Key identity: tan(α/2) = (1 - cos α) / sin α
  have h_tan_half : tan (α / 2) = (1 - cos α) / sin α := by
    have hcos_two_mul : cos α = 2 * cos (α / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (α / 2)
      -- this : cos (2*(α/2)) = 2*cos²(α/2) - 1
      simpa [show 2*(α/2) = α by ring] using this
    have h_denom : 2 * cos (α / 2) ^ 2 = 1 + cos α := by linarith
    calc
      tan (α / 2) = sin (α / 2) / cos (α / 2) := by rw [Real.tan_eq_sin_div_cos]
      _ = (2 * sin (α / 2) * cos (α / 2)) / (2 * cos (α / 2) ^ 2) := by
        field_simp
      _ = sin α / (2 * cos (α / 2) ^ 2) := by
        rw [← Real.sin_two_mul (α / 2), show 2*(α/2) = α by ring]
      _ = sin α / (1 + cos α) := by rw [h_denom]
      _ = (1 - cos α) / sin α := by
        have hcos_α_pos : 0 < cos α := by
          rw [hcos_α]
          exact div_pos hcos_pos h_one_plus_cos_pos
        field_simp [show 1 + cos α ≠ 0 from by linarith, hsin_α_ne_zero]
        nlinarith [Real.sin_sq_add_cos_sq α]
  -- Now compute c * tan(α/2)
  have h_key : c * tan (α / 2) = cos α / sin α := by
    rw [h_tan_half, hcos_α]
    field_simp [hsin_α_ne_zero, show 1 + c ≠ 0 from by linarith]
    ring
  -- cos α / sin α = cot α = tan(π/2 - α)
  have h_cot : cos α / sin α = tan (π / 2 - α) := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos]
    field_simp [hsin_α_ne_zero]
  -- Therefore c * tan(α/2) = tan(π/2 - α)
  have h_tan_eq : c * tan (α / 2) = tan (π / 2 - α) := by
    rw [h_key, h_cot]
  -- Now apply arctan to both sides
  have hαpos : 0 < α := by
    rw [hα, alpha]
    exact (Real.arccos_pos.mpr h_cos_div_lt_one)
  have hα_lt_pi_div_two : α < π / 2 := by
    rw [hα, alpha]
    -- arccos x < π/2 ↔ 0 < x
    rw [Real.arccos_lt_pi_div_two]
    exact h_cos_div_pos
  have h_arctan : arctan (c * tan (α / 2)) = π / 2 - α := by
    rw [h_tan_eq]
    apply Real.arctan_tan
    · -- -(π/2) < π/2 - α
      linarith
    · -- π/2 - α < π/2
      linarith
  -- Finally, compute rho d α
  rw [rho, hα, ← hc, h_arctan]
  ring

theorem cot_mul_cot_rho (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    cos d = cot (x / 2) * cot (rho d x / 2) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hx with ⟨hx_pos, hx_lt⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hx2_lt_pi_div_2 : x / 2 < π / 2 := by linarith
  have hx2_mem_Ioo : x / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith
  have hx2_mem_Ioo_pi : x / 2 ∈ Set.Ioo (0 : ℝ) π := by
    constructor <;> linarith
  have hsin_pos : 0 < sin (x / 2) := Real.sin_pos_of_mem_Ioo hx2_mem_Ioo_pi
  have hcos_pos : 0 < cos (x / 2) := Real.cos_pos_of_mem_Ioo hx2_mem_Ioo
  have htan_pos : 0 < tan (x / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin_pos hcos_pos
  have htan_ne_zero : tan (x / 2) ≠ 0 := by linarith
  have h_cot_pi_div_two_sub (y : ℝ) : cot (π / 2 - y) = tan y := by
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
      Real.tan_eq_sin_div_cos]
  have h_rho_div_two : rho d x / 2 = π / 2 - arctan (cos d * tan (x / 2)) := by
    dsimp [rho]
    ring
  calc
    cos d = cos d * 1 := by ring
    _ = cos d * (cot (x / 2) * tan (x / 2)) := by
      rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
      field_simp [hsin_pos.ne.symm, hcos_pos.ne.symm]
    _ = (cos d * tan (x / 2)) * cot (x / 2) := by ring
    _ = tan (arctan (cos d * tan (x / 2))) * cot (x / 2) := by rw [Real.tan_arctan]
    _ = cot (π / 2 - arctan (cos d * tan (x / 2))) * cot (x / 2) := by rw [h_cot_pi_div_two_sub]
    _ = cot (rho d x / 2) * cot (x / 2) := by rw [h_rho_div_two]
    _ = cot (x / 2) * cot (rho d x / 2) := by ring

theorem Ssum_strictMonoOn : StrictMonoOn Ssum (Set.Ioo 0 (π / 2)) := by
  intro a ha b hb hlt
  have ha' : a ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rcases ha with ⟨ha1, ha2⟩
    refine ⟨by linarith, by linarith⟩
  have hb' : b ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rcases hb with ⟨hb1, hb2⟩
    refine ⟨by linarith, by linarith⟩
  have hcos_pos_a : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ha'
  have hcos_pos_b : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo hb'
  have hcos_lt : Real.cos b < Real.cos a := by
    have hanti : StrictAntiOn Real.cos (Set.Icc (0 : ℝ) Real.pi) := Real.strictAntiOn_cos
    have ha_mem : a ∈ Set.Icc (0 : ℝ) Real.pi := by
      rcases ha with ⟨ha1, ha2⟩
      have hpi_pos : 0 < π := by exact Real.pi_pos
      constructor
      · linarith
      · have : π / 2 < π := by linarith [Real.pi_pos]
        linarith
    have hb_mem : b ∈ Set.Icc (0 : ℝ) Real.pi := by
      rcases hb with ⟨hb1, hb2⟩
      have hpi_pos : 0 < π := by exact Real.pi_pos
      constructor
      · linarith
      · have : π / 2 < π := by linarith [Real.pi_pos]
        linarith
    exact hanti ha_mem hb_mem hlt
  have hsqrt_pos_a : 0 < Real.sqrt (Real.cos a) := Real.sqrt_pos.mpr hcos_pos_a
  have hsqrt_pos_b : 0 < Real.sqrt (Real.cos b) := Real.sqrt_pos.mpr hcos_pos_b
  have hsqrt_lt : Real.sqrt (Real.cos b) < Real.sqrt (Real.cos a) :=
    Real.sqrt_lt_sqrt (by linarith) hcos_lt
  have hone_div_lt : 1 / Real.sqrt (Real.cos a) < 1 / Real.sqrt (Real.cos b) := by
    rw [one_div_lt_one_div hsqrt_pos_a hsqrt_pos_b]
    exact hsqrt_lt
  have harctan_lt : Real.arctan (1 / Real.sqrt (Real.cos a)) < Real.arctan (1 / Real.sqrt (Real.cos b)) :=
    Real.arctan_strictMono hone_div_lt
  dsimp [Ssum]
  nlinarith

theorem rhombus_d_monotoneOn_x (y : ℝ) (hy : 0 < y ∧ y < π) :
    MonotoneOn (fun x => arccos (cot (x / 2) * cot (y / 2))) (Set.Ioo 0 π) := by
  rcases hy with ⟨hy_pos, hy_lt_pi⟩
  have hy2_pos : 0 < y / 2 := by linarith
  have hy2_lt_pi_div_two : y / 2 < π / 2 := by linarith
  have hcot_y_pos : 0 < cot (y / 2) := by
    have htan_pos : 0 < tan (y / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two hy2_pos hy2_lt_pi_div_two
    rw [← Real.tan_inv_eq_cot]
    exact inv_pos.mpr htan_pos
  have h_cot_anti : AntitoneOn (fun x => cot (x / 2)) (Set.Ioo 0 π) := by
    intro a ha b hb hle
    rcases ha with ⟨ha_left, ha_right⟩
    rcases hb with ⟨hb_left, hb_right⟩
    have ha2_pos : 0 < a / 2 := by linarith
    have ha2_lt_pi_div_two : a / 2 < π / 2 := by linarith
    have hb2_pos : 0 < b / 2 := by linarith
    have hb2_lt_pi_div_two : b / 2 < π / 2 := by linarith
    have htan_le : tan (a / 2) ≤ tan (b / 2) := by
      by_cases h_eq : a / 2 = b / 2
      · rw [h_eq]
      · have h_lt : a / 2 < b / 2 := by
          by_contra! hge
          have heq : a / 2 = b / 2 := by linarith
          exact h_eq heq
        have hmem_a : a / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
          constructor <;> linarith
        have hmem_b : b / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
          constructor <;> linarith
        exact le_of_lt (Real.strictMonoOn_tan hmem_a hmem_b h_lt)
    have htan_pos_a : 0 < tan (a / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two ha2_pos ha2_lt_pi_div_two
    have htan_pos_b : 0 < tan (b / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two hb2_pos hb2_lt_pi_div_two
    have h_one_div : 1 / tan (b / 2) ≤ 1 / tan (a / 2) :=
      (one_div_le_one_div htan_pos_b htan_pos_a).mpr htan_le
    have h_cot_eq : ∀ x, cot x = 1 / tan x := by
      intro x
      rw [← Real.tan_inv_eq_cot, inv_eq_one_div]
    dsimp
    rw [h_cot_eq (a/2), h_cot_eq (b/2)]
    exact h_one_div
  have h_mul_anti : AntitoneOn (fun x => cot (x / 2) * cot (y / 2)) (Set.Ioo 0 π) := by
    intro a ha b hb hle
    have hcot := h_cot_anti ha hb hle
    have hpos : 0 ≤ cot (y / 2) := le_of_lt hcot_y_pos
    exact mul_le_mul_of_nonneg_right hcot hpos
  exact Real.antitone_arccos.comp_antitoneOn h_mul_anti

theorem alpha_strictMonoOn : StrictMonoOn alpha (Set.Ioo 0 (π / 2)) := by
  -- The function t/(1+t) is strictly increasing on (0, ∞)
  have h_div_strictMono : StrictMonoOn (fun t : ℝ => t / (1 + t)) (Set.Ioi 0) := by
    intro a ha b hb hlt
    have ha_val : 0 < a := ha
    have hb_val : 0 < b := hb
    have ha_pos : 0 < 1 + a := by linarith
    have hb_pos : 0 < 1 + b := by linarith
    -- a/(1+a) < b/(1+b) ↔ a*(1+b) < b*(1+a) ↔ a + ab < b + ab ↔ a < b
    field_simp [ha_pos.ne', hb_pos.ne']
    nlinarith
  -- Restrict to (0, 1)
  have h_div_strictMono_Ioo : StrictMonoOn (fun t : ℝ => t / (1 + t)) (Set.Ioo (0 : ℝ) 1) :=
    h_div_strictMono.mono (Set.Ioo_subset_Ioi_self)
  -- cos is strictly decreasing on (0, π/2) (inherited from [0, π])
  have h_cos_strictAnti : StrictAntiOn Real.cos (Set.Ioo 0 (π / 2)) := by
    intro a ha b hb hlt
    have ha' : a ∈ Set.Icc (0 : ℝ) π := by
      rcases ha with ⟨haL, haR⟩
      exact ⟨by linarith, by linarith [pi_pos]⟩
    have hb' : b ∈ Set.Icc (0 : ℝ) π := by
      rcases hb with ⟨hbL, hbR⟩
      exact ⟨by linarith, by linarith [pi_pos]⟩
    exact Real.strictAntiOn_cos ha' hb' hlt
  -- cos maps (0, π/2) into (0, 1)
  have h_cos_maps : Set.MapsTo Real.cos (Set.Ioo 0 (π / 2)) (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    rcases hx with ⟨hxL, hxR⟩
    have hcos_pos : 0 < Real.cos x := by
      apply Real.cos_pos_of_mem_Ioo
      refine ⟨by linarith, ?_⟩
      linarith
    have hcos_lt_one : Real.cos x < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) hxL
      simpa [Real.cos_zero] using this
    exact ⟨hcos_pos, hcos_lt_one⟩
  -- t/(1+t) maps (0, 1) into [-1, 1]
  have h_div_maps : Set.MapsTo (fun t : ℝ => t / (1 + t)) (Set.Ioo (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    rcases hx with ⟨hxL, hxR⟩
    have hpos : 0 < 1 + x := by linarith
    have h_lt_one : x / (1 + x) < 1 := by
      apply (div_lt_one hpos).mpr
      linarith
    have h_gt_neg_one : -1 ≤ x / (1 + x) := by
      have : 0 ≤ x / (1 + x) := by positivity
      linarith
    exact ⟨h_gt_neg_one, by linarith⟩
  -- Compose: (arccos ∘ (t/(1+t))) is StrictAntiOn on (0, 1)
  have h_arccos_div_strictAnti : StrictAntiOn (Real.arccos ∘ (fun t : ℝ => t / (1 + t))) (Set.Ioo (0 : ℝ) 1) :=
    Real.strictAntiOn_arccos.comp_strictMonoOn h_div_strictMono_Ioo h_div_maps
  -- Compose: alpha = (arccos ∘ (t/(1+t))) ∘ cos is StrictMonoOn on (0, π/2)
  have h_alpha_strictMono : StrictMonoOn (Real.arccos ∘ (fun t : ℝ => t / (1 + t)) ∘ Real.cos) (Set.Ioo 0 (π / 2)) :=
    h_arccos_div_strictAnti.comp h_cos_strictAnti h_cos_maps
  -- alpha equals the composition
  convert h_alpha_strictMono using 1
  ext d
  simp [alpha]

theorem alpha_inverse (a : ℝ) (ha : π / 3 < a ∧ a < π / 2) :
    alpha (arccos (cos a / (1 - cos a))) = a := by
  rcases ha with ⟨h_left, h_right⟩
  have ha_nonneg : 0 ≤ a := by linarith
  have ha_le_pi : a ≤ π := by linarith
  have hcos_pos : 0 < cos a := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hcos_lt_half : cos a < 1 / 2 := by
    have h : cos a < cos (π / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h_left
    rw [Real.cos_pi_div_three] at h
    exact h
  have h_one_minus_cos_pos : 0 < 1 - cos a := by linarith
  set t := cos a / (1 - cos a) with ht
  have ht_pos : 0 < t := div_pos hcos_pos h_one_minus_cos_pos
  have ht_lt_one : t < 1 := by
    rw [ht]
    exact (div_lt_one h_one_minus_cos_pos).mpr (by linarith)
  have ht_range : -1 ≤ t ∧ t ≤ 1 := ⟨by linarith, by linarith⟩
  have hcos_arccos_t : cos (arccos t) = t := Real.cos_arccos ht_range.1 ht_range.2
  have h_t_div : t / (1 + t) = cos a := by
    rw [ht]
    field_simp [h_one_minus_cos_pos.ne']
    ring
  calc
    alpha (arccos t) = arccos (cos (arccos t) / (1 + cos (arccos t))) := rfl
    _ = arccos (t / (1 + t)) := by rw [hcos_arccos_t]
    _ = arccos (cos a) := by rw [h_t_div]
    _ = a := Real.arccos_cos ha_nonneg ha_le_pi

theorem hrad_strictMonoOn : StrictMonoOn hrad (Set.Ioo 0 (π / 2)) := by
  have harccos_anti : StrictAntiOn Real.arccos (Set.Icc (-1 : ℝ) 1) := Real.strictAntiOn_arccos
  -- cos is positive on (0, π/2)
  have hcos_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : 0 < cos x := by
    rcases hx with ⟨hx1, hx2⟩
    have hx' : x ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    exact Real.cos_pos_of_mem_Ioo hx'
  -- cos(d/2) is positive on (0, π/2)
  have hcos_half_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : 0 < cos (x / 2) := by
    rcases hx with ⟨hx1, hx2⟩
    have hx' : x / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    exact Real.cos_pos_of_mem_Ioo hx'
  -- The ratio cos d / cos(d/2) is positive on (0, π/2)
  have hcos_ratio_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : 0 < cos x / cos (x / 2) :=
    div_pos (hcos_pos hx) (hcos_half_pos hx)
  -- The ratio cos d / cos(d/2) is < 1 on (0, π/2)
  have hcos_ratio_lt_one {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : cos x / cos (x / 2) < 1 := by
    rcases hx with ⟨hx1, hx2⟩
    have hcos_lt : cos x < cos (x / 2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    exact (div_lt_one (hcos_half_pos ⟨hx1, hx2⟩)).mpr hcos_lt
  -- The ratio f(d) = cos d / cos(d/2) is strictly decreasing on (0, π/2)
  have hcos_ratio_anti : StrictAntiOn (λ d => cos d / cos (d / 2)) (Set.Ioo 0 (π / 2)) := by
    intro x hx y hy hxy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    -- Double-angle: cos d = 2 cos²(d/2) - 1
    have hcosx_eq : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
      calc
        cos x = cos (2 * (x / 2)) := by ring_nf
        _ = 2 * cos (x / 2) ^ 2 - 1 := Real.cos_two_mul (x / 2)
    have hcosy_eq : cos y = 2 * cos (y / 2) ^ 2 - 1 := by
      calc
        cos y = cos (2 * (y / 2)) := by ring_nf
        _ = 2 * cos (y / 2) ^ 2 - 1 := Real.cos_two_mul (y / 2)
    -- cos is strictly decreasing on [0, π], so cos(y/2) < cos(x/2) since x/2 < y/2
    have hcos_half_anti : cos (y / 2) < cos (x / 2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have hcx_pos : 0 < cos (x / 2) := hcos_half_pos ⟨hx1, hx2⟩
    have hcy_pos : 0 < cos (y / 2) := hcos_half_pos ⟨hy1, hy2⟩
    -- Goal: (λ d => cos d / cos (d/2)) y < (λ d => cos d / cos (d/2)) x
    -- Simplify the lambda applications
    simp
    -- Goal: cos y / cos (y/2) < cos x / cos (x/2)
    rw [hcosy_eq, hcosx_eq]
    -- Goal: (2*c_y² - 1)/c_y < (2*c_x² - 1)/c_x  where c_x = cos(x/2), c_y = cos(y/2)
    -- Cross-multiply (both denominators positive)
    field_simp [hcx_pos.ne.symm, hcy_pos.ne.symm]
    -- Goal: (2*c_y² - 1)*c_x < (2*c_x² - 1)*c_y  where c_x = cos(x/2), c_y = cos(y/2)
    -- Compute the difference: RHS - LHS = (c_x - c_y)*(2*c_x*c_y + 1) > 0
    have h_diff : (2 * cos (x / 2) ^ 2 - 1) * cos (y / 2) - (2 * cos (y / 2) ^ 2 - 1) * cos (x / 2)
        = (cos (x / 2) - cos (y / 2)) * (2 * cos (x / 2) * cos (y / 2) + 1) := by
      ring_nf
    have h_pos : 0 < (2 * cos (x / 2) ^ 2 - 1) * cos (y / 2) - (2 * cos (y / 2) ^ 2 - 1) * cos (x / 2) := by
      rw [h_diff]
      have h1 : 0 < cos (x / 2) - cos (y / 2) := by linarith
      have h2 : 0 < 2 * cos (x / 2) * cos (y / 2) + 1 := by
        have : 0 < 2 * cos (x / 2) * cos (y / 2) := by
          positivity
        linarith
      exact mul_pos h1 h2
    linarith
  -- The ratio maps into [-1, 1]
  have h_maps_to : Set.MapsTo (λ d => cos d / cos (d / 2)) (Set.Ioo 0 (π / 2)) (Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    have hpos : 0 < cos x / cos (x / 2) := hcos_ratio_pos hx
    have hlt1 : cos x / cos (x / 2) < 1 := hcos_ratio_lt_one hx
    exact ⟨by linarith, by linarith⟩
  -- arccos is strictly decreasing on [-1, 1], so the composition is strictly increasing
  have h := StrictAntiOn.comp harccos_anti hcos_ratio_anti h_maps_to
  -- h : StrictMonoOn (Real.arccos ∘ (λ d => cos d / cos (d / 2))) (Set.Ioo 0 (π / 2))
  -- hrad d = arccos (cos d / cos (d / 2)) = (Real.arccos ∘ (λ d => cos d / cos (d / 2))) d
  unfold hrad
  exact h

theorem hrad_bounds (d : ℝ) (hd : 0 < d ∧ d < π / 2) : d / 2 < hrad d ∧ hrad d < d := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hd_nonneg : 0 ≤ d := by linarith
  have hd_div2_pos : 0 < d / 2 := by linarith
  have hd_div2_nonneg : 0 ≤ d / 2 := by linarith
  have hd_le_pi : d ≤ π := by
    have h : π / 2 < π := by linarith [Real.pi_pos]
    linarith
  have hd_div2_le_pi : d / 2 ≤ π := by
    have h : π / 2 < π := by linarith [Real.pi_pos]
    linarith
  have hcos_d_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos_d_div2_pos : 0 < cos (d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos_d_div2_lt_one : cos (d / 2) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      (le_refl 0) (by linarith) hd_div2_pos
    simpa [cos_zero] using this
  have hcos_d_lt_one : cos d < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      (le_refl 0) hd_lt.le hd_pos
    simpa [cos_zero] using this
  have h_cos_d_lt_cos_div2 : cos d < cos (d / 2) := by
    have h_lt : d / 2 < d := by linarith
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hd_div2_nonneg hd_le_pi h_lt
  have h_cos_sq_half : cos (d / 2) * cos (d / 2) = (1 + cos d) / 2 := by
    have h := Real.cos_two_mul (d / 2)
    have h' : 2 * (d / 2) = d := by ring
    rw [h'] at h
    -- h: cos d = 2 * cos(d/2)^2 - 1
    -- So 2 * cos(d/2)^2 = cos d + 1
    -- And cos(d/2)^2 = cos(d/2) * cos(d/2)
    have hsq : cos (d / 2) ^ 2 = cos (d / 2) * cos (d / 2) := by ring
    rw [hsq] at h
    linarith
  have harccos_cos_d : arccos (cos d) = d :=
    Real.arccos_cos hd_nonneg hd_le_pi
  have harccos_cos_div2 : arccos (cos (d / 2)) = d / 2 :=
    Real.arccos_cos hd_div2_nonneg hd_div2_le_pi
  have h_hrad_def : hrad d = arccos (cos d / cos (d / 2)) := rfl
  -- First inequality: hrad d < d
  have h_lt : hrad d < d := by
    rw [h_hrad_def]
    calc
      arccos (cos d / cos (d / 2)) < arccos (cos d) := by
        refine Real.arccos_lt_arccos ?_ ?_ ?_
        · -- -1 ≤ cos d
          exact le_trans (by norm_num) hcos_d_pos.le
        · -- cos d < cos d / cos(d/2)
          -- Equivalent to cos d * cos(d/2) < cos d, i.e., cos(d/2) < 1
          have h : cos d * cos (d / 2) < cos d := by nlinarith
          exact (lt_div_iff₀ hcos_d_div2_pos).mpr h
        · -- cos d / cos(d/2) ≤ 1
          exact (div_le_one hcos_d_div2_pos).mpr h_cos_d_lt_cos_div2.le
      _ = d := by rw [harccos_cos_d]
  -- Second inequality: d/2 < hrad d
  have h_gt : d / 2 < hrad d := by
    rw [h_hrad_def]
    calc
      d / 2 = arccos (cos (d / 2)) := by rw [harccos_cos_div2]
      _ < arccos (cos d / cos (d / 2)) := by
        refine Real.arccos_lt_arccos ?_ ?_ ?_
        · -- -1 ≤ cos d / cos(d/2)
          have hpos' : 0 ≤ cos d / cos (d / 2) := by
            exact div_nonneg hcos_d_pos.le hcos_d_div2_pos.le
          exact le_trans (by norm_num) hpos'
        · -- cos d / cos(d/2) < cos(d/2)
          -- Equivalent to cos d < cos(d/2) * cos(d/2) = (1 + cos d)/2, i.e., cos d < 1
          have h : cos d < cos (d / 2) * cos (d / 2) := by
            rw [h_cos_sq_half]
            nlinarith
          exact (div_lt_iff₀ hcos_d_div2_pos).mpr h
        · -- cos(d/2) ≤ 1
          exact Real.cos_le_one _
  exact And.intro h_gt h_lt

theorem ebase_strictMonoOn (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    StrictMonoOn (ebase d) (Set.Ioc 0 π) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hpi_pos : 0 < π := Real.pi_pos
  have hsin_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  have hsin_lt_one : sin d < 1 := by
    have : sin d < sin (π / 2) := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hdlt
    simpa [Real.sin_pi_div_two] using this
  intro x hx y hy hxy
  rcases hx with ⟨hx_left, hx_right⟩
  rcases hy with ⟨hy_left, hy_right⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hy2_pos : 0 < y / 2 := by linarith
  have hx2_lt_y2 : x / 2 < y / 2 := by linarith
  have hy2_le_pi2 : y / 2 ≤ π / 2 := by linarith
  have hx2_le_pi2 : x / 2 ≤ π / 2 := by linarith
  have hx2_nonneg : 0 ≤ x / 2 := by linarith
  have hy2_nonneg : 0 ≤ y / 2 := by linarith
  -- sin is strictly increasing on [0, π/2]
  have hsin_x2_lt_sin_y2 : sin (x / 2) < sin (y / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hy2_le_pi2 hx2_lt_y2
  have hsin_x2_pos : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx2_pos (by linarith)
  have hsin_y2_pos : 0 < sin (y / 2) := sin_pos_of_pos_of_lt_pi hy2_pos (by linarith)
  have hsin_y2_le_one : sin (y / 2) ≤ 1 := sin_le_one (y / 2)
  -- sin d * sin(x/2) < sin d * sin(y/2)
  have hprod_lt : sin d * sin (x / 2) < sin d * sin (y / 2) := by
    nlinarith
  have hprod_pos : 0 < sin d * sin (x / 2) := by nlinarith
  have hprod_le_one : sin d * sin (y / 2) ≤ 1 := by
    nlinarith
  have hprod_ge_neg_one : -1 ≤ sin d * sin (x / 2) := by
    nlinarith
  -- arcsin is strictly increasing on [-1, 1]
  have harcsin_lt : arcsin (sin d * sin (x / 2)) < arcsin (sin d * sin (y / 2)) :=
    Real.arcsin_lt_arcsin hprod_ge_neg_one hprod_lt hprod_le_one
  -- multiply by 2
  unfold ebase
  nlinarith

theorem ebase_symm (d u : ℝ) : ebase d (2 * π - u) = ebase d u := by
  unfold ebase
  have h : (2 * π - u) / 2 = π - u / 2 := by ring
  rw [h]
  rw [Real.sin_pi_sub]

theorem bangle_strictAntiOn (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    StrictAntiOn (bangle d) (Set.Ioc 0 π) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hcos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, hd_lt⟩
  intro x hx y hy hlt
  rcases hx with ⟨hx_left, hx_right⟩
  rcases hy with ⟨hy_left, hy_right⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hy2_pos : 0 < y / 2 := by linarith
  have hx2_lt_pi : x / 2 < π := by linarith
  have hy2_lt_pi : y / 2 < π := by linarith
  have hsin_x2_pos : 0 < sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi hx2_pos hx2_lt_pi
  have hsin_y2_pos : 0 < sin (y / 2) := Real.sin_pos_of_pos_of_lt_pi hy2_pos hy2_lt_pi
  have hsub_pos : 0 < y / 2 - x / 2 := by linarith
  have hsub_lt_pi : y / 2 - x / 2 < π := by linarith
  have hsin_sub_pos : 0 < sin (y / 2 - x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hsub_pos hsub_lt_pi
  have hkey_mul : cos (y / 2) * sin (x / 2) < cos (x / 2) * sin (y / 2) := by
    have h := hsin_sub_pos
    rw [Real.sin_sub] at h
    linarith
  have hkey_div : cos (y / 2) / (cos d * sin (y / 2)) < cos (x / 2) / (cos d * sin (x / 2)) := by
    field_simp [hcos_pos.ne.symm, hsin_x2_pos.ne.symm, hsin_y2_pos.ne.symm]
    simpa [mul_comm] using hkey_mul
  dsimp [bangle]
  exact (Real.arctan_lt_arctan_iff.mpr hkey_div)

theorem napier_isosceles (d u : ℝ) (hd : 0 < d ∧ d < π / 2) (hu : 0 < u ∧ u < π) :
    cos d = cot (u / 2) * cot (bangle d u) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hu with ⟨hu_pos, hu_lt⟩
  have hcosd_pos : cos d > 0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin_half_u_pos : sin (u / 2) > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hcos_half_u_pos : cos (u / 2) > 0 :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hcot_bangle : cot (bangle d u) = (cos (u / 2) / (cos d * sin (u / 2)))⁻¹ := by
    dsimp [bangle]
    rw [← Real.tan_inv_eq_cot, Real.tan_arctan]
  calc
    cos d = (cos (u / 2) / sin (u / 2)) * ((cos d * sin (u / 2)) / cos (u / 2)) := by
      field_simp [hcos_half_u_pos.ne', hsin_half_u_pos.ne']
    _ = cot (u / 2) * ((cos (u / 2) / (cos d * sin (u / 2)))⁻¹) := by
      rw [Real.cot_eq_cos_div_sin]
      field_simp [hcos_half_u_pos.ne', hsin_half_u_pos.ne', hcosd_pos.ne']
    _ = cot (u / 2) * cot (bangle d u) := by rw [hcot_bangle]

/-- (T7) bound, non-increasing in the corner `u₁` (deep.rs `longdiag_lb` reads it at `u.hi`). -/
theorem T7_bound_antitoneOn (d : ℝ) (hd : 0 < d ∧ d < π / 2) :
    AntitoneOn (fun u => bangle d u + arccos (min 1 (cot d * tan (ebase d u / 2))))
      (Set.Ioc 0 π) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hcosd_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hd_lt_pi : d < π := by linarith [Real.pi_pos]
  have hsin_pos : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hdpos hd_lt_pi
  have hcotd_pos : 0 < cot d := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_pos hcosd_pos hsin_pos
  -- Part 1: bangle d is antitone on (0, π]
  have hbangle_anti : AntitoneOn (fun u => bangle d u) (Set.Ioc 0 π) := by
    intro u₁ hu₁ u₂ hu₂ hle
    rcases hu₁ with ⟨hu₁pos, hu₁le⟩
    rcases hu₂ with ⟨hu₂pos, hu₂le⟩
    dsimp [bangle]
    have hu₁_half_pos : 0 < u₁ / 2 := by linarith
    have hu₂_half_pos : 0 < u₂ / 2 := by linarith
    have hsin1_pos : 0 < sin (u₁ / 2) := Real.sin_pos_of_pos_of_lt_pi hu₁_half_pos (by linarith [Real.pi_pos])
    have hsin2_pos : 0 < sin (u₂ / 2) := Real.sin_pos_of_pos_of_lt_pi hu₂_half_pos (by linarith [Real.pi_pos])
    -- Key inequality: cos(u₂/2)*sin(u₁/2) ≤ cos(u₁/2)*sin(u₂/2)
    have h_cross : cos (u₂ / 2) * sin (u₁ / 2) ≤ cos (u₁ / 2) * sin (u₂ / 2) := by
      have hsub_nonpos : u₁ / 2 - u₂ / 2 ≤ 0 := by linarith
      have hsub_ge_neg_pi : -π ≤ u₁ / 2 - u₂ / 2 := by
        have : u₂ / 2 ≤ π / 2 := by linarith
        linarith
      have hsin_sub_nonpos : sin (u₁ / 2 - u₂ / 2) ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le hsub_nonpos hsub_ge_neg_pi
      rw [Real.sin_sub] at hsin_sub_nonpos
      linarith
    -- Convert to division inequality
    have h_div_ineq : cos (u₂ / 2) / (cos d * sin (u₂ / 2)) ≤ cos (u₁ / 2) / (cos d * sin (u₁ / 2)) := by
      calc
        cos (u₂ / 2) / (cos d * sin (u₂ / 2)) = (cos (u₂ / 2) * sin (u₁ / 2)) / ((cos d * sin (u₂ / 2)) * sin (u₁ / 2)) := by
          field_simp [hsin1_pos.ne.symm]
        _ ≤ (cos (u₁ / 2) * sin (u₂ / 2)) / ((cos d * sin (u₂ / 2)) * sin (u₁ / 2)) := by
          refine div_le_div_of_nonneg_right h_cross ?_
          positivity
        _ = cos (u₁ / 2) / (cos d * sin (u₁ / 2)) := by
          field_simp [hsin2_pos.ne.symm]
    exact (Real.arctan_le_arctan_iff.mpr h_div_ineq)
  -- Part 2: arccos(min 1 (cot d * tan (ebase d u / 2))) is antitone on (0, π]
  have harccos_anti : AntitoneOn (fun u => arccos (min 1 (cot d * tan (ebase d u / 2)))) (Set.Ioc 0 π) := by
    intro u₁ hu₁ u₂ hu₂ hle
    rcases hu₁ with ⟨hu₁pos, hu₁le⟩
    rcases hu₂ with ⟨hu₂pos, hu₂le⟩
    -- Helper: arcsin(sin d * sin(u/2)) is in Ioo (-(π/2)) (π/2)
    have h_arcsin_range (u : ℝ) (hu_pos : 0 < u) (hu_le : u ≤ π) : arcsin (sin d * sin (u / 2)) ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      have hu_half_pos : 0 < u / 2 := by linarith
      have hsin_half_nonneg : 0 ≤ sin (u / 2) := by
        have hu_half_lt_pi : u / 2 < π := by linarith [Real.pi_pos]
        exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hu_half_pos hu_half_lt_pi)
      have hprod_lt_one : sin d * sin (u / 2) < 1 := by
        have hsin_d_lt_one : sin d < 1 := by
          have : sin d < sin (π / 2) := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hdlt
          simpa [Real.sin_pi_div_two] using this
        have hsin_half_le_one : sin (u / 2) ≤ 1 := Real.sin_le_one _
        calc
          sin d * sin (u / 2) ≤ sin d * 1 := mul_le_mul_of_nonneg_left hsin_half_le_one (by linarith)
          _ = sin d := by ring
          _ < 1 := hsin_d_lt_one
      have hprod_gt_neg_one : -1 < sin d * sin (u / 2) := by nlinarith
      have h_low : -(π / 2) < arcsin (sin d * sin (u / 2)) := by
        rw [Real.neg_pi_div_two_lt_arcsin]
        exact hprod_gt_neg_one
      have h_high : arcsin (sin d * sin (u / 2)) < π / 2 := by
        rw [Real.arcsin_lt_pi_div_two]
        exact hprod_lt_one
      exact ⟨h_low, h_high⟩
    -- Monotonicity of ebase d u / 2
    have hebase_mono : ebase d u₁ / 2 ≤ ebase d u₂ / 2 := by
      have hsin_half_mono : sin (u₁ / 2) ≤ sin (u₂ / 2) := by
        refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
        · linarith
        · linarith
        · linarith
      have hprod_mono : sin d * sin (u₁ / 2) ≤ sin d * sin (u₂ / 2) := by
        nlinarith
      have h_arcsin_mono : arcsin (sin d * sin (u₁ / 2)) ≤ arcsin (sin d * sin (u₂ / 2)) :=
        Real.arcsin_le_arcsin hprod_mono
      dsimp [ebase]
      linarith
    -- tan monotonicity
    have htan_mono : tan (ebase d u₁ / 2) ≤ tan (ebase d u₂ / 2) := by
      have hmono := Real.strictMonoOn_tan.monotoneOn
      have hleft : ebase d u₁ / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
        dsimp [ebase]
        rcases h_arcsin_range u₁ hu₁pos hu₁le with ⟨hl, hr⟩
        exact ⟨by linarith, by linarith⟩
      have hright : ebase d u₂ / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
        dsimp [ebase]
        rcases h_arcsin_range u₂ hu₂pos hu₂le with ⟨hl, hr⟩
        exact ⟨by linarith, by linarith⟩
      exact hmono hleft hright hebase_mono
    -- cot d * tan(...)
    have h_mul_mono : cot d * tan (ebase d u₁ / 2) ≤ cot d * tan (ebase d u₂ / 2) := by
      nlinarith
    -- min 1
    have h_min_mono : min 1 (cot d * tan (ebase d u₁ / 2)) ≤ min 1 (cot d * tan (ebase d u₂ / 2)) :=
      min_le_min (le_refl 1) h_mul_mono
    -- arccos
    exact Real.arccos_le_arccos h_min_mono
  -- Combine using AntitoneOn.add
  exact AntitoneOn.add hbangle_anti harccos_anti

/-- (T9) the side opposite a known angle is increasing in the angle. -/
theorem T9_monotoneOn_G (e f : ℝ) (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) :
    MonotoneOn (fun G => arccos (cos e * cos f + sin e * sin f * cos G)) (Set.Icc 0 π) := by
  rcases he with ⟨he_pos, he_lt⟩
  rcases hf with ⟨hf_pos, hf_lt⟩
  have hsin_pos : sin e * sin f > 0 := by
    have hse := Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
    have hsf := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt
    exact mul_pos hse hsf
  have hcos_anti : StrictAntiOn cos (Set.Icc (0 : ℝ) π) := Real.strictAntiOn_cos
  intro G₁ hG₁ G₂ hG₂ hle
  rcases lt_or_eq_of_le hle with (hlt | heq)
  · have hcos_le : cos G₂ < cos G₁ := hcos_anti hG₁ hG₂ hlt
    have h_mul : sin e * sin f * cos G₂ < sin e * sin f * cos G₁ := by
      exact mul_lt_mul_of_pos_left hcos_le hsin_pos
    have h_add : cos e * cos f + sin e * sin f * cos G₂ < cos e * cos f + sin e * sin f * cos G₁ := by
      linarith
    exact Real.arccos_le_arccos (le_of_lt h_add)
  · subst heq
    rfl

/-- (T9) monotone in `e` where `sin e cos f - cos e sin f cos G ≥ 0`. -/
theorem T9_monotoneOn_e (f G a b : ℝ) (hab : 0 < a ∧ b < π)
    (hsign : ∀ e ∈ Set.Icc a b, 0 ≤ sin e * cos f - cos e * sin f * cos G) :
    MonotoneOn (fun e => arccos (cos e * cos f + sin e * sin f * cos G)) (Set.Icc a b) := by
  set g := fun e : ℝ => cos e * cos f + sin e * sin f * cos G with hg
  have hg_cont : Continuous g := by
    unfold g
    refine Continuous.add ?_ ?_
    · exact Real.continuous_cos.mul continuous_const
    · exact ((Real.continuous_sin.mul continuous_const).mul continuous_const)
  have hg_diff : DifferentiableOn ℝ g (Set.Ioo a b) := by
    intro x hx
    refine (DifferentiableAt.differentiableWithinAt ?_)
    unfold g
    refine ((Real.differentiableAt_cos).mul_const (cos f)).add ?_
    refine ((Real.differentiableAt_sin).mul_const (sin f)).mul_const (cos G)
  have hderiv (x : ℝ) : deriv g x = -(sin x * cos f - cos x * sin f * cos G) := by
    have h_hasDeriv : HasDerivAt g (-(sin x * cos f - cos x * sin f * cos G)) x := by
      have hcos : HasDerivAt cos (-sin x) x := Real.hasDerivAt_cos x
      have hsin : HasDerivAt sin (cos x) x := Real.hasDerivAt_sin x
      have h1 : HasDerivAt (fun e => cos e * cos f) ((-sin x) * cos f) x :=
        hcos.mul_const (cos f)
      have h2 : HasDerivAt (fun e => (sin e * sin f) * cos G) ((cos x * sin f) * cos G) x :=
        (hsin.mul_const (sin f)).mul_const (cos G)
      have hsum := h1.add h2
      have hg_eq : g = ((fun e => cos e * cos f) + (fun e => (sin e * sin f) * cos G)) := by
        ext e; dsimp [g]
      rw [hg_eq]
      convert hsum using 1
      ring_nf
    exact HasDerivAt.deriv h_hasDeriv
  have hg_antitone : AntitoneOn g (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · exact hg_cont.continuousOn
    · rw [interior_Icc]
      exact hg_diff
    · rw [interior_Icc]
      intro x hx
      rw [hderiv x]
      have hx_icc : x ∈ Set.Icc a b := by
        rcases hx with ⟨hax, hxb⟩
        exact ⟨by linarith, by linarith⟩
      have h_nonneg := hsign x hx_icc
      linarith
  have harccos_antitone : AntitoneOn Real.arccos Set.univ := by
    intro x _ y _ hxy
    exact Real.arccos_le_arccos hxy
  have h_maps : Set.MapsTo g (Set.Icc a b) Set.univ := by
    intro x _; exact Set.mem_univ _
  exact (harccos_antitone.comp hg_antitone h_maps : MonotoneOn (Real.arccos ∘ g) (Set.Icc a b))

/-- (T2) `η` is decreasing in `g`. -/
theorem eta_strictAntiOn_g (e f : ℝ) (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) :
    StrictAntiOn (fun g => eta g e f) (Set.Icc 0 π) := by
  rcases he with ⟨he_pos, he_lt⟩
  rcases hf with ⟨hf_pos, hf_lt⟩
  have hsin_pos : 0 < sin e * sin f := by
    have h1 : 0 < sin e := Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
    have h2 : 0 < sin f := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt
    exact mul_pos h1 h2
  intro x hx y hy hxy
  have hcos : cos y < cos x := Real.strictAntiOn_cos hx hy hxy
  have hsub : cos y - cos e * cos f < cos x - cos e * cos f := sub_lt_sub_right hcos (cos e * cos f)
  exact div_lt_div_of_pos_right hsub hsin_pos

/-- (T2) derivative of `η` in `e`, with the sign of `cos f - cos e cos g`. -/
theorem eta_hasDerivAt_e (g e f : ℝ) (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) :
    HasDerivAt (fun e => eta g e f)
      (sin f * (cos f - cos e * cos g) / (sin e * sin f) ^ 2) e := by
  rcases he with ⟨heL, heR⟩
  rcases hf with ⟨hfL, hfR⟩
  have hsin_e_pos : sin e > 0 := Real.sin_pos_of_pos_of_lt_pi heL heR
  have hsin_f_pos : sin f > 0 := Real.sin_pos_of_pos_of_lt_pi hfL hfR
  have hden_ne_zero : sin e * sin f ≠ 0 := by positivity
  have hN_deriv : HasDerivAt (fun e => cos g - cos e * cos f) (sin e * cos f) e := by
    have h1 : HasDerivAt (fun _ : ℝ => cos g) 0 e := hasDerivAt_const e (cos g)
    have h2 : HasDerivAt cos (-sin e) e := Real.hasDerivAt_cos e
    have h3 : HasDerivAt (fun _ : ℝ => cos f) 0 e := hasDerivAt_const e (cos f)
    have hprod : HasDerivAt (fun x => cos x * cos f) ((-sin e) * cos f) e := by
      have := HasDerivAt.mul h2 h3
      simpa [Pi.mul_def] using this
    have hsub : HasDerivAt (fun x => cos g - cos x * cos f) (0 - (-sin e) * cos f) e :=
      HasDerivAt.sub h1 hprod
    simpa [zero_sub, neg_mul, mul_comm] using hsub
  have hD_deriv : HasDerivAt (fun e => sin e * sin f) (cos e * sin f) e := by
    have hsin_e : HasDerivAt sin (cos e) e := Real.hasDerivAt_sin e
    have hsin_f_const : HasDerivAt (fun _ : ℝ => sin f) 0 e := hasDerivAt_const e (sin f)
    have hprod : HasDerivAt (fun x => sin x * sin f) ((cos e) * sin f) e := by
      have := HasDerivAt.mul hsin_e hsin_f_const
      simpa [Pi.mul_def, add_zero] using this
    exact hprod
  have h_deriv : HasDerivAt (fun e => eta g e f)
      ((sin e * cos f * (sin e * sin f) - (cos g - cos e * cos f) * (cos e * sin f)) / (sin e * sin f) ^ 2) e :=
    HasDerivAt.div hN_deriv hD_deriv hden_ne_zero
  have h_simplify : (sin e * cos f * (sin e * sin f) - (cos g - cos e * cos f) * (cos e * sin f)) / (sin e * sin f) ^ 2 =
      sin f * (cos f - cos e * cos g) / (sin e * sin f) ^ 2 := by
    have hden_sq_ne_zero : (sin e * sin f) ^ 2 ≠ 0 := by positivity
    field_simp [hden_sq_ne_zero]
    calc
      sin e ^ 2 * cos f - cos e * (cos g - cos f * cos e)
          = sin e ^ 2 * cos f - cos e * cos g + cos e * (cos f * cos e) := by ring
      _ = sin e ^ 2 * cos f - cos e * cos g + cos e ^ 2 * cos f := by ring
      _ = cos f * (sin e ^ 2 + cos e ^ 2) - cos e * cos g := by ring
      _ = cos f * 1 - cos e * cos g := by rw [Real.sin_sq_add_cos_sq e]
      _ = cos f - cos e * cos g := by ring
      _ = cos f - cos g * cos e := by ring
  simpa [h_simplify, eta] using h_deriv

/-- The sine rule in the form used by `gam_hasDerivAt_side`: both sides are
`sqrt (1 - cos² a - cos² b - cos² c + 2 cos a cos b cos c) / sin a`. -/
theorem sine_rule_eta (a b c : ℝ) (ha : 0 < a ∧ a < π) (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) :
    sin c * Real.sqrt (1 - eta b a c ^ 2) = sin b * Real.sqrt (1 - eta c a b ^ 2) := by
  rcases ha with ⟨ha_pos, ha_lt⟩
  rcases hb with ⟨hb_pos, hb_lt⟩
  rcases hc with ⟨hc_pos, hc_lt⟩
  have ha_sin_pos : sin a > 0 := sin_pos_of_pos_of_lt_pi ha_pos ha_lt
  have hb_sin_pos : sin b > 0 := sin_pos_of_pos_of_lt_pi hb_pos hb_lt
  have hc_sin_pos : sin c > 0 := sin_pos_of_pos_of_lt_pi hc_pos hc_lt
  have ha_sin_ne_zero : sin a ≠ 0 := by linarith
  have hb_sin_ne_zero : sin b ≠ 0 := by linarith
  have hc_sin_ne_zero : sin c ≠ 0 := by linarith
  have h_sq_eq : sin c ^ 2 * (1 - eta b a c ^ 2) = sin b ^ 2 * (1 - eta c a b ^ 2) := by
    unfold eta
    field_simp [ha_sin_ne_zero, hb_sin_ne_zero, hc_sin_ne_zero]
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq c]
  calc
    sin c * Real.sqrt (1 - eta b a c ^ 2)
        = Real.sqrt ((sin c ^ 2) * (1 - eta b a c ^ 2)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ sin c ^ 2), Real.sqrt_sq (by linarith : 0 ≤ sin c)]
    _ = Real.sqrt ((sin b ^ 2) * (1 - eta c a b ^ 2)) := by rw [h_sq_eq]
    _ = Real.sqrt (sin b ^ 2) * Real.sqrt (1 - eta c a b ^ 2) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ sin b ^ 2)]
    _ = sin b * Real.sqrt (1 - eta c a b ^ 2) := by
      rw [Real.sqrt_sq (by linarith : 0 ≤ sin b)]

/-- (G1) the angle `C` between the sides `a, b` opposite `c`: `∂C/∂a = -cot B / sin a`. -/
theorem gam_hasDerivAt_side (a b c : ℝ) (ha : 0 < a ∧ a < π) (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (h : -1 < eta c a b ∧ eta c a b < 1) :
    HasDerivAt (fun a => gam c a b) (-(cot (gam b a c)) / sin a) a := by
  rcases ha with ⟨haL, haR⟩
  rcases hb with ⟨hbL, hbR⟩
  rcases hc with ⟨hcL, hcR⟩
  rcases h with ⟨hηL, hηR⟩
  have hηC_ne_neg_one : eta c a b ≠ -1 := by linarith
  have hηC_ne_one : eta c a b ≠ 1 := by linarith
  have hηC_lower : -1 ≤ eta c a b := by linarith
  have hηC_upper : eta c a b ≤ 1 := by linarith
  have hsin_pos_a : sin a > 0 := Real.sin_pos_of_pos_of_lt_pi haL haR
  have hsin_pos_b : sin b > 0 := Real.sin_pos_of_pos_of_lt_pi hbL hbR
  have hsin_pos_c : sin c > 0 := Real.sin_pos_of_pos_of_lt_pi hcL hcR
  set ηC := eta c a b with hηC_def
  set ηB := eta b a c with hηB_def
  have h_sine_rule : sin c * Real.sqrt (1 - ηB ^ 2) = sin b * Real.sqrt (1 - ηC ^ 2) :=
    sine_rule_eta a b c ⟨haL, haR⟩ ⟨hbL, hbR⟩ ⟨hcL, hcR⟩
  have h_sqrt_ηC_pos : Real.sqrt (1 - ηC ^ 2) > 0 := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith
  have h_sqrt_ηB_pos : Real.sqrt (1 - ηB ^ 2) > 0 := by
    have hpos : sin b * Real.sqrt (1 - ηC ^ 2) > 0 := mul_pos hsin_pos_b h_sqrt_ηC_pos
    rw [← h_sine_rule] at hpos
    exact pos_of_mul_pos_right hpos hsin_pos_c.le
  have hηB_lower : -1 ≤ ηB := by
    have : 1 - ηB ^ 2 > 0 := Real.sqrt_pos.mp h_sqrt_ηB_pos
    nlinarith
  have hηB_upper : ηB ≤ 1 := by
    have : 1 - ηB ^ 2 > 0 := Real.sqrt_pos.mp h_sqrt_ηB_pos
    nlinarith
  have h_deriv_eta : HasDerivAt (fun x => eta c x b) (sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2) a :=
    eta_hasDerivAt_e c a b ⟨haL, haR⟩ ⟨hbL, hbR⟩
  have h_deriv_arccos : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - ηC ^ 2))) ηC :=
    Real.hasDerivAt_arccos hηC_ne_neg_one hηC_ne_one
  have h_deriv_gam_raw : HasDerivAt (fun x => gam c x b) ((-(1 / Real.sqrt (1 - ηC ^ 2))) * (sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2)) a := by
    have h_deriv_arccos' : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - ηC ^ 2))) (eta c a b) := by
      simpa [hηC_def] using h_deriv_arccos
    have hcomp : HasDerivAt (Real.arccos ∘ (fun x => eta c x b)) ((-(1 / Real.sqrt (1 - ηC ^ 2))) * (sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2)) a :=
      HasDerivAt.comp (x := a) (h := fun x => eta c x b) (h₂ := Real.arccos) h_deriv_arccos' h_deriv_eta
    dsimp [gam]
    exact hcomp
  have h_cos_diff : cos b - cos a * cos c = ηB * sin a * sin c := by
    dsimp [ηB, eta]
    have hsin_a_ne : sin a ≠ 0 := by linarith
    have hsin_b_ne : sin b ≠ 0 := by linarith
    field_simp [hsin_a_ne, hsin_b_ne]
  have h_gam_eq : gam b a c = Real.arccos ηB := by
    dsimp [gam, ηB]
  have h_simplify : (-(1 / Real.sqrt (1 - ηC ^ 2))) * (sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2) = -(cot (gam b a c)) / sin a := by
    have h_step1 : sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2 = sin b * (ηB * sin a * sin c) / ((sin a) ^ 2 * (sin b) ^ 2) := by
      simp [h_cos_diff]
      ring
    have h_step2 : sin b * (ηB * sin a * sin c) / ((sin a) ^ 2 * (sin b) ^ 2) = (ηB * sin c) / (sin a * sin b) := by
      field_simp [hsin_pos_a.ne.symm, hsin_pos_b.ne.symm]
    have h_step3 : (-(ηB * sin c) / (sin a * (sin c * Real.sqrt (1 - ηB ^ 2)))) = -(ηB) / (sin a * Real.sqrt (1 - ηB ^ 2)) := by
      field_simp [hsin_pos_c.ne.symm]
    calc
      (-(1 / Real.sqrt (1 - ηC ^ 2))) * (sin b * (cos b - cos a * cos c) / (sin a * sin b) ^ 2)
          = (-(1 / Real.sqrt (1 - ηC ^ 2))) * (sin b * (ηB * sin a * sin c) / ((sin a) ^ 2 * (sin b) ^ 2)) := by rw [h_step1]
      _ = (-(1 / Real.sqrt (1 - ηC ^ 2))) * ((ηB * sin c) / (sin a * sin b)) := by rw [h_step2]
      _ = -(ηB * sin c) / (sin a * sin b * Real.sqrt (1 - ηC ^ 2)) := by ring
      _ = -(ηB * sin c) / (sin a * (sin b * Real.sqrt (1 - ηC ^ 2))) := by ring
      _ = -(ηB * sin c) / (sin a * (sin c * Real.sqrt (1 - ηB ^ 2))) := by rw [h_sine_rule]
      _ = -(ηB) / (sin a * Real.sqrt (1 - ηB ^ 2)) := by rw [h_step3]
      _ = -(Real.cos (Real.arccos ηB) / Real.sin (Real.arccos ηB)) / sin a := by
        rw [Real.cos_arccos hηB_lower hηB_upper, Real.sin_arccos]
        ring
      _ = -(Real.cos (gam b a c) / Real.sin (gam b a c)) / sin a := by rw [h_gam_eq]
      _ = -(cot (gam b a c)) / sin a := by rw [Real.cot_eq_cos_div_sin]
  rw [h_simplify] at h_deriv_gam_raw
  exact h_deriv_gam_raw

/-- (G1) the identity behind the sign of the fan maps of (T5), (T6). -/
theorem fan_sign_identity (d u X : ℝ) (hd : 0 < d ∧ d < π / 2) (hu : 0 < u ∧ u < π)
    (hX : 0 < X ∧ X < π) :
    cos d * sin (u / 2) + cot X * cos (u / 2) =
      cos (u / 2) * sin (bangle d u + X) / (sin (bangle d u) * sin X) := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hu with ⟨hupos, hult⟩
  rcases hX with ⟨hXpos, hXlt⟩
  have hcosd_pos : cos d > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hsin_u2_pos : sin (u / 2) > 0 := by
    apply Real.sin_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hcos_u2_pos : cos (u / 2) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hsin_X_pos : sin X > 0 := by
    apply Real.sin_pos_of_mem_Ioo
    exact ⟨hXpos, hXlt⟩
  set y := cos (u / 2) / (cos d * sin (u / 2)) with hy_def
  have hy_pos : y > 0 := by
    rw [hy_def]
    refine div_pos hcos_u2_pos (mul_pos hcosd_pos hsin_u2_pos)
  set β := bangle d u with hβ_def
  have htan_β : tan β = y := by
    rw [hβ_def, Tammes15.bangle, hy_def, Real.tan_arctan]
  have hsin_β_pos : sin β > 0 := by
    rw [hβ_def, Tammes15.bangle]
    exact (Real.sin_arctan_pos.mpr hy_pos)
  have hcos_β_div_sin_β : cos β / sin β = cos d * sin (u / 2) / cos (u / 2) := by
    calc
      cos β / sin β = 1 / (sin β / cos β) := by rw [← one_div_div]
      _ = 1 / tan β := by rw [← Real.tan_eq_sin_div_cos]
      _ = 1 / y := by rw [htan_β]
      _ = cos d * sin (u / 2) / cos (u / 2) := by
        rw [hy_def]
        field_simp [hcos_u2_pos.ne']
  calc
    cos d * sin (u / 2) + cot X * cos (u / 2) = cos d * sin (u / 2) + (cos X / sin X) * cos (u / 2) := by
      rw [Real.cot_eq_cos_div_sin]
    _ = cos (u / 2) * (cos X / sin X) + cos d * sin (u / 2) := by ring
    _ = cos (u / 2) * cot X + cos d * sin (u / 2) := by rw [Real.cot_eq_cos_div_sin]
    _ = cos (u / 2) * (cos X / sin X) + cos (u / 2) * (cos d * sin (u / 2) / cos (u / 2)) := by
      rw [Real.cot_eq_cos_div_sin]
      field_simp [hcos_u2_pos.ne']
    _ = cos (u / 2) * ((cos X / sin X) + (cos d * sin (u / 2) / cos (u / 2))) := by
      rw [← mul_add]
    _ = cos (u / 2) * (cos X / sin X + cos β / sin β) := by rw [hcos_β_div_sin_β]
    _ = cos (u / 2) * ((sin β * cos X) / (sin β * sin X) + (cos β * sin X) / (sin β * sin X)) := by
      field_simp [hsin_β_pos.ne', hsin_X_pos.ne']
    _ = cos (u / 2) * ((sin β * cos X + cos β * sin X) / (sin β * sin X)) := by rw [← add_div]
    _ = cos (u / 2) * sin (β + X) / (sin β * sin X) := by
      rw [Real.sin_add β X, ← mul_div_assoc]
    _ = cos (u / 2) * sin (bangle d u + X) / (sin (bangle d u) * sin X) := by rw [hβ_def]

end Tammes15
