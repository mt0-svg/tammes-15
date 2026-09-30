import Tammes15.Rattlers.Hex

/-!
# Proposition nor by an inscribed polygon: circle points, the perimeter, the margin


With `r, e₁, e₂` orthonormal, `circPt h t` is
the point of the circle of radius `h` about `r` at angle `t` from `e₁`. The polygon has the vertex
`e₁` (the point `v'` at distance `π/2` from `r`) and the five circle points at `t = π/2 + jπ/4`,
`j = 0, …, 4`; its perimeter is `π + 4 arccos (cos² h + sin² h cos (π/4))`, which exceeds `5 dhi`
at `h = hrad dlo` and increases with `h`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- The point at angle `t` on the circle of radius `h` about `r`, in the frame `e₁, e₂`. -/
noncomputable def circPt (r e₁ e₂ : E3) (h t : ℝ) : E3 :=
  cos h • r + sin h • (cos t • e₁ + sin t • e₂)

/-- The perimeter of the inscribed polygon of Proposition nor, `k = 4`. -/
noncomputable def norPoly (h : ℝ) : ℝ := π + 4 * arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4))

theorem inner_circPt (r e₁ e₂ : E3) (hr : ‖r‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (hr₁ : ⟪r, e₁⟫ = 0) (hr₂ : ⟪r, e₂⟫ = 0) (h₁₂ : ⟪e₁, e₂⟫ = 0) (h s t : ℝ) :
    ⟪circPt r e₁ e₂ h s, circPt r e₁ e₂ h t⟫ = cos h ^ 2 + sin h ^ 2 * cos (t - s) := by
  unfold circPt
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm,
    hr, h₁, h₂, hr₁, hr₂, h₁₂]
  simp only [starRingEnd_apply, star_trivial]
  rw [Real.cos_sub]
  ring

theorem norm_circPt (r e₁ e₂ : E3) (hr : ‖r‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (hr₁ : ⟪r, e₁⟫ = 0) (hr₂ : ⟪r, e₂⟫ = 0) (h₁₂ : ⟪e₁, e₂⟫ = 0) (h t : ℝ) :
    ‖circPt r e₁ e₂ h t‖ = 1 := by
  have h_inner : ⟪circPt r e₁ e₂ h t, circPt r e₁ e₂ h t⟫ = 1 := by
    calc
      ⟪circPt r e₁ e₂ h t, circPt r e₁ e₂ h t⟫
          = cos h ^ 2 + sin h ^ 2 * cos (t - t) :=
        inner_circPt r e₁ e₂ hr h₁ h₂ hr₁ hr₂ h₁₂ h t t
      _ = cos h ^ 2 + sin h ^ 2 * cos 0 := by rw [sub_self t]
      _ = cos h ^ 2 + sin h ^ 2 * 1 := by rw [Real.cos_zero]
      _ = cos h ^ 2 + sin h ^ 2 := by ring
      _ = sin h ^ 2 + cos h ^ 2 := by ring
      _ = 1 := Real.sin_sq_add_cos_sq h
  have h_norm_sq : ‖circPt r e₁ e₂ h t‖ ^ 2 = 1 := by
    calc
      ‖circPt r e₁ e₂ h t‖ ^ 2 = ⟪circPt r e₁ e₂ h t, circPt r e₁ e₂ h t⟫ := by
        rw [real_inner_self_eq_norm_sq]
      _ = 1 := h_inner
  have h_nonneg : 0 ≤ ‖circPt r e₁ e₂ h t‖ := norm_nonneg _
  nlinarith

theorem sdist_center_circPt (r e₁ e₂ : E3) (hr : ‖r‖ = 1) (hr₁ : ⟪r, e₁⟫ = 0)
    (hr₂ : ⟪r, e₂⟫ = 0) (h : ℝ) (hh : 0 ≤ h ∧ h ≤ π) (t : ℝ) :
    sdist r (circPt r e₁ e₂ h t) = h := by
  rcases hh with ⟨hh1, hh2⟩
  unfold sdist circPt
  have hinner : ⟪r, cos h • r + sin h • (cos t • e₁ + sin t • e₂)⟫ = cos h := by
    calc
      ⟪r, cos h • r + sin h • (cos t • e₁ + sin t • e₂)⟫
          = ⟪r, cos h • r⟫ + ⟪r, sin h • (cos t • e₁ + sin t • e₂)⟫ := by rw [inner_add_right]
      _ = cos h * ⟪r, r⟫ + sin h * ⟪r, cos t • e₁ + sin t • e₂⟫ := by rw [inner_smul_right, inner_smul_right]
      _ = cos h * ⟪r, r⟫ + sin h * (⟪r, cos t • e₁⟫ + ⟪r, sin t • e₂⟫) := by rw [inner_add_right]
      _ = cos h * ⟪r, r⟫ + sin h * (cos t * ⟪r, e₁⟫ + sin t * ⟪r, e₂⟫) := by rw [inner_smul_right, inner_smul_right]
      _ = cos h * ⟪r, r⟫ + sin h * (cos t * 0 + sin t * 0) := by rw [hr₁, hr₂]
      _ = cos h * ⟪r, r⟫ := by ring
      _ = cos h * (‖r‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
      _ = cos h * (1 ^ 2) := by rw [hr]
      _ = cos h := by norm_num
  rw [hinner]
  exact Real.arccos_cos hh1 hh2

theorem sdist_e1_circPt (r e₁ e₂ : E3) (h₁ : ‖e₁‖ = 1) (hr₁ : ⟪r, e₁⟫ = 0)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) (h t : ℝ) (ht : cos t = 0) : sdist e₁ (circPt r e₁ e₂ h t) = π / 2 := by
  unfold sdist circPt
  have hinner : ⟪e₁, cos h • r + sin h • (cos t • e₁ + sin t • e₂)⟫ = 0 := by
    calc
      ⟪e₁, cos h • r + sin h • (cos t • e₁ + sin t • e₂)⟫
          = ⟪e₁, cos h • r⟫ + ⟪e₁, sin h • (cos t • e₁ + sin t • e₂)⟫ := by
        rw [inner_add_right]
      _ = cos h * ⟪e₁, r⟫ + ⟪e₁, sin h • (cos t • e₁ + sin t • e₂)⟫ := by
        rw [real_inner_smul_right]
      _ = cos h * ⟪e₁, r⟫ + sin h * ⟪e₁, cos t • e₁ + sin t • e₂⟫ := by
        rw [real_inner_smul_right]
      _ = cos h * ⟪e₁, r⟫ + sin h * (⟪e₁, cos t • e₁⟫ + ⟪e₁, sin t • e₂⟫) := by
        rw [inner_add_right]
      _ = cos h * ⟪e₁, r⟫ + sin h * (cos t * ⟪e₁, e₁⟫ + sin t * ⟪e₁, e₂⟫) := by
        simp [real_inner_smul_right]
      _ = cos h * ⟪e₁, r⟫ + sin h * (cos t * ‖e₁‖ ^ 2 + sin t * ⟪e₁, e₂⟫) := by
        rw [real_inner_self_eq_norm_sq]
      _ = cos h * ⟪e₁, r⟫ + sin h * (cos t * (1 : ℝ) ^ 2 + sin t * 0) := by
        rw [h₁, h₁₂]
      _ = cos h * ⟪e₁, r⟫ + sin h * (cos t * 1 + 0) := by ring
      _ = cos h * ⟪e₁, r⟫ + sin h * (cos t) := by ring
      _ = cos h * ⟪e₁, r⟫ + sin h * 0 := by rw [ht]
      _ = cos h * ⟪e₁, r⟫ := by ring
      _ = cos h * 0 := by rw [← real_inner_comm, hr₁]
      _ = 0 := by ring
  rw [hinner]
  exact Real.arccos_zero

/-- The perimeter of the polygon `e₁, p₀, …, p₄` as the sum of its sides. -/
theorem norPoly_eq (r e₁ e₂ : E3) (hr : ‖r‖ = 1) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (hr₁ : ⟪r, e₁⟫ = 0) (hr₂ : ⟪r, e₂⟫ = 0) (h₁₂ : ⟪e₁, e₂⟫ = 0) (h : ℝ) :
    sdist e₁ (circPt r e₁ e₂ h (π / 2)) +
      (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
        (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) +
      sdist (circPt r e₁ e₂ h (3 * π / 2)) e₁ = norPoly h := by
  have hcos_3pi_div_two : cos (3 * π / 2) = 0 := by
    calc
      cos (3 * π / 2) = cos (π / 2 + π) := by ring
      _ = -cos (π / 2) := by rw [Real.cos_add_pi]
      _ = -0 := by rw [Real.cos_pi_div_two]
      _ = 0 := by simp
  have hfirst : sdist e₁ (circPt r e₁ e₂ h (π / 2)) = π / 2 :=
    sdist_e1_circPt r e₁ e₂ h₁ hr₁ h₁₂ h (π / 2) Real.cos_pi_div_two
  have hlast : sdist (circPt r e₁ e₂ h (3 * π / 2)) e₁ = π / 2 := by
    rw [sdist_comm]
    exact sdist_e1_circPt r e₁ e₂ h₁ hr₁ h₁₂ h (3 * π / 2) hcos_3pi_div_two
  have hsum : (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
        (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) =
      4 * arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4)) := by
    have hterm (j : Fin 4) : sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
        (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4))) =
        arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4)) := by
      unfold sdist
      have hinner : ⟪circPt r e₁ e₂ h (π / 2 + j * (π / 4)),
          circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4))⟫ =
          cos h ^ 2 + sin h ^ 2 * cos (π / 4) := by
        rw [inner_circPt r e₁ e₂ hr h₁ h₂ hr₁ hr₂ h₁₂ h (π / 2 + j * (π / 4))
          (π / 2 + (j + 1) * (π / 4))]
        congr 1
        ring
      rw [hinner]
    calc
      (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
        (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) =
        (∑ j : Fin 4, arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4))) := by
        apply Finset.sum_congr rfl; intro j hj; rw [hterm j]
      _ = (Finset.card (Finset.univ : Finset (Fin 4))) • arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4)) := by
        rw [Finset.sum_const]
      _ = 4 * arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4)) := by
        simp
  calc
    sdist e₁ (circPt r e₁ e₂ h (π / 2)) +
      (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
        (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) +
      sdist (circPt r e₁ e₂ h (3 * π / 2)) e₁
        = (π / 2) + (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
            (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) + (π / 2) := by
      rw [hfirst, hlast]
    _ = π + (∑ j : Fin 4, sdist (circPt r e₁ e₂ h (π / 2 + j * (π / 4)))
            (circPt r e₁ e₂ h (π / 2 + (j + 1) * (π / 4)))) := by ring
    _ = π + (4 * arccos (cos h ^ 2 + sin h ^ 2 * cos (π / 4))) := by rw [hsum]
    _ = norPoly h := by
      unfold norPoly
      ring

theorem norPoly_monotoneOn : MonotoneOn norPoly (Set.Icc 0 (π / 2)) := by
  intro a ha b hb hle
  rcases ha with ⟨ha_left, ha_right⟩
  rcases hb with ⟨hb_left, hb_right⟩
  unfold norPoly
  have hy_le : (cos b ^ 2 + sin b ^ 2 * cos (π / 4)) ≤ (cos a ^ 2 + sin a ^ 2 * cos (π / 4)) := by
    have hcos_sq_a : cos a ^ 2 = 1 - sin a ^ 2 := Real.cos_sq' a
    have hcos_sq_b : cos b ^ 2 = 1 - sin b ^ 2 := Real.cos_sq' b
    rw [hcos_sq_a, hcos_sq_b]
    have hsin_nonneg_a : 0 ≤ sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha_left (by linarith)
    have hsin_nonneg_b : 0 ≤ sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb_left (by linarith)
    have hsin_le : sin a ≤ sin b :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hle
    have hsin_sq_le : sin a ^ 2 ≤ sin b ^ 2 :=
      pow_le_pow_left₀ hsin_nonneg_a hsin_le 2
    have hpos : 0 ≤ 1 - cos (π / 4) := by
      have hcos_le_one : cos (π / 4) ≤ 1 := Real.cos_le_one (π / 4)
      linarith
    nlinarith
  have harccos_le : arccos (cos a ^ 2 + sin a ^ 2 * cos (π / 4)) ≤ arccos (cos b ^ 2 + sin b ^ 2 * cos (π / 4)) :=
    Real.arccos_le_arccos hy_le
  linarith

/-- The margin: `5 dhi < norPoly (hrad dlo)` (about 29.6°). -/
theorem margin_nor_poly : 5 * dhi < norPoly (hrad dlo) := by
  have hpi_pos : 0 < π := Real.pi_pos
  have hpi4_pos : 0 < π / 4 := by linarith
  have hdlo_lt_dhi : dlo < dhi := by
    unfold dlo dhi
    nlinarith
  have hdhi_lt_pi3 : dhi < π / 3 := dhi_lt_pi_div_three
  have hdlo_lt_pi2 : dlo < π / 2 := by linarith
  have hpi4_lt_dlo : π / 4 < dlo := pi_div_four_lt_dlo
  have hmem_pi4 : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hmem_dlo : dlo ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    exact Set.mem_Ioo.mpr ⟨by linarith, hdlo_lt_pi2⟩
  have hrad_pi4_lt_hrad_dlo : hrad (π / 4) < hrad dlo :=
    hrad_strictMonoOn hmem_pi4 hmem_dlo hpi4_lt_dlo
  have hrad_pi4_le_hrad_dlo : hrad (π / 4) ≤ hrad dlo :=
    le_of_lt hrad_pi4_lt_hrad_dlo
  -- bounds for hrad values
  have hrad_pi4_bounds : (π / 4) / 2 < hrad (π / 4) ∧ hrad (π / 4) < π / 4 :=
    hrad_bounds (π / 4) ⟨by linarith, by linarith⟩
  have hrad_dlo_bounds : dlo / 2 < hrad dlo ∧ hrad dlo < dlo :=
    hrad_bounds dlo ⟨by linarith, hdlo_lt_pi2⟩
  have hmem_nor_pi4 : hrad (π / 4) ∈ Set.Icc (0 : ℝ) (π / 2) :=
    Set.mem_Icc.mpr ⟨by linarith [hrad_pi4_bounds.1], by linarith [hrad_pi4_bounds.2]⟩
  have hmem_nor_dlo : hrad dlo ∈ Set.Icc (0 : ℝ) (π / 2) :=
    Set.mem_Icc.mpr ⟨by linarith [hrad_dlo_bounds.1], by linarith [hrad_dlo_bounds.2]⟩
  have hnor_pi4_le_nor_dlo : norPoly (hrad (π / 4)) ≤ norPoly (hrad dlo) :=
    norPoly_monotoneOn hmem_nor_pi4 hmem_nor_dlo hrad_pi4_le_hrad_dlo
  -- compute norPoly at hrad (π/4)
  have hsin_sq : sin (hrad (π / 4)) ^ 2 = Real.sqrt 2 - 1 := by
    rw [sin_hrad_pi_div_four]
    have h_nonneg : 0 ≤ Real.sqrt 2 - 1 := by
      have hsq2 : 1 < Real.sqrt 2 := by
        calc
          1 = Real.sqrt 1 := by norm_num
          _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    rw [Real.sq_sqrt h_nonneg]
  have hcos_sq : cos (hrad (π / 4)) ^ 2 = 2 - Real.sqrt 2 := by
    have := Real.cos_sq' (hrad (π / 4))
    rw [hsin_sq] at this
    linarith
  have hcos_pi4 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h_arg : cos (hrad (π / 4)) ^ 2 + sin (hrad (π / 4)) ^ 2 * cos (π / 4) = 3 - (3/2) * Real.sqrt 2 := by
    rw [hcos_sq, hsin_sq, hcos_pi4]
    -- (2 - √2) + (√2 - 1) * (√2 / 2) = 3 - (3/2)√2
    -- Expand: (√2 - 1) * (√2 / 2) = (2 - √2)/2 = 1 - √2/2
    -- So: 2 - √2 + 1 - √2/2 = 3 - (3/2)√2
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) from by norm_num)]
  set y := 3 - (3/2) * Real.sqrt 2 with hy_def
  set θ := (5 * dhi - π) / 4 with hθ_def
  have h5dhi_eq : 5 * dhi = π + 4 * θ := by
    rw [hθ_def]
    ring
  have hnor_pi4_eq : norPoly (hrad (π / 4)) = π + 4 * arccos y := by
    rw [norPoly, h_arg, hy_def]
  have hgoal_reduced : π + 4 * θ < π + 4 * arccos y := by
    -- need to show θ < arccos y
    have hθ_nonneg : 0 ≤ θ := by
      rw [hθ_def]
      have h5dhi_gt_pi : π < 5 * dhi := by
        -- since dhi > π/4, 5*dhi > 5π/4 > π
        have hdhi_gt_pi4 : π / 4 < dhi := by linarith
        nlinarith
      nlinarith
    have hθ_le_pi : θ ≤ π := by
      rw [hθ_def]
      have h5dhi_lt_2pi : 5 * dhi < 2 * π := by
        have hdhi_lt_pi2 : dhi < π / 2 := by linarith
        nlinarith
      nlinarith
    have hy_lower : -1 ≤ y := by
      rw [hy_def]
      have hsqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
        have h : (2:ℝ)^2 = 4 := by norm_num
        exact calc
          Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
          _ = 2 := by norm_num
      nlinarith
    have hy_upper : y ≤ 1 := by
      rw [hy_def]
      have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      nlinarith
    have hcosθ_le_one : cos θ ≤ 1 := by
      exact Real.cos_le_one _
    -- need: y < cos θ
    have hy_lt_cosθ : y < cos θ := by
      rw [hy_def]
      -- cos θ ≥ 1 - θ^2/2
      have hcosθ_ge : 1 - θ ^ 2 / 2 ≤ cos θ := Real.one_sub_sq_div_two_le_cos
      -- so it suffices to show 3 - (3/2)√2 < 1 - θ^2/2
      -- i.e., θ^2 < 3*√2 - 4
      have hθ_sq_lt : θ ^ 2 < 3 * Real.sqrt 2 - 4 := by
        rw [hθ_def]
        have hθ_expr : (5 * dhi - π) / 4 = 51679 * π / 360000 := by
          unfold dhi
          ring
        rw [hθ_expr]
        have hπ_lt : π < 31416/10000 := by linarith [Real.pi_lt_d4]
        have hsqrt2_gt : (14142/10000 : ℝ) < Real.sqrt 2 := by
          have hsq : ((14142 : ℝ)/10000)^2 < 2 := by norm_num
          have hpos : 0 ≤ (14142/10000 : ℝ) := by norm_num
          calc
            (14142/10000 : ℝ) = Real.sqrt (((14142 : ℝ)/10000)^2) := by rw [Real.sqrt_sq hpos]
            _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by positivity) hsq
        have hθ_lt : 51679*π/360000 < 51679*(31416/10000)/360000 := by
          gcongr
        have h_bound : (51679*(31416/10000)/360000)^2 < 3*(14142/10000 : ℝ) - 4 := by
          norm_num
        have h_sqrt2_gt' : 3*(14142/10000 : ℝ) - 4 < 3 * Real.sqrt 2 - 4 := by
          gcongr
        calc
          (51679*π/360000)^2 < (51679*(31416/10000)/360000)^2 := by
            gcongr
          _ < 3*(14142/10000 : ℝ) - 4 := h_bound
          _ < 3 * Real.sqrt 2 - 4 := h_sqrt2_gt'
      nlinarith
    -- Now use Real.arccos_lt_arccos
    have h_arccos : arccos (cos θ) < arccos y :=
      Real.arccos_lt_arccos hy_lower hy_lt_cosθ hcosθ_le_one
    have harccos_cosθ : arccos (cos θ) = θ :=
      Real.arccos_cos hθ_nonneg hθ_le_pi
    rw [harccos_cosθ] at h_arccos
    nlinarith
  -- Combine: 5*dhi = π + 4*θ < π + 4*arccos y = norPoly(hrad(π/4)) ≤ norPoly(hrad dlo)
  calc
    5 * dhi = π + 4 * θ := h5dhi_eq
    _ < π + 4 * arccos y := hgoal_reduced
    _ = norPoly (hrad (π / 4)) := by rw [hnor_pi4_eq]
    _ ≤ norPoly (hrad dlo) := hnor_pi4_le_nor_dlo

end Tammes15
