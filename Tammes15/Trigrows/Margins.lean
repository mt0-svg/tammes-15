import Tammes15.Trigrows.Rows

/-!
# The range `[dlo, dhi]` and the closed-form margins of Section 3.4


`dlo = 53.65785°` and `dhi = 56.6716°` (paper, Section 1). The margins
`7 dlo > 2π` and `α(dhi) < 72°` (the hypothesis `hmarg` of Theorem 3.1), `3 dhi < π` (T8),
`dhi + 2 h(dhi) < π` (Lemma perims (2)) and the closed-form bound of Proposition nor,
`5 dhi < π (1 + sin h(dlo))`. The margin of Proposition onehex is not here: it depends on the
polygon form of Rattlers.
-/

open Real

namespace Tammes15

/-- `dlo = 53.65785°`. -/
noncomputable def dlo : ℝ := 5365785 / 100000 * (π / 180)

/-- `dhi = 56.6716°`. -/
noncomputable def dhi : ℝ := 566716 / 10000 * (π / 180)

theorem dlo_lt_dhi : dlo < dhi := by
  unfold dlo dhi
  have hπ : 0 < π / 180 := div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 180)
  refine (mul_lt_mul_of_pos_right ?_ hπ)
  norm_num

theorem pi_div_four_lt_dlo : π / 4 < dlo := by
  unfold dlo
  nlinarith [Real.pi_pos]

theorem dhi_lt_pi_div_three : dhi < π / 3 := by
  unfold dhi
  have hpi : 0 < π := Real.pi_pos
  have hpi_div : 0 < π / 180 := by nlinarith
  have h_lt : (566716 : ℝ) / 10000 < (60 : ℝ) := by norm_num
  have h_mul : (566716 / 10000 : ℝ) * (π / 180) < (60 : ℝ) * (π / 180) :=
    mul_lt_mul_of_pos_right h_lt hpi_div
  calc
    (566716 / 10000 : ℝ) * (π / 180) < (60 : ℝ) * (π / 180) := h_mul
    _ = π / 3 := by
      field_simp
      ring

theorem two_pi_lt_seven_dlo : 2 * π < 7 * dlo := by
  unfold dlo
  nlinarith [Real.pi_pos]

theorem three_dhi_lt_pi : 3 * dhi < π := by
  unfold dhi
  nlinarith [Real.pi_pos]

theorem cos_two_pi_div_five : cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h := Real.cos_two_mul (π / 5)
  have h2 : 2 * (π / 5) = 2 * π / 5 := by ring
  rw [h2] at h
  rw [Real.cos_pi_div_five] at h
  rw [h]
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (show 0 ≤ 5 by norm_num)
  field_simp
  nlinarith [hsq]

theorem alpha_pi_div_three : alpha (π / 3) = arccos (1 / 3) := by
  unfold alpha
  rw [Real.cos_pi_div_three]
  norm_num

theorem alpha_dhi_lt : alpha dhi < 2 * π / 5 := by
  have hdhi_pos : 0 < dhi := by
    unfold dhi
    have h : (0 : ℝ) < 566716 / 10000 * (π / 180) := by
      positivity
    exact h
  have hdhi_lt_pi_div_three : dhi < π / 3 := dhi_lt_pi_div_three
  have hpi_div_three_lt_pi_div_two : π / 3 < π / 2 := by
    nlinarith [Real.pi_pos]
  have hmem : dhi ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    exact Set.mem_Ioo.mpr ⟨hdhi_pos, lt_trans hdhi_lt_pi_div_three hpi_div_three_lt_pi_div_two⟩
  have halpha_lt : alpha dhi < alpha (π / 3) :=
    alpha_strictMonoOn hmem (Set.mem_Ioo.mpr ⟨by nlinarith [Real.pi_pos], by nlinarith⟩) hdhi_lt_pi_div_three
  have halpha_pi_div_three : alpha (π / 3) = arccos (1 / 3) := alpha_pi_div_three
  rw [halpha_pi_div_three] at halpha_lt
  have h_cos_lt : cos (2 * π / 5) < 1/3 := by
    rw [cos_two_pi_div_five]
    have h_sqrt5_lt : Real.sqrt 5 < 7/3 := by
      have h5pos : (0 : ℝ) ≤ 5 := by norm_num
      have hsq : (Real.sqrt 5) ^ 2 < (7/3 : ℝ) ^ 2 := by
        calc
          (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt h5pos
          _ < (49 : ℝ) / 9 := by norm_num
          _ = (7/3 : ℝ) ^ 2 := by ring
      have h_nonneg_sqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
      have h_nonneg_73 : 0 ≤ (7/3 : ℝ) := by norm_num
      nlinarith
    nlinarith
  have h_cos_ge_neg_one : (-1 : ℝ) ≤ cos (2 * π / 5) := by
    have := neg_one_le_cos (2 * π / 5)
    exact this
  have h_third_le_one : (1/3 : ℝ) ≤ 1 := by norm_num
  have h_arccos_lt : arccos (1/3 : ℝ) < arccos (cos (2 * π / 5)) :=
    Real.arccos_lt_arccos h_cos_ge_neg_one h_cos_lt h_third_le_one
  have h_arccos_cos : arccos (cos (2 * π / 5)) = 2 * π / 5 := by
    apply Real.arccos_cos
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  rw [h_arccos_cos] at h_arccos_lt
  exact lt_trans halpha_lt h_arccos_lt

theorem sin_hrad_pi_div_four : sin (hrad (π / 4)) = Real.sqrt (Real.sqrt 2 - 1) := by
  have hcos4 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hcos8 : cos (π / 8) = Real.sqrt (2 + Real.sqrt 2) / 2 := Real.cos_pi_div_eight
  have h_div2 : (π / 4) / 2 = π / 8 := by ring
  have hrad_def : hrad (π / 4) = arccos (cos (π / 4) / cos ((π / 4) / 2)) := rfl
  rw [h_div2] at hrad_def
  rw [hrad_def, Real.sin_arccos]
  rw [hcos4, hcos8]
  have h_sq : ((Real.sqrt 2 / 2) / (Real.sqrt (2 + Real.sqrt 2) / 2)) ^ 2 = 2 - Real.sqrt 2 := by
    calc
      ((Real.sqrt 2 / 2) / (Real.sqrt (2 + Real.sqrt 2) / 2)) ^ 2
          = (Real.sqrt 2 / Real.sqrt (2 + Real.sqrt 2)) ^ 2 := by ring
      _ = (Real.sqrt 2) ^ 2 / (Real.sqrt (2 + Real.sqrt 2)) ^ 2 := by ring
      _ = 2 / (2 + Real.sqrt 2) := by
        rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
          Real.sq_sqrt (show 0 ≤ 2 + Real.sqrt 2 by nlinarith [Real.sqrt_nonneg 2])]
      _ = 2 - Real.sqrt 2 := by
        field_simp [show 2 + Real.sqrt 2 ≠ 0 by nlinarith [Real.sqrt_nonneg 2]]
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  rw [h_sq]
  ring_nf

theorem margin_perims : dhi + 2 * hrad dhi < π := by
  have hπ_pos : 0 < π := Real.pi_pos
  have hdhi_pos : 0 < dhi := by
    unfold dhi
    positivity
  have hdhi_lt_pi_div_two : dhi < π / 2 := by
    unfold dhi
    have h : (566716 : ℝ) / 10000 / 180 < 1/2 := by norm_num
    nlinarith
  have h_bounds := hrad_bounds dhi ⟨hdhi_pos, hdhi_lt_pi_div_two⟩
  have h_hrad_lt_dhi : hrad dhi < dhi := h_bounds.right
  have h : dhi + 2 * hrad dhi < dhi + 2 * dhi := by
    nlinarith
  have h_eq : dhi + 2 * dhi = 3 * dhi := by ring
  rw [h_eq] at h
  have h_final : 3 * dhi < π := three_dhi_lt_pi
  linarith

theorem margin_nor_closed : 5 * dhi < π * (1 + sin (hrad dlo)) := by
  have hpi_pos : 0 < π := Real.pi_pos
  have hpi4_pos : 0 < π / 4 := by linarith
  have hpi4_lt_pi2 : π / 4 < π / 2 := by linarith
  have hdlo_pos : 0 < dlo := by
    unfold dlo
    positivity
  have hdlo_lt_pi2 : dlo < π / 2 := by
    unfold dlo
    have h : (5365785 : ℝ) < 9000000 := by norm_num
    nlinarith
  have h_sqrt_gt : (3/5 : ℝ) < Real.sqrt (Real.sqrt 2 - 1) := by
    have h_inner_sq : ((3/5 : ℝ) ^ 2) < Real.sqrt 2 - 1 := by
      have h_sqrt2_gt_34_25 : (34/25 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num : 0 ≤ (34/25 : ℝ))]
        norm_num
      have h_sq_eq : (3/5 : ℝ) ^ 2 = (34/25 : ℝ) - 1 := by norm_num
      linarith
    rw [Real.lt_sqrt (by norm_num : 0 ≤ (3/5 : ℝ))]
    exact h_inner_sq
  have h_dhi_bound : 5 * dhi < (8/5 : ℝ) * π := by
    unfold dhi
    have hcoeff : (5 * 566716 / 10000 / 180 : ℝ) < (8/5 : ℝ) := by norm_num
    nlinarith [hpi_pos]
  have h_sin_lt : sin (hrad (π / 4)) < sin (hrad dlo) := by
    have hx_mem : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hpi4_pos, hpi4_lt_pi2⟩
    have hy_mem : dlo ∈ Set.Ioo (0 : ℝ) (π / 2) := Set.mem_Ioo.mpr ⟨hdlo_pos, hdlo_lt_pi2⟩
    have h_lt : hrad (π / 4) < hrad dlo := hrad_strictMonoOn hx_mem hy_mem pi_div_four_lt_dlo
    have hx_sin_low : -(π / 2) ≤ hrad (π / 4) := by
      have hpos : 0 < hrad (π / 4) := by
        have := (hrad_bounds (π / 4) ⟨hpi4_pos, hpi4_lt_pi2⟩).1
        linarith
      linarith
    have hy_sin_high : hrad dlo ≤ π / 2 := by
      have hlt := (hrad_bounds dlo ⟨hdlo_pos, hdlo_lt_pi2⟩).2
      linarith
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two hx_sin_low hy_sin_high h_lt
  calc
    5 * dhi < (8/5 : ℝ) * π := h_dhi_bound
    _ = π * (8/5 : ℝ) := by ring
    _ = π * (1 + (3/5 : ℝ)) := by ring
    _ < π * (1 + Real.sqrt (Real.sqrt 2 - 1)) := by
      nlinarith
    _ = π * (1 + sin (hrad (π / 4))) := by rw [sin_hrad_pi_div_four]
    _ < π * (1 + sin (hrad dlo)) := by
      nlinarith

end Tammes15
