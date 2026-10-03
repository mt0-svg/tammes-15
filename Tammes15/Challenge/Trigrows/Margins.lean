import Tammes15.Challenge.Trigrows.Rows

/-!
# The range `[dlo, dhi]` and the closed-form margins of Section 4.3

`dlo = 53.65785°` and `dhi = 56.6716°` (paper, Conventions of Section 1). Proved here: the margins
`7 dlo > 2π`, `α(dhi) < 72°` (the hypothesis `hmarg` of Theorem 4.1), `3 dhi < π` (T8) and
`dhi + 2 h(dhi) < π` (the hypothesis of Lemma A.11). The margin of Proposition 4.6 is not here: it
depends on the polygon form of Rattlers.
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

end Tammes15
