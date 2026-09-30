import Tammes15.Numerics.Taylor

/-!
# The two numerical facts of the Fejes Tóth bound

Paper, Section 8.4, facts N1 and N2. The level `c₀ = 0.5494377` lies above `cos dhi`
(N1, `dhi = π · 566716 / 1800000`), and the equilateral angle `θ₀ = arg (1 + 3c₀ + i (1 - c₀)
√(1 + 2c₀))` exceeds `π / 13` (N2), so `52 θ₀ > 4π`. Both by the Taylor enclosures of
`Tammes15.Numerics` at a rational bound of `π` (`Real.pi_gt_d20`, `Real.pi_lt_d20`); the rational
steps are closed by `norm_num`.

-/

open Real

namespace Tammes15.FejesToth

theorem pi_ge_d10 : (3.1415926535 : ℝ) ≤ π := by
  have := Real.pi_gt_d20; norm_num at this ⊢; linarith

theorem pi_le_d10 : π ≤ (3.1415926536 : ℝ) := by
  have := Real.pi_lt_d20; norm_num at this ⊢; linarith

/-- N1: `cos dhi ≤ c₀`. -/
theorem N1 : Real.cos (π * (566716 / 1800000)) ≤ 5494377 / 10 ^ 7 := by
  rw [mul_comm]
  refine Numerics.cos_mul_pi_le 7 (p := 3.1415926535) (by norm_num) pi_ge_d10 (by norm_num)
    (by norm_num) ?_
  simp only [Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- N2b: `r ≤ cos (π / 13)` for `r = 0.9709417579`. -/
theorem cos_pi_div_13_ge : (9709417579 / 10 ^ 10 : ℝ) ≤ Real.cos (π / 13) := by
  rw [show π / 13 = (1 / 13 : ℝ) * π by ring]
  refine Numerics.le_cos_mul_pi 5 (p := 3.1415926536) pi_le_d10 (by norm_num) (by norm_num) ?_
  simp only [Numerics.cosT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- N2 from N2b: `arg = arccos (s₀ / ‖·‖)` and `s₀ / ‖·‖ < r` (a rational inequality). -/
theorem N2_of_cos (h : (9709417579 / 10 ^ 10 : ℝ) ≤ Real.cos (π / 13)) :
    π / 13 < Complex.arg ⟨1 + 3 * (5494377 / 10 ^ 7 : ℝ),
      (1 - 5494377 / 10 ^ 7) * √(1 + 2 * (5494377 / 10 ^ 7 : ℝ))⟩ := by
  set c₀ := (5494377 / 10 ^ 7 : ℝ) with hc₀
  set s₀ := (1 + 3 * c₀ : ℝ) with hs₀
  set D₀ := ((1 - c₀) * √(1 + 2 * c₀) : ℝ) with hD₀
  set w := Complex.mk s₀ D₀ with hw
  set r := (9709417579 / 10 ^ 10 : ℝ) with hr
  have hDpos : 0 < D₀ := by
    rw [hD₀]
    have h1 : 0 < 1 - c₀ := by
      rw [hc₀]
      norm_num
    have h2 : 0 < √(1 + 2 * c₀) := by
      apply Real.sqrt_pos.mpr
      rw [hc₀]
      norm_num
    exact mul_pos h1 h2
  have harg : Complex.arg w = Real.arccos (s₀ / ‖w‖) := by
    apply Complex.arg_of_im_pos
    simpa [hw] using hDpos
  have hnorm_pos : 0 < ‖w‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hDzero : D₀ = 0 := by
      simpa [hw] using congrArg Complex.im hzero
    linarith [hDpos, hDzero]
  have h_s₀_pos : 0 < s₀ := by
    rw [hs₀, hc₀]
    norm_num
  have hpos_r : 0 < r := by
    rw [hr]
    norm_num
  have h_nonneg_s₀ : 0 ≤ s₀ := le_of_lt h_s₀_pos
  have h_nonneg_r : 0 ≤ r := le_of_lt hpos_r
  have h_nonneg_norm : 0 ≤ ‖w‖ := norm_nonneg _
  have h_norm_sq : ‖w‖ ^ 2 = s₀ ^ 2 + ((1 - c₀) ^ 2 * (1 + 2 * c₀)) := by
    calc
      ‖w‖ ^ 2 = Complex.normSq w := by rw [Complex.sq_norm]
      _ = s₀ ^ 2 + D₀ ^ 2 := by
        rw [Complex.normSq_mk]
        ring
      _ = s₀ ^ 2 + ((1 - c₀) * √(1 + 2 * c₀)) ^ 2 := by rw [hD₀]
      _ = s₀ ^ 2 + (1 - c₀) ^ 2 * ((√(1 + 2 * c₀)) ^ 2) := by ring
      _ = s₀ ^ 2 + (1 - c₀) ^ 2 * (1 + 2 * c₀) := by
        rw [Real.sq_sqrt (show 0 ≤ 1 + 2 * c₀ by
          rw [hc₀]
          norm_num)]
      _ = s₀ ^ 2 + ((1 - c₀) ^ 2 * (1 + 2 * c₀)) := by ring
  have h_ineq_sq : s₀ ^ 2 < r ^ 2 * (s₀ ^ 2 + ((1 - c₀) ^ 2 * (1 + 2 * c₀))) := by
    rw [hs₀, hc₀, hr]
    norm_num
  have h_ineq : s₀ / ‖w‖ < r := by
    apply (div_lt_iff₀ hnorm_pos).mpr
    have h_sq_lt : s₀ ^ 2 < (r * ‖w‖) ^ 2 := by
      calc
        s₀ ^ 2 < r ^ 2 * (s₀ ^ 2 + ((1 - c₀) ^ 2 * (1 + 2 * c₀))) := h_ineq_sq
        _ = r ^ 2 * (‖w‖ ^ 2) := by rw [h_norm_sq]
        _ = (r * ‖w‖) ^ 2 := by ring
    have h_nonneg_prod : 0 ≤ r * ‖w‖ := mul_nonneg h_nonneg_r h_nonneg_norm
    have h_lt : s₀ < r * ‖w‖ := by
      rwa [sq_lt_sq₀ h_nonneg_s₀ h_nonneg_prod] at h_sq_lt
    exact h_lt
  have h_pi_nonneg : 0 ≤ π / 13 := by positivity
  have h_pi_le_pi : π / 13 ≤ π := by
    have hπpos : 0 < π := by positivity
    nlinarith
  have h_cos_pi_le_one : Real.cos (π / 13) ≤ 1 := Real.cos_le_one _
  have h_arg_lt : Real.arccos (Real.cos (π / 13)) < Real.arccos (s₀ / ‖w‖) := by
    apply Real.arccos_lt_arccos
    · -- -1 ≤ s₀ / ‖w‖
      have : 0 ≤ s₀ / ‖w‖ := div_nonneg h_nonneg_s₀ h_nonneg_norm
      linarith
    · -- s₀ / ‖w‖ < Real.cos (π / 13)
      calc
        s₀ / ‖w‖ < r := h_ineq
        _ ≤ Real.cos (π / 13) := h
    · -- Real.cos (π / 13) ≤ 1
      exact h_cos_pi_le_one
  calc
    π / 13 = Real.arccos (Real.cos (π / 13)) := by
      rw [Real.arccos_cos h_pi_nonneg h_pi_le_pi]
    _ < Real.arccos (s₀ / ‖w‖) := h_arg_lt
    _ = Complex.arg w := by rw [harg]

/-- N2: `π / 13 < θ₀`. -/
theorem N2 : π / 13 < Complex.arg ⟨1 + 3 * (5494377 / 10 ^ 7 : ℝ),
    (1 - 5494377 / 10 ^ 7) * √(1 + 2 * (5494377 / 10 ^ 7 : ℝ))⟩ :=
  N2_of_cos cos_pi_div_13_ge

end Tammes15.FejesToth
