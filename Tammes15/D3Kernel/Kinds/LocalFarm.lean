import Tammes15.PaperSteps.Defs

namespace Tammes15.D3Kernel.Kinds

open Tammes15 Tammes15.PaperSteps
open scoped RealInnerProductSpace

theorem lc_inner_sub (z z0 x x0 : EuclideanSpace ℝ (Fin 3)) :
    |inner ℝ z x - inner ℝ z0 x0| ≤ ‖z - z0‖ * ‖x‖ + ‖z0‖ * ‖x - x0‖ := by
  calc
    |inner ℝ z x - inner ℝ z0 x0|
        = |inner ℝ (z - z0) x + inner ℝ z0 (x - x0)| := by
      congr 1
      calc
        inner ℝ z x - inner ℝ z0 x0
            = (inner ℝ z x - inner ℝ z0 x) + (inner ℝ z0 x - inner ℝ z0 x0) := by ring
        _ = inner ℝ (z - z0) x + inner ℝ z0 (x - x0) := by
          simp [inner_sub_left, inner_sub_right]
    _ ≤ |inner ℝ (z - z0) x| + |inner ℝ z0 (x - x0)| := by
      exact abs_add_le _ _
    _ ≤ ‖z - z0‖ * ‖x‖ + ‖z0‖ * ‖x - x0‖ := by
      nlinarith [abs_real_inner_le_norm (z - z0) x, abs_real_inner_le_norm z0 (x - x0)]

theorem lc_cross_norm_le (a b : EuclideanSpace ℝ (Fin 3)) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hnorm : ‖cross a b‖ = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) := by
    simpa [cross] using InnerProductGeometry.norm_ofLp_crossProduct a b
  rw [hnorm]
  have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  calc
    ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) ≤ ‖a‖ * ‖b‖ * 1 := by
      gcongr
    _ = ‖a‖ * ‖b‖ := by ring

theorem lc_normalize_sub (u u0 : EuclideanSpace ℝ (Fin 3)) (h0 : u0 ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖u0‖⁻¹ • u0‖ ≤ 2 * ‖u - u0‖ / ‖u0‖ := by
  have h0norm : ‖u0‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact h0
  have h0norm_nonneg : 0 ≤ ‖u0‖ := norm_nonneg _
  have h0norm_pos : 0 < ‖u0‖ := lt_of_le_of_ne h0norm_nonneg h0norm.symm
  have h0inv_nonneg : 0 ≤ ‖u0‖⁻¹ := inv_nonneg.mpr h0norm_nonneg
  by_cases hu : u = 0
  · subst hu
    simp [norm_smul_of_nonneg h0inv_nonneg, h0norm]
  · have hunorm : ‖u‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact hu
    have hunorm_nonneg : 0 ≤ ‖u‖ := norm_nonneg _
    have hunorm_pos : 0 < ‖u‖ := lt_of_le_of_ne hunorm_nonneg hunorm.symm
    have huinv_nonneg : 0 ≤ ‖u‖⁻¹ := inv_nonneg.mpr hunorm_nonneg
    have h_eq : ‖u‖⁻¹ • u - ‖u0‖⁻¹ • u0 = (‖u0‖⁻¹ • (u - u0)) + ((‖u‖⁻¹ - ‖u0‖⁻¹) • u) := by
      calc
        ‖u‖⁻¹ • u - ‖u0‖⁻¹ • u0 = (‖u‖⁻¹ • u - ‖u0‖⁻¹ • u) + (‖u0‖⁻¹ • u - ‖u0‖⁻¹ • u0) := by abel
        _ = (‖u‖⁻¹ - ‖u0‖⁻¹) • u + ‖u0‖⁻¹ • (u - u0) := by simp [sub_smul, smul_sub]
        _ = (‖u0‖⁻¹ • (u - u0)) + ((‖u‖⁻¹ - ‖u0‖⁻¹) • u) := by abel
    rw [h_eq]
    calc
      ‖(‖u0‖⁻¹ • (u - u0)) + ((‖u‖⁻¹ - ‖u0‖⁻¹) • u)‖ ≤ ‖‖u0‖⁻¹ • (u - u0)‖ + ‖(‖u‖⁻¹ - ‖u0‖⁻¹) • u‖ :=
        norm_add_le _ _
      _ = (‖u0‖⁻¹ * ‖u - u0‖) + (|‖u‖⁻¹ - ‖u0‖⁻¹| * ‖u‖) := by
        simp [norm_smul_of_nonneg h0inv_nonneg, norm_smul, Real.norm_eq_abs]
      _ = (‖u0‖⁻¹ * ‖u - u0‖) + (|‖u0‖ - ‖u‖| / ‖u0‖) := by
        have hkey : |‖u‖⁻¹ - ‖u0‖⁻¹| * ‖u‖ = |‖u0‖ - ‖u‖| / ‖u0‖ := by
          apply ((div_eq_iff h0norm).mpr ?_).symm
          calc
            |‖u0‖ - ‖u‖| = |(‖u‖⁻¹ - ‖u0‖⁻¹) * (‖u‖ * ‖u0‖)| := by
              have h_inner : (‖u‖⁻¹ - ‖u0‖⁻¹) * (‖u‖ * ‖u0‖) = ‖u0‖ - ‖u‖ := by
                field_simp [hunorm, h0norm]
              rw [h_inner]
            _ = |‖u‖⁻¹ - ‖u0‖⁻¹| * |‖u‖ * ‖u0‖| := by rw [abs_mul]
            _ = |‖u‖⁻¹ - ‖u0‖⁻¹| * (‖u‖ * ‖u0‖) := by
              rw [abs_of_pos (mul_pos hunorm_pos h0norm_pos)]
            _ = (|‖u‖⁻¹ - ‖u0‖⁻¹| * ‖u‖) * ‖u0‖ := by ring
        rw [hkey]
      _ ≤ (‖u0‖⁻¹ * ‖u - u0‖) + (‖u - u0‖ / ‖u0‖) := by
        have h_abs : |‖u0‖ - ‖u‖| ≤ ‖u - u0‖ := by
          simpa [abs_sub_comm] using abs_norm_sub_norm_le u u0
        have h_div : |‖u0‖ - ‖u‖| / ‖u0‖ ≤ ‖u - u0‖ / ‖u0‖ :=
          div_le_div_of_nonneg_right h_abs h0norm_nonneg
        exact add_le_add_right h_div (‖u0‖⁻¹ * ‖u - u0‖)
      _ = ‖u - u0‖ / ‖u0‖ + ‖u - u0‖ / ‖u0‖ := by ring
      _ = 2 * ‖u - u0‖ / ‖u0‖ := by ring

theorem lc_u_sub {za zb a b : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (ha : ‖za - a‖ ≤ ρ) (hb : ‖zb - b‖ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hna : ‖a‖ ≤ 2) (hnb : ‖b‖ ≤ 2) :
    ‖(zb - inner ℝ za zb • za) - (b - inner ℝ a b • a)‖ ≤ 20 * ρ := by
  have hρ_nonneg : 0 ≤ ρ := by
    have h := norm_nonneg (za - a)
    linarith
  have hza_norm : ‖za‖ ≤ 3 := by
    calc
      ‖za‖ = ‖(za - a) + a‖ := by simp
      _ ≤ ‖za - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ ρ + 2 := add_le_add ha hna
      _ ≤ 1 + 2 := add_le_add hρ1 (le_refl 2)
      _ = 3 := by norm_num
  have hzb_norm : ‖zb‖ ≤ 3 := by
    calc
      ‖zb‖ = ‖(zb - b) + b‖ := by simp
      _ ≤ ‖zb - b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ ρ + 2 := add_le_add hb hnb
      _ ≤ 1 + 2 := add_le_add hρ1 (le_refl 2)
      _ = 3 := by norm_num
  have h_inner_diff : |inner ℝ za zb - inner ℝ a b| ≤ 5 * ρ := by
    have h := lc_inner_sub za a zb b
    have h_right : ‖za - a‖ * ‖zb‖ + ‖a‖ * ‖zb - b‖ ≤ 5 * ρ := by
      have h1 : ‖za - a‖ * ‖zb‖ ≤ ρ * 3 :=
        mul_le_mul ha hzb_norm (norm_nonneg _) hρ_nonneg
      have h2 : ‖a‖ * ‖zb - b‖ ≤ 2 * ρ :=
        mul_le_mul hna hb (norm_nonneg _) (by norm_num)
      linarith
    linarith
  have h_inner_ab : |inner ℝ a b| ≤ 4 := by
    have h := abs_real_inner_le_norm a b
    have h_right : ‖a‖ * ‖b‖ ≤ 4 := by
      have h' : ‖a‖ * ‖b‖ ≤ 2 * 2 :=
        mul_le_mul hna hnb (norm_nonneg _) (by norm_num)
      linarith
    linarith
  have h_decomp : (zb - inner ℝ za zb • za) - (b - inner ℝ a b • a) =
      (zb - b) - ((inner ℝ za zb - inner ℝ a b) • za) - (inner ℝ a b • (za - a)) := by
    simp [sub_eq_add_neg, add_assoc, smul_add, add_smul]
    abel
  rw [h_decomp]
  have h_smul1 : ‖(inner ℝ za zb - inner ℝ a b) • za‖ ≤ (5 * ρ) * 3 := by
    calc
      ‖(inner ℝ za zb - inner ℝ a b) • za‖ = |inner ℝ za zb - inner ℝ a b| * ‖za‖ := norm_smul _ _
      _ ≤ (5 * ρ) * 3 := mul_le_mul h_inner_diff hza_norm (norm_nonneg _) (by nlinarith)
  have h_smul2 : ‖inner ℝ a b • (za - a)‖ ≤ 4 * ρ := by
    calc
      ‖inner ℝ a b • (za - a)‖ = |inner ℝ a b| * ‖za - a‖ := norm_smul _ _
      _ ≤ 4 * ρ := mul_le_mul h_inner_ab ha (norm_nonneg _) (by nlinarith)
  calc
    ‖(zb - b) - ((inner ℝ za zb - inner ℝ a b) • za) - (inner ℝ a b • (za - a))‖
        ≤ ‖(zb - b) - ((inner ℝ za zb - inner ℝ a b) • za)‖ + ‖inner ℝ a b • (za - a)‖ :=
      norm_sub_le _ _
    _ ≤ (‖zb - b‖ + ‖(inner ℝ za zb - inner ℝ a b) • za‖) + ‖inner ℝ a b • (za - a)‖ := by
      apply add_le_add (norm_sub_le _ _) (le_refl _)
    _ = ‖zb - b‖ + ‖(inner ℝ za zb - inner ℝ a b) • za‖ + ‖inner ℝ a b • (za - a)‖ := by ring
    _ ≤ ρ + (5 * ρ) * 3 + 4 * ρ := by
      linarith
    _ = 20 * ρ := by ring

theorem lc_e1_sub {u u0 : EuclideanSpace ℝ (Fin 3)} {ρ μ : ℝ} (hu : ‖u - u0‖ ≤ 20 * ρ) (hμ : 0 < μ)
    (hμu : μ ≤ ‖u0‖) : ‖‖u‖⁻¹ • u - ‖u0‖⁻¹ • u0‖ ≤ 40 * ρ / μ := by
  have hu0_ne_zero : u0 ≠ 0 := by
    intro hzero
    have hnorm0 : ‖u0‖ = 0 := by simp [hzero]
    linarith
  have hnorm_u_sub_u0_nonneg : 0 ≤ ‖u - u0‖ := norm_nonneg _
  have hnorm_u0_nonneg : 0 ≤ ‖u0‖ := norm_nonneg _
  have hρ_nonneg : 0 ≤ ρ := by
    have : 0 ≤ 20 * ρ := by linarith
    nlinarith
  have h_first : ‖‖u‖⁻¹ • u - ‖u0‖⁻¹ • u0‖ ≤ 2 * ‖u - u0‖ / ‖u0‖ :=
    lc_normalize_sub u u0 hu0_ne_zero
  have h_second : 2 * ‖u - u0‖ / ‖u0‖ ≤ 40 * ρ / μ := by
    have hnum : 2 * ‖u - u0‖ ≤ 40 * ρ := by nlinarith
    have hpos_u0 : 0 < ‖u0‖ := by linarith
    have h40ρ_nonneg : 0 ≤ 40 * ρ := by nlinarith
    have h_div_same_denom : (2 * ‖u - u0‖) / ‖u0‖ ≤ (40 * ρ) / ‖u0‖ :=
      div_le_div_of_nonneg_right hnum hnorm_u0_nonneg
    have h_div_same_num : (40 * ρ) / ‖u0‖ ≤ (40 * ρ) / μ :=
      div_le_div_of_nonneg_left h40ρ_nonneg hμ hμu
    linarith
  linarith

theorem lc_norm3_le (x y z : ℝ) : ‖(!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))‖ ≤ |x| + |y| + |z| := by
  have h_nonneg : 0 ≤ |x| + |y| + |z| := by positivity
  have h_sq : ‖(!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤ (|x| + |y| + |z|) ^ 2 := by
    calc
      ‖(!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = ∑ i : Fin 3, ‖((!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))).ofLp i‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      _ = ∑ i : Fin 3, ((!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) i) ^ 2 := by
        simp [Real.norm_eq_abs]
      _ = ((!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) 0) ^ 2 + ((!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) 1) ^ 2 + ((!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) 2) ^ 2 := by
        rw [Fin.sum_univ_three]
      _ = x ^ 2 + y ^ 2 + z ^ 2 := by
        simp
      _ = |x| ^ 2 + |y| ^ 2 + |z| ^ 2 := by
        simp [sq_abs]
      _ ≤ (|x| + |y| + |z|) ^ 2 := by
        have h_eq : (|x| + |y| + |z|) ^ 2 = |x| ^ 2 + |y| ^ 2 + |z| ^ 2 + 2 * (|x| * |y| + |x| * |z| + |y| * |z|) := by ring
        rw [h_eq]
        have h_nonneg_cross : 0 ≤ 2 * (|x| * |y| + |x| * |z| + |y| * |z|) := by positivity
        exact le_add_of_nonneg_right h_nonneg_cross
  have h_nonneg_norm : 0 ≤ ‖(!₂[x, y, z] : EuclideanSpace ℝ (Fin 3))‖ := by positivity
  nlinarith

theorem lc_inner3 (x0 x1 x2 y0 y1 y2 : ℝ) :
    inner ℝ (!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)) !₂[y0, y1, y2] = x0 * y0 + x1 * y1 + x2 * y2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem lc_cross3 (x0 x1 x2 y0 y1 y2 : ℝ) :
    cross (!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)) !₂[y0, y1, y2] =
      !₂[x1 * y2 - x2 * y1, x2 * y0 - x0 * y2, x0 * y1 - x1 * y0] := by
  simp [cross, cross_apply]

theorem lc_dist_le {u w : EuclideanSpace ℝ (Fin 3)} {x0 x1 x2 y0 y1 y2 Qa Qb T D : ℤ} (hQa : 0 < Qa)
    (hQb : 0 < Qb) (hT : 0 ≤ T) (hD : 0 < D)
    (hu : u.ofLp 0 = (x0 : ℝ) / Qa ∧ u.ofLp 1 = (x1 : ℝ) / Qa ∧ u.ofLp 2 = (x2 : ℝ) / Qa)
    (hw : w.ofLp 0 = (y0 : ℝ) / Qb ∧ w.ofLp 1 = (y1 : ℝ) / Qb ∧ w.ofLp 2 = (y2 : ℝ) / Qb)
    (h : ((x0 * Qb - y0 * Qa) * (x0 * Qb - y0 * Qa) + (x1 * Qb - y1 * Qa) * (x1 * Qb - y1 * Qa) +
        (x2 * Qb - y2 * Qa) * (x2 * Qb - y2 * Qa)) * (D * D) ≤ (T * Qa * Qb) * (T * Qa * Qb)) :
    ‖u - w‖ ≤ (T : ℝ) / D := by
  rcases hu with ⟨hu0, hu1, hu2⟩
  rcases hw with ⟨hw0, hw1, hw2⟩

  have hnorm_sq : ‖u - w‖ ^ 2 = (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) ^ 2 + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) ^ 2 + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) ^ 2) / ((Qa : ℝ) * Qb) ^ 2 := by
    calc
      ‖u - w‖ ^ 2 = ∑ i : Fin 3, ‖(u - w).ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
      _ = ∑ i : Fin 3, ((u - w).ofLp i) ^ 2 := by
        refine Finset.sum_congr rfl (λ i hi => ?_)
        simp [Real.norm_eq_abs, sq_abs]
      _ = ((u - w).ofLp 0) ^ 2 + ((u - w).ofLp 1) ^ 2 + ((u - w).ofLp 2) ^ 2 := by
        simp [Fin.sum_univ_three]
      _ = (u.ofLp 0 - w.ofLp 0) ^ 2 + (u.ofLp 1 - w.ofLp 1) ^ 2 + (u.ofLp 2 - w.ofLp 2) ^ 2 := by simp
      _ = (((x0 : ℝ) / Qa) - ((y0 : ℝ) / Qb)) ^ 2 + (((x1 : ℝ) / Qa) - ((y1 : ℝ) / Qb)) ^ 2 + (((x2 : ℝ) / Qa) - ((y2 : ℝ) / Qb)) ^ 2 := by rw [hu0, hu1, hu2, hw0, hw1, hw2]
      _ = (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) / ((Qa : ℝ) * Qb)) ^ 2 + (((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) / ((Qa : ℝ) * Qb)) ^ 2 + (((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) / ((Qa : ℝ) * Qb)) ^ 2 := by
        field_simp
      _ = (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) ^ 2 + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) ^ 2 + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) ^ 2) / ((Qa : ℝ) * Qb) ^ 2 := by
        ring

  have h_real : (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) ^ 2 + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) ^ 2 + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) ^ 2) * ((D : ℝ) ^ 2) ≤ (((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) ^ 2) := by

    have h_cast : (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) * ((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) * ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) * ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa)) * ((D : ℝ) * (D : ℝ)) ≤ ((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) * ((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) := by
      exact_mod_cast h

    simpa [pow_two] using h_cast

  have hposD_sq : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have h_bound : (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) ^ 2 + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) ^ 2 + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) ^ 2) ≤ (((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) ^ 2) / ((D : ℝ) ^ 2) :=
    (le_div_iff₀ hposD_sq).mpr h_real

  have h_norm_sq_le : ‖u - w‖ ^ 2 ≤ ((T : ℝ) / (D : ℝ)) ^ 2 := by
    rw [hnorm_sq]

    have hpos_denom_sq : (0 : ℝ) ≤ ((Qa : ℝ) * Qb) ^ 2 := by positivity
    calc
      (((x0 : ℝ) * Qb - (y0 : ℝ) * Qa) ^ 2 + ((x1 : ℝ) * Qb - (y1 : ℝ) * Qa) ^ 2 + ((x2 : ℝ) * Qb - (y2 : ℝ) * Qa) ^ 2) / ((Qa : ℝ) * Qb) ^ 2
          ≤ ((((T : ℝ) * (Qa : ℝ) * (Qb : ℝ)) ^ 2) / ((D : ℝ) ^ 2)) / ((Qa : ℝ) * Qb) ^ 2 :=
        div_le_div_of_nonneg_right h_bound hpos_denom_sq
      _ = ((T : ℝ) / (D : ℝ)) ^ 2 := by
        field_simp

  have hnonneg_norm : 0 ≤ ‖u - w‖ := norm_nonneg _
  have hnonneg_T_div_D : 0 ≤ (T : ℝ) / (D : ℝ) := by
    have hT' : (0 : ℝ) ≤ T := by exact_mod_cast hT
    have hD' : (0 : ℝ) ≤ D := by exact_mod_cast hD.le
    exact div_nonneg hT' hD'
  exact le_of_sq_le_sq h_norm_sq_le hnonneg_T_div_D

theorem lc_inv_norm_mem {u : EuclideanSpace ℝ (Fin 3)} {l1 l2 : ℝ} (h1 : 0 ≤ l1) (h2 : 0 ≤ l2)
    (hl1 : l1 ^ 2 * (u.ofLp 0 ^ 2 + u.ofLp 1 ^ 2 + u.ofLp 2 ^ 2) ≤ 1)
    (hl2 : 1 ≤ l2 ^ 2 * (u.ofLp 0 ^ 2 + u.ofLp 1 ^ 2 + u.ofLp 2 ^ 2)) :
    u ≠ 0 ∧ l1 ≤ ‖u‖⁻¹ ∧ ‖u‖⁻¹ ≤ l2 := by
  set S := u.ofLp 0 ^ 2 + u.ofLp 1 ^ 2 + u.ofLp 2 ^ 2 with hS
  have hS_nonneg : 0 ≤ S := by
    unfold S
    positivity
  have h_norm_sq_eq : ‖u‖ ^ 2 = S := by
    calc
      ‖u‖ ^ 2 = ∑ i : Fin 3, ‖u.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq u
      _ = ‖u.ofLp 0‖ ^ 2 + ‖u.ofLp 1‖ ^ 2 + ‖u.ofLp 2‖ ^ 2 := by simp [Fin.sum_univ_three]
      _ = |u.ofLp 0| ^ 2 + |u.ofLp 1| ^ 2 + |u.ofLp 2| ^ 2 := by simp [Real.norm_eq_abs]
      _ = (u.ofLp 0) ^ 2 + (u.ofLp 1) ^ 2 + (u.ofLp 2) ^ 2 := by simp [sq_abs]
      _ = S := rfl
  have h_norm_pos : 0 < ‖u‖ := by
    by_contra! hle
    have h_nonneg : 0 ≤ ‖u‖ := norm_nonneg _
    have h_norm_zero : ‖u‖ = 0 := by linarith
    have hS_zero : S = 0 := by
      rw [← h_norm_sq_eq, h_norm_zero]
      norm_num
    have h_contra : (1 : ℝ) ≤ (0 : ℝ) := by
      calc
        (1 : ℝ) ≤ l2 ^ 2 * S := hl2
        _ = l2 ^ 2 * (0 : ℝ) := by rw [hS_zero]
        _ = (0 : ℝ) := by ring
    linarith
  have h_mul_nonneg1 : 0 ≤ l1 * ‖u‖ := mul_nonneg h1 (by positivity)
  have h_mul_nonneg2 : 0 ≤ l2 * ‖u‖ := mul_nonneg h2 (by positivity)
  have h_mul_sq_le_one : (l1 * ‖u‖) ^ 2 ≤ 1 := by
    calc
      (l1 * ‖u‖) ^ 2 = l1 ^ 2 * ‖u‖ ^ 2 := by ring
      _ = l1 ^ 2 * S := by rw [h_norm_sq_eq]
      _ ≤ 1 := hl1
  have h_mul_sq_ge_one : 1 ≤ (l2 * ‖u‖) ^ 2 := by
    calc
      1 ≤ l2 ^ 2 * S := hl2
      _ = l2 ^ 2 * ‖u‖ ^ 2 := by rw [h_norm_sq_eq]
      _ = (l2 * ‖u‖) ^ 2 := by ring
  have h_one_le_mul : 1 ≤ l2 * ‖u‖ := by
    have h_sq : (1 : ℝ) ^ 2 ≤ (l2 * ‖u‖) ^ 2 := by
      simpa [one_pow] using h_mul_sq_ge_one
    exact ((sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) h_mul_nonneg2).mp h_sq)
  have h_mul_le_one : l1 * ‖u‖ ≤ 1 := by
    have h_sq : (l1 * ‖u‖) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa [one_pow] using h_mul_sq_le_one
    exact ((sq_le_sq₀ h_mul_nonneg1 (by norm_num : (0 : ℝ) ≤ 1)).mp h_sq)
  have hu_ne_zero : u ≠ 0 := by
    intro hzero
    have hnorm0 : ‖u‖ = 0 := by simp [hzero]
    rw [hnorm0] at h_one_le_mul
    have : l2 * (0 : ℝ) = 0 := by ring
    rw [this] at h_one_le_mul
    linarith
  have h_inv_le : l1 ≤ ‖u‖⁻¹ := by
    calc
      l1 ≤ (1 : ℝ) / ‖u‖ := (le_div_iff₀ h_norm_pos).mpr h_mul_le_one
      _ = ‖u‖⁻¹ := by simp
  have h_inv_le' : ‖u‖⁻¹ ≤ l2 := by
    rw [inv_le_iff_one_le_mul₀' h_norm_pos]
    simpa [mul_comm] using h_one_le_mul
  exact And.intro hu_ne_zero (And.intro h_inv_le h_inv_le')

theorem lc_norm_le_two {x0 x1 x2 : ℝ} (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 ≤ 4) :
    ‖(!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 := by
  have hsq : ‖(!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
    calc
      ‖(!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = ∑ i : Fin 3, ‖((!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)).ofLp i)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
      _ = ‖((!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)).ofLp 0)‖ ^ 2 + ‖((!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)).ofLp 1)‖ ^ 2 + ‖((!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3)).ofLp 2)‖ ^ 2 := by
        rw [Fin.sum_univ_three]
      _ = x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := by
        simp
      _ ≤ 4 := h
      _ = (2 : ℝ) ^ 2 := by norm_num
  have hnonneg_norm : 0 ≤ ‖(!₂[x0, x1, x2] : EuclideanSpace ℝ (Fin 3))‖ := by
    positivity
  have hnonneg_2 : (0 : ℝ) ≤ 2 := by norm_num
  exact ((pow_le_pow_iff_left₀ hnonneg_norm hnonneg_2 (by norm_num : 2 ≠ 0)).mp hsq)

theorem lc_tieN_expand (a b q : EuclideanSpace ℝ (Fin 3)) (mirror : Bool) :
    tieNormalize a b mirror q =
      !₂[inner ℝ q (b - inner ℝ a b • a) * ‖b - inner ℝ a b • a‖⁻¹,
        (if mirror then -1 else 1) * (inner ℝ q (cross a (b - inner ℝ a b • a)) * ‖b - inner ℝ a b • a‖⁻¹),
        inner ℝ q a] := by
  unfold tieNormalize
  ext i
  fin_cases i <;> simp [cross, inner_smul_right, mul_comm]

theorem lc_cross_sub_of (a a0 b b0 : EuclideanSpace ℝ (Fin 3))
    (hn : ∀ x y : EuclideanSpace ℝ (Fin 3), ‖cross x y‖ ≤ ‖x‖ * ‖y‖) :
    ‖cross a b - cross a0 b0‖ ≤ ‖a - a0‖ * ‖b‖ + ‖a0‖ * ‖b - b0‖ := by
  have h_eq : cross a b - cross a0 b0 = cross (a - a0) b + cross a0 (b - b0) := by
    ext i
    fin_cases i <;> simp [cross, cross_apply] <;> ring
  rw [h_eq]
  calc
    ‖cross (a - a0) b + cross a0 (b - b0)‖ ≤ ‖cross (a - a0) b‖ + ‖cross a0 (b - b0)‖ :=
      norm_add_le _ _
    _ ≤ ‖a - a0‖ * ‖b‖ + ‖a0‖ * ‖b - b0‖ := by
      apply add_le_add
      · exact hn _ _
      · exact hn _ _

theorem lc_cross_sub (a a0 b b0 : EuclideanSpace ℝ (Fin 3)) :
    ‖cross a b - cross a0 b0‖ ≤ ‖a - a0‖ * ‖b‖ + ‖a0‖ * ‖b - b0‖ :=
  lc_cross_sub_of a a0 b b0 lc_cross_norm_le

theorem lc_coord_sub {za zq a q e e0 : EuclideanSpace ℝ (Fin 3)} {ρ μ : ℝ} (ha : ‖za - a‖ ≤ ρ)
    (hq : ‖zq - q‖ ≤ ρ) (hρ1 : ρ ≤ 1) (hna : ‖a‖ ≤ 2) (hnq : ‖q‖ ≤ 2) (hμ : 0 < μ) (hμ10 : μ ≤ 10)
    (hsmall : 40 * ρ ≤ μ) (he : ‖e - e0‖ ≤ 40 * ρ / μ) (hne : ‖e0‖ ≤ 1) :
    |inner ℝ zq e - inner ℝ q e0| ≤ 100 * ρ / μ ∧
      |inner ℝ zq (cross za e) - inner ℝ q (cross a e0)| ≤ 400 * ρ / μ ∧
      |inner ℝ zq za - inner ℝ q a| ≤ 100 * ρ / μ := by
  have hρ_nonneg : 0 ≤ ρ := by
    have h := norm_nonneg (za - a)
    linarith
  have hdiv_le_one : 40 * ρ / μ ≤ 1 := by
    exact (div_le_one (by linarith [hμ])).mpr hsmall
  have he_norm_le_two : ‖e‖ ≤ 2 := by
    calc
      ‖e‖ = ‖e0 + (e - e0)‖ := by simp
      _ ≤ ‖e0‖ + ‖e - e0‖ := norm_add_le _ _
      _ ≤ 1 + (40 * ρ / μ) := by nlinarith
      _ ≤ 1 + 1 := by nlinarith
      _ = 2 := by norm_num
  have hza_norm_le_three : ‖za‖ ≤ 3 := by
    calc
      ‖za‖ = ‖a + (za - a)‖ := by simp
      _ ≤ ‖a‖ + ‖za - a‖ := norm_add_le _ _
      _ ≤ 2 + ρ := by nlinarith
      _ ≤ 3 := by nlinarith
  have hzq_norm_le_three : ‖zq‖ ≤ 3 := by
    calc
      ‖zq‖ = ‖q + (zq - q)‖ := by simp
      _ ≤ ‖q‖ + ‖zq - q‖ := norm_add_le _ _
      _ ≤ 2 + ρ := by nlinarith
      _ ≤ 3 := by nlinarith
  have hρ_le_ten_ρ_div_μ : ρ ≤ 10 * ρ / μ := by
    have h : ρ * μ ≤ 10 * ρ := by
      nlinarith
    calc
      ρ = (ρ * μ) / μ := by field_simp [hμ.ne.symm]
      _ ≤ (10 * ρ) / μ := div_le_div_of_nonneg_right h (by linarith)
      _ = 10 * ρ / μ := by ring
  have h1 : |inner ℝ zq e - inner ℝ q e0| ≤ 100 * ρ / μ := by
    have hbound := lc_inner_sub zq q e e0
    have hright : ‖zq - q‖ * ‖e‖ + ‖q‖ * ‖e - e0‖ ≤ 100 * ρ / μ := by
      have h1' : ‖zq - q‖ * ‖e‖ ≤ ρ * 2 :=
        mul_le_mul hq he_norm_le_two (norm_nonneg _) hρ_nonneg
      have h2' : ‖q‖ * ‖e - e0‖ ≤ 2 * (40 * ρ / μ) :=
        mul_le_mul hnq he (norm_nonneg _) (by norm_num)
      have hsum : ‖zq - q‖ * ‖e‖ + ‖q‖ * ‖e - e0‖ ≤ ρ * 2 + 2 * (40 * ρ / μ) := by nlinarith
      have hcalc : ρ * 2 + 2 * (40 * ρ / μ) ≤ 100 * ρ / μ := by
        field_simp [hμ.ne.symm]
        nlinarith
      nlinarith
    exact le_trans hbound hright
  have h_cross_sub : ‖cross za e - cross a e0‖ ≤ 100 * ρ / μ := by
    have hbound := lc_cross_sub za a e e0
    have hright : ‖za - a‖ * ‖e‖ + ‖a‖ * ‖e - e0‖ ≤ 100 * ρ / μ := by
      have h1' : ‖za - a‖ * ‖e‖ ≤ ρ * 2 :=
        mul_le_mul ha he_norm_le_two (norm_nonneg _) hρ_nonneg
      have h2' : ‖a‖ * ‖e - e0‖ ≤ 2 * (40 * ρ / μ) :=
        mul_le_mul hna he (norm_nonneg _) (by norm_num)
      have hsum : ‖za - a‖ * ‖e‖ + ‖a‖ * ‖e - e0‖ ≤ ρ * 2 + 2 * (40 * ρ / μ) := by nlinarith
      have hcalc : ρ * 2 + 2 * (40 * ρ / μ) ≤ 100 * ρ / μ := by
        field_simp [hμ.ne.symm]
        nlinarith
      nlinarith
    exact le_trans hbound hright
  have h_cross_norm : ‖cross za e‖ ≤ 6 := by
    have hbound := lc_cross_norm_le za e
    have hright : ‖za‖ * ‖e‖ ≤ 6 :=
      calc
        ‖za‖ * ‖e‖ ≤ 3 * 2 := mul_le_mul hza_norm_le_three he_norm_le_two (norm_nonneg _) (by norm_num)
        _ = 6 := by norm_num
    exact le_trans hbound hright
  have h2 : |inner ℝ zq (cross za e) - inner ℝ q (cross a e0)| ≤ 400 * ρ / μ := by
    have hbound := lc_inner_sub zq q (cross za e) (cross a e0)
    have hright : ‖zq - q‖ * ‖cross za e‖ + ‖q‖ * ‖cross za e - cross a e0‖ ≤ 400 * ρ / μ := by
      have h1' : ‖zq - q‖ * ‖cross za e‖ ≤ ρ * 6 :=
        mul_le_mul hq h_cross_norm (norm_nonneg _) hρ_nonneg
      have h2' : ‖q‖ * ‖cross za e - cross a e0‖ ≤ 2 * (100 * ρ / μ) :=
        mul_le_mul hnq h_cross_sub (norm_nonneg _) (by norm_num)
      have hsum : ‖zq - q‖ * ‖cross za e‖ + ‖q‖ * ‖cross za e - cross a e0‖ ≤ ρ * 6 + 2 * (100 * ρ / μ) := by nlinarith
      have hcalc : ρ * 6 + 2 * (100 * ρ / μ) ≤ 400 * ρ / μ := by
        field_simp [hμ.ne.symm]
        nlinarith
      nlinarith
    exact le_trans hbound hright
  have h3 : |inner ℝ zq za - inner ℝ q a| ≤ 100 * ρ / μ := by
    have hbound := lc_inner_sub zq q za a
    have hright : ‖zq - q‖ * ‖za‖ + ‖q‖ * ‖za - a‖ ≤ 100 * ρ / μ := by
      have h1' : ‖zq - q‖ * ‖za‖ ≤ ρ * 3 :=
        mul_le_mul hq hza_norm_le_three (norm_nonneg _) hρ_nonneg
      have h2' : ‖q‖ * ‖za - a‖ ≤ 2 * ρ :=
        mul_le_mul hnq ha (norm_nonneg _) (by norm_num)
      have hsum : ‖zq - q‖ * ‖za‖ + ‖q‖ * ‖za - a‖ ≤ ρ * 3 + 2 * ρ := by nlinarith
      have hcalc : ρ * 3 + 2 * ρ ≤ 100 * ρ / μ := by
        field_simp [hμ.ne.symm]
        nlinarith
      nlinarith
    exact le_trans hbound hright
  exact And.intro h1 (And.intro h2 h3)

theorem lc_tie_pert {za zb zq a b q : EuclideanSpace ℝ (Fin 3)} {ρ μ : ℝ} (mirror : Bool)
    (ha : ‖za - a‖ ≤ ρ) (hb : ‖zb - b‖ ≤ ρ) (hq : ‖zq - q‖ ≤ ρ) (hρ1 : ρ ≤ 1) (hna : ‖a‖ ≤ 2) (hnb : ‖b‖ ≤ 2)
    (hnq : ‖q‖ ≤ 2) (hμ : 0 < μ) (hsmall : 40 * ρ ≤ μ) (hu : μ ≤ ‖b - inner ℝ a b • a‖) :
    ‖tieNormalize za zb mirror zq - tieNormalize a b mirror q‖ ≤ 1000 * ρ / μ := by
  let u := zb - inner ℝ za zb • za
  let u0 := b - inner ℝ a b • a
  let e := ‖u‖⁻¹ • u
  let e0 := ‖u0‖⁻¹ • u0
  have hu_sub : ‖u - u0‖ ≤ 20 * ρ := lc_u_sub ha hb hρ1 hna hnb
  have hμu : μ ≤ ‖u0‖ := hu
  have hμ10 : μ ≤ 10 := by
    have hnorm : ‖b - inner ℝ a b • a‖ ≤ 10 := by
      calc
        ‖b - inner ℝ a b • a‖ ≤ ‖b‖ + ‖inner ℝ a b • a‖ := norm_sub_le _ _
        _ = ‖b‖ + ‖inner ℝ a b‖ * ‖a‖ := by rw [norm_smul]
        _ ≤ ‖b‖ + (‖a‖ * ‖b‖) * ‖a‖ := by
          have hinner : ‖inner ℝ a b‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm _ _
          gcongr
        _ ≤ 2 + (2 * 2) * 2 := by
          gcongr
        _ = 10 := by norm_num
    exact le_trans hu hnorm
  have hne : ‖e0‖ ≤ 1 := by
    dsimp [e0]
    have hpos : 0 < ‖u0‖ := by linarith [hμ, hμu]
    rw [norm_smul, norm_inv]
    have : ‖(‖u0‖ : ℝ)‖ = ‖u0‖ := abs_of_pos hpos
    rw [this]
    exact (inv_mul_cancel₀ hpos.ne.symm).le
  have he_sub : ‖e - e0‖ ≤ 40 * ρ / μ := lc_e1_sub hu_sub hμ hμu
  have hcoord := lc_coord_sub ha hq hρ1 hna hnq hμ hμ10 hsmall he_sub hne
  rcases hcoord with ⟨h1, h2, h3⟩
  have hdiff : tieNormalize za zb mirror zq - tieNormalize a b mirror q =
      !₂[inner ℝ zq e - inner ℝ q e0,
        ((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
          ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0)),
        inner ℝ zq za - inner ℝ q a] := by
    ext i
    fin_cases i <;> simp [tieNormalize, u, u0, e, e0]
  rw [hdiff]
  have h_bound : ‖(!₂[inner ℝ zq e - inner ℝ q e0,
      ((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
        ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0)),
      inner ℝ zq za - inner ℝ q a] : EuclideanSpace ℝ (Fin 3))‖ ≤
      |inner ℝ zq e - inner ℝ q e0| + |((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
        ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0))| + |inner ℝ zq za - inner ℝ q a| :=
    lc_norm3_le _ _ _
  refine le_trans h_bound ?_
  have h2' : |((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
      ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0))| ≤ 400 * ρ / μ := by
    have : ((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
        ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0)) =
        (if mirror then -1 else 1 : ℝ) * (inner ℝ zq (cross za e) - inner ℝ q (cross a e0)) := by ring
    rw [this]
    rw [abs_mul]
    have h_abs_s : |(if mirror then -1 else 1 : ℝ)| = 1 := by
      cases mirror <;> norm_num
    rw [h_abs_s, one_mul]
    exact h2
  have hsum : |inner ℝ zq e - inner ℝ q e0| + |((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
      ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0))| + |inner ℝ zq za - inner ℝ q a| ≤
      100 * ρ / μ + 400 * ρ / μ + 100 * ρ / μ := by
    nlinarith
  have hsum' : 100 * ρ / μ + 400 * ρ / μ + 100 * ρ / μ = 600 * ρ / μ := by ring
  have hsum600 : |inner ℝ zq e - inner ℝ q e0| + |((if mirror then -1 else 1 : ℝ) * inner ℝ zq (cross za e)) -
      ((if mirror then -1 else 1 : ℝ) * inner ℝ q (cross a e0))| + |inner ℝ zq za - inner ℝ q a| ≤
      600 * ρ / μ := by
    linarith
  have hfinal : 600 * ρ / μ ≤ 1000 * ρ / μ := by
    have hρ_nonneg : 0 ≤ ρ := (norm_nonneg _).trans ha
    have h_div_nonneg : 0 ≤ ρ / μ := div_nonneg hρ_nonneg hμ.le
    have e6 : 600 * ρ / μ = 600 * (ρ / μ) := by ring
    have e10 : 1000 * ρ / μ = 1000 * (ρ / μ) := by ring
    rw [e6, e10]
    linarith
  exact le_trans hsum600 hfinal

theorem lc_box_norm (z : EuclideanSpace ℝ (Fin 3)) (m r : Fin 3 → ℝ) (h : ∀ l, |z.ofLp l - m l| ≤ r l) :
    ‖z - !₂[m 0, m 1, m 2]‖ ≤ r 0 + r 1 + r 2 := by
  have e : z - !₂[m 0, m 1, m 2] = !₂[z.ofLp 0 - m 0, z.ofLp 1 - m 1, z.ofLp 2 - m 2] := by
    ext i
    fin_cases i <;> simp
  rw [e]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  exact (lc_norm3_le _ _ _).trans (by linarith)

theorem lc_mid_close {A B C t l1 l2 s : ℝ} (ht1 : l1 ≤ t) (ht2 : t ≤ l2) (hs : |s| = 1) :
    ‖(!₂[A * t, s * (B * t), C] : EuclideanSpace ℝ (Fin 3)) - !₂[A * l1, s * (B * l1), C]‖ ≤
      (l2 - l1) * (|A| + |B|) := by
  have e : (!₂[A * t, s * (B * t), C] : EuclideanSpace ℝ (Fin 3)) - !₂[A * l1, s * (B * l1), C] =
      !₂[A * (t - l1), s * (B * (t - l1)), 0] := by
    ext i
    fin_cases i <;> simp <;> ring
  rw [e]
  refine (lc_norm3_le _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, hs, abs_zero, abs_of_nonneg (sub_nonneg.mpr ht1)]
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  nlinarith

end Tammes15.D3Kernel.Kinds
