import Tammes15.Params.Defs
import Tammes15.Geom.Nor

/-!
# Generic bounds for the parameter inequalities

Each check of Checks.lean follows from rational bounds on `cos` and `sin` at explicit points (the Taylor bounds of
Numerics/Taylor.lean) through one of these lemmas, stated on variables.
-/

open Real

namespace Tammes15.Params

/-- A lower bound of `α(d) = arccos (cos d / (1 + cos d))` from an upper bound of `cos d`. -/
theorem le_alpha_of {d a cU : ℝ} (hc0 : 0 < cos d) (hc : cos d ≤ cU) (ha0 : 0 ≤ a) (haπ : a ≤ π)
    (h : cU / (1 + cU) ≤ cos a) : a ≤ alpha d := by
  have hpos1 : 0 < 1 + cos d := by linarith
  have hpos2 : 0 < 1 + cU := by linarith
  have hdiv : cos d / (1 + cos d) ≤ cU / (1 + cU) := by
    field_simp [hpos1.ne.symm, hpos2.ne.symm]
    nlinarith
  have hcos_le : cos d / (1 + cos d) ≤ cos a :=
    le_trans hdiv h
  calc
    a = arccos (cos a) := by rw [Real.arccos_cos ha0 haπ]
    _ ≤ arccos (cos d / (1 + cos d)) := Real.arccos_le_arccos hcos_le
    _ = alpha d := rfl

/-- An upper bound of `α(d)` from a lower bound of `cos d`. -/
theorem alpha_le_of {d a cL : ℝ} (hcL : 0 < cL) (hc : cL ≤ cos d) (ha0 : 0 ≤ a) (haπ : a ≤ π)
    (h : cos a ≤ cL / (1 + cL)) : alpha d ≤ a := by
  unfold alpha
  have h_denom : cL / (1 + cL) ≤ cos d / (1 + cos d) := by
    have hpos_cL' : 0 < 1 + cL := by linarith
    have hpos_cosd' : 0 < 1 + cos d := by linarith
    field_simp [ne_of_gt hpos_cL', ne_of_gt hpos_cosd']
    nlinarith
  have h_cos_a_le : cos a ≤ cos d / (1 + cos d) := by
    linarith
  have h_arccos_le : arccos (cos d / (1 + cos d)) ≤ arccos (cos a) :=
    Real.arccos_le_arccos h_cos_a_le
  have h_arccos_cos_a : arccos (cos a) = a :=
    Real.arccos_cos ha0 haπ
  linarith

/-- An upper bound of `smax d = 4 atan (1 / √(cos d))`: `1 / √(cos d) ≤ tan s`. -/
theorem smax_le_of {d s cL Cu Sl : ℝ} (hcL : 0 < cL) (hc : cL ≤ cos d) (hs0 : 0 < s) (hs : s < π / 2)
    (hCu : cos s ≤ Cu) (hSl : Sl ≤ sin s) (hSl0 : 0 < Sl) (h : Cu ^ 2 ≤ cL * Sl ^ 2) :
    smax d ≤ 4 * s := by
  dsimp [smax]
  have hcosd_pos : 0 < cos d := by linarith
  have hcos_s_pos : 0 < cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith, hs⟩
  have hsin_s_pos : 0 < sin s := Real.sin_pos_of_mem_Ioo ⟨hs0, by linarith [hs]⟩
  have hsqrt_cosd_pos : 0 < √(cos d) := Real.sqrt_pos.mpr hcosd_pos
  have harctan_tan : arctan (tan s) = s := Real.arctan_tan (by linarith) hs
  have h_main : 1 / √(cos d) ≤ tan s := by
    rw [Real.tan_eq_sin_div_cos]
    rw [div_le_div_iff₀ hsqrt_cosd_pos hcos_s_pos]
    -- goal: 1 * cos s ≤ sin s * √(cos d)
    simp only [one_mul]
    -- goal: cos s ≤ sin s * √(cos d)
    have hcos_s_sq_le : cos s ^ 2 ≤ cos d * sin s ^ 2 := by
      have h1 : cos s ^ 2 ≤ Cu ^ 2 := by
        have hcos_s_nonneg : 0 ≤ cos s := by linarith
        nlinarith
      have h2 : Cu ^ 2 ≤ cL * Sl ^ 2 := h
      have h3 : cL * Sl ^ 2 ≤ cos d * sin s ^ 2 := by
        have hcL_nonneg : 0 ≤ cL := by linarith
        have hSl_sq_le : Sl ^ 2 ≤ sin s ^ 2 := by
          have hSl_nonneg : 0 ≤ Sl := by linarith
          nlinarith
        nlinarith
      nlinarith
    have hcosd_nonneg : 0 ≤ cos d := by linarith
    have hcos_s_nonneg : 0 ≤ cos s := by linarith
    have hsin_s_nonneg : 0 ≤ sin s := by linarith
    have h_sq_eq : cos d * sin s ^ 2 = (√(cos d) * sin s) ^ 2 := by
      calc
        cos d * sin s ^ 2 = ((√(cos d)) ^ 2) * sin s ^ 2 := by rw [Real.sq_sqrt hcosd_nonneg]
        _ = (√(cos d) * sin s) ^ 2 := by ring
    rw [h_sq_eq] at hcos_s_sq_le
    -- cos s ^ 2 ≤ (√(cos d) * sin s) ^ 2, both sides nonnegative → cos s ≤ √(cos d) * sin s
    have h_nonneg_prod : 0 ≤ √(cos d) * sin s := by
      have hsqrt_nonneg : 0 ≤ √(cos d) := Real.sqrt_nonneg _
      nlinarith
    nlinarith
  have harctan_le : arctan (1 / √(cos d)) ≤ arctan (tan s) :=
    Real.arctan_mono h_main
  rw [harctan_tan] at harctan_le
  nlinarith

/-- The quintic increases on `[1/2, 7/10]`: a point where it is negative lies below its root. -/
theorem lt_of_quintic_neg {u c : ℝ} (h1 : 1 / 2 < u) (h2 : u < 7 / 10) (hc1 : 1 / 2 ≤ c)
    (hc2 : c ≤ 7 / 10) (h0 : quintic u = 0) (hc : quintic c < 0) : c < u := by
  by_contra hcu'
  have hcu : u ≤ c := not_lt.mp hcu'
  have hP : 0 < 13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3 := by
    have hu0 : 0 < u := by linarith
    have hc0 : 0 < c := by linarith
    have e1 : u ^ 3 ≤ 343 / 1000 := by nlinarith [pow_le_pow_left₀ hu0.le h2.le 3]
    have e2 : c ^ 3 ≤ 343 / 1000 := by nlinarith [pow_le_pow_left₀ hc0.le hc2 3]
    have e3 : u ^ 2 * c ≤ 343 / 1000 := by
      have := mul_le_mul (pow_le_pow_left₀ hu0.le h2.le 2) hc2 hc0.le (by positivity); nlinarith
    have e4 : u * c ^ 2 ≤ 343 / 1000 := by
      have := mul_le_mul h2.le (pow_le_pow_left₀ hc0.le hc2 2) (by positivity) (by norm_num); nlinarith
    have f1 : 0 ≤ u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4 := by positivity
    have f2 : 3 / 4 ≤ u ^ 2 + u * c + c ^ 2 := by nlinarith
    nlinarith
  have hdiff : (quintic u) - (quintic c) = (u - c) *
      (13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3) := by
    unfold quintic; ring
  rw [h0] at hdiff
  have h_nonpos : (u - c) *
      (13 * (u ^ 4 + u ^ 3 * c + u ^ 2 * c ^ 2 + u * c ^ 3 + c ^ 4) -
      (u ^ 3 + u ^ 2 * c + u * c ^ 2 + c ^ 3) + 6 * (u ^ 2 + u * c + c ^ 2) + 2 * (u + c) - 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hP.le
  linarith

/-- The Fejes Tóth value `arccos ((cot² ω - 1) / 2)`, `ω = 15π / 78`, lies below `d` if
`cos d < 1 / (2 sin² ω) - 1`. -/
theorem ft_lt_of {d SU cU : ℝ} (hd0 : 0 < d) (hdπ : d ≤ π) (hS : sin (15 * π / (6 * 13)) ≤ SU)
    (hc : cos d ≤ cU) (h : cU < 1 / (2 * SU ^ 2) - 1) :
    arccos ((cot (15 * π / (6 * 13)) ^ 2 - 1) / 2) < d := by
  let ω := 15 * π / (6 * 13)
  have hω_pos : 0 < ω := by
    positivity
  have hω_lt_pi_div_two : ω < π / 2 := by
    have h_ratio : (15 : ℝ) / (6 * 13) < 1 / 2 := by norm_num
    calc
      ω = ((15 : ℝ) / (6 * 13)) * π := by ring
      _ < (1 / 2) * π := by nlinarith [Real.pi_pos]
      _ = π / 2 := by ring
  have hω_lt_pi : ω < π := by linarith
  have hsin_ω_pos : Real.sin ω > 0 :=
    Real.sin_pos_of_pos_of_lt_pi hω_pos hω_lt_pi
  have hSU_pos : 0 < SU := lt_of_lt_of_le hsin_ω_pos hS
  have hsin_sq_le_SU_sq : Real.sin ω ^ 2 ≤ SU ^ 2 := by
    have hS' : Real.sin ω ≤ SU := hS
    nlinarith
  have h_identity : (Real.cot ω ^ 2 - 1) / 2 = 1 / (2 * Real.sin ω ^ 2) - 1 := by
    rw [Real.cot_eq_cos_div_sin ω]
    field_simp [hsin_ω_pos.ne.symm]
    nlinarith [Real.cos_sq_add_sin_sq ω]
  have hy_lt : Real.cos d < (Real.cot ω ^ 2 - 1) / 2 := by
    calc
      Real.cos d ≤ cU := hc
      _ < 1 / (2 * SU ^ 2) - 1 := h
      _ ≤ 1 / (2 * Real.sin ω ^ 2) - 1 := by
        have hdiv : 1 / (2 * SU ^ 2) ≤ 1 / (2 * Real.sin ω ^ 2) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
        linarith
      _ = (Real.cot ω ^ 2 - 1) / 2 := by rw [h_identity]
  by_cases hy_le_one : (Real.cot ω ^ 2 - 1) / 2 ≤ 1
  · -- case y ≤ 1
    have h_arccos_lt : Real.arccos ((Real.cot ω ^ 2 - 1) / 2) < Real.arccos (Real.cos d) :=
      Real.arccos_lt_arccos (Real.neg_one_le_cos d) hy_lt hy_le_one
    have h_arccos_cos_d : Real.arccos (Real.cos d) = d :=
      Real.arccos_cos (by linarith) hdπ
    rw [h_arccos_cos_d] at h_arccos_lt
    exact h_arccos_lt
  · -- case 1 < y
    have hy_ge_one : 1 ≤ (Real.cot ω ^ 2 - 1) / 2 := by linarith
    have h_arccos_eq_zero : Real.arccos ((Real.cot ω ^ 2 - 1) / 2) = 0 :=
      Real.arccos_of_one_le hy_ge_one
    rw [h_arccos_eq_zero]
    exact hd0

end Tammes15.Params
