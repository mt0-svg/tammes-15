import Tammes15.Params.Defs
import Tammes15.Geom.Nor

/-!
# Generic bounds for params_check

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

/-- A lower bound of `P(l, h)` from bounds of its three pieces. -/
theorem Pform_ge {l h x y s p : ℝ} (hA : (cos l - sin h ^ 2) / cos h ^ 2 ≤ cos x) (hx0 : 0 ≤ x)
    (hxπ : x ≤ π) (hB : tan h * tan (l / 2) ≤ sin y) (hy0 : 0 ≤ y) (hyπ : y ≤ π / 2) (hs : s ≤ sin h)
    (hs0 : 0 ≤ s) (hp : p ≤ π) (hpy : 2 * y ≤ p) : 2 * x + 2 * s * (p - 2 * y) ≤ Pform l h := by
  set A := (cos l - sin h ^ 2) / cos h ^ 2
  set B := tan h * tan (l / 2)
  have hx_le_arccos_A : x ≤ arccos A := by
    have h1 : arccos (cos x) ≤ arccos A := Real.arccos_le_arccos hA
    have h2 : arccos (cos x) = x := Real.arccos_cos hx0 hxπ
    linarith
  have h_arcsin_B_le_y : arcsin B ≤ y := by
    have h1 : arcsin B ≤ arcsin (sin y) := Real.arcsin_le_arcsin hB
    have h2 : arcsin (sin y) = y := Real.arcsin_sin (by linarith) hyπ
    linarith
  have h_nonneg_diff : 0 ≤ p - 2 * y := by linarith
  have h_sin_h_nonneg : 0 ≤ sin h := by linarith
  have h_diff_le : p - 2 * y ≤ π - 2 * arcsin B := by
    have h1 : p - 2 * y ≤ π - 2 * y := by linarith
    have h2 : π - 2 * y ≤ π - 2 * arcsin B := by
      linarith
    linarith
  have h_mul : s * (p - 2 * y) ≤ sin h * (π - 2 * arcsin B) := by
    exact mul_le_mul hs h_diff_le h_nonneg_diff h_sin_h_nonneg
  have h_goal : 2 * x + 2 * s * (p - 2 * y) ≤ 2 * arccos A + 2 * sin h * (π - 2 * arcsin B) := by
    nlinarith
  simpa [Tammes15.Params.Pform, A, B] using h_goal

/-- The arccos argument of `P(l, h(l))` from bounds `cos (l / 2) ≤ e2 ≤ 1`. -/
theorem hrad_A_le {l e1 e2 : ℝ} (hl0 : 0 < l) (hl : l < π / 2) (he1 : e1 ≤ cos (l / 2))
    (he2 : cos (l / 2) ≤ e2) (he21 : e2 ≤ 1) (he10 : 0 < e1) (hc1 : 0 < 2 * e1 ^ 2 - 1) :
    (cos l - sin (hrad l) ^ 2) / cos (hrad l) ^ 2 ≤
      1 - (2 - 2 * e2 ^ 2) * e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2 := by
  set e := cos (l / 2) with he
  set c := cos l with hc
  set C := cos (hrad l) with hC
  have hd : 0 < l ∧ l < π / 2 := ⟨hl0, hl⟩
  have hC_eq : C = c / e := by
    rw [hC, hc, he, Tammes15.Geom.cos_hrad l hd]
  have he_pos : 0 < e := by
    rw [he]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have he_nonneg : 0 ≤ e := he_pos.le
  have hc_pos : 0 < c := by
    rw [hc]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hl⟩
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hc_eq : c = 2 * e ^ 2 - 1 := by
    rw [hc, he]
    calc
      cos l = cos (2 * (l / 2)) := by ring_nf
      _ = 2 * cos (l / 2) ^ 2 - 1 := by rw [Real.cos_two_mul]
      _ = 2 * e ^ 2 - 1 := by rw [he]
  have he_le_one : e ≤ 1 := by
    rw [he]
    exact Real.cos_le_one (l / 2)
  have he2_nonneg : 0 ≤ e2 := by linarith
  have he2_pos : 0 < e2 := by linarith
  have he2_ge_e : e ≤ e2 := by
    rw [he]
    exact he2
  have hC_pos : 0 < C := by
    rw [hC_eq]
    exact div_pos hc_pos he_pos
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have h_sin_sq : sin (hrad l) ^ 2 = 1 - C ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (hrad l)
    rw [← hC] at h
    linarith
  have h_left : (cos l - sin (hrad l) ^ 2) / cos (hrad l) ^ 2 = 1 - (1 - c) / C ^ 2 := by
    rw [hc, ← hC, h_sin_sq]
    field_simp [hC_pos.ne']
    ring_nf
  rw [h_left]
  have h_one_minus_c_nonneg : 0 ≤ 1 - c := by
    rw [hc_eq]
    have he_sq_le_one : e ^ 2 ≤ 1 := by
      nlinarith
    nlinarith
  have h_one_minus_c_ge : 2 - 2 * e2 ^ 2 ≤ 1 - c := by
    rw [hc_eq]
    have he_sq_le_e2_sq : e ^ 2 ≤ e2 ^ 2 := by
      simpa [sq] using mul_self_le_mul_self he_nonneg he2_ge_e
    nlinarith
  have h_denom_pos : 0 < C ^ 2 := pow_pos hC_pos 2
  have h_denom_pos' : 0 < (2 * e2 ^ 2 - 1) ^ 2 := by
    have h_pos : 0 < 2 * e2 ^ 2 - 1 := by
      have he1_sq_le_e2_sq : e1 ^ 2 ≤ e2 ^ 2 := by
        have he1_nonneg : 0 ≤ e1 := by linarith
        simpa [sq] using mul_self_le_mul_self he1_nonneg (he1.trans he2)
      linarith
    exact pow_pos h_pos 2
  have h_denom_pos'' : 0 < e2 ^ 2 := pow_pos he2_pos 2
  have hC_le : C ≤ (2 * e2 ^ 2 - 1) / e2 := by
    rw [hC_eq, hc_eq]
    refine (div_le_div_iff₀ he_pos he2_pos).mpr ?_
    have h_nonneg_prod : 0 ≤ 2 * e * e2 := by nlinarith
    have h_diff_nonpos : e - e2 ≤ 0 := by linarith
    nlinarith
  have hC_nonneg_div : 0 ≤ (2 * e2 ^ 2 - 1) / e2 := by
    refine div_nonneg ?_ he2_nonneg
    have h_pos : 0 < 2 * e2 ^ 2 - 1 := by
      have he1_sq_le_e2_sq : e1 ^ 2 ≤ e2 ^ 2 := by
        have he1_nonneg : 0 ≤ e1 := by linarith
        simpa [sq] using mul_self_le_mul_self he1_nonneg (he1.trans he2)
      linarith
    linarith
  have hC_sq_le : C ^ 2 ≤ ((2 * e2 ^ 2 - 1) / e2) ^ 2 :=
    (sq_le_sq₀ hC_nonneg hC_nonneg_div).mpr hC_le
  have hC_sq_le' : C ^ 2 ≤ (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2 := by
    rw [div_pow] at hC_sq_le
    exact hC_sq_le
  have h_div_pos : 0 < (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2 :=
    div_pos h_denom_pos' h_denom_pos''
  have h_recip_ineq : e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2 ≤ 1 / C ^ 2 := by
    have h_eq : e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2 = 1 / ((2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2) := by
      field_simp [h_denom_pos''.ne', h_denom_pos'.ne']
    rw [h_eq]
    exact (one_div_le_one_div h_div_pos h_denom_pos).mpr hC_sq_le'
  have h_main : (1 - c) / C ^ 2 ≥ (2 - 2 * e2 ^ 2) * e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2 := by
    calc
      (1 - c) / C ^ 2 = (1 - c) * (1 / C ^ 2) := by rw [div_eq_mul_one_div]
      _ ≥ (1 - c) * (e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h_recip_ineq h_one_minus_c_nonneg
      _ = (e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2) * (1 - c) := by ring
      _ ≥ (e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2) * (2 - 2 * e2 ^ 2) :=
        mul_le_mul_of_nonneg_left h_one_minus_c_ge (div_nonneg (by positivity) (by positivity))
      _ = (2 - 2 * e2 ^ 2) * e2 ^ 2 / (2 * e2 ^ 2 - 1) ^ 2 := by ring
  exact sub_le_sub_left h_main 1

/-- The arcsin argument of `P(l, h(l))`: `tan h tan (l / 2) = sin h sin (l / 2) / cos l`. -/
theorem hrad_B_le {l e1 f2 s2 : ℝ} (hl0 : 0 < l) (hl : l < π / 2) (he1 : e1 ≤ cos (l / 2))
    (hf2 : sin (l / 2) ≤ f2) (he10 : 0 < e1) (hc1 : 0 < 2 * e1 ^ 2 - 1) (hs2 : 0 ≤ s2)
    (hs2' : 1 - (2 * e1 ^ 2 - 1) ^ 2 / e1 ^ 2 ≤ s2 ^ 2) :
    tan (hrad l) * tan (l / 2) ≤ s2 * f2 / (2 * e1 ^ 2 - 1) := by
  set e := cos (l / 2) with he_def
  set f := sin (l / 2) with hf_def
  have he_pos : 0 < e := by
    refine Real.cos_pos_of_mem_Ioo ?_
    constructor <;> linarith
  have hf_pos : 0 < f := by
    refine Real.sin_pos_of_mem_Ioo ?_
    constructor <;> linarith
  have hcosl_eq : cos l = 2 * e ^ 2 - 1 := by
    calc
      cos l = cos (2 * (l / 2)) := by ring_nf
      _ = 2 * cos (l / 2) ^ 2 - 1 := by rw [Real.cos_two_mul]
      _ = 2 * e ^ 2 - 1 := by rw [he_def]
  have hcos_hrad : cos (hrad l) = cos l / e := by
    rw [Tammes15.Geom.cos_hrad l ⟨hl0, hl⟩, he_def]
  let c := cos l
  let C := cos (hrad l)
  let S := sin (hrad l)
  have hc_eq : c = 2 * e ^ 2 - 1 := by
    dsimp [c]; rw [hcosl_eq]
  have hC_eq : C = c / e := hcos_hrad
  have hc_pos : 0 < c := by
    rw [hc_eq]
    have he_sq_ge : e1 ^ 2 ≤ e ^ 2 := by
      nlinarith
    nlinarith
  have hC_nonneg : 0 ≤ C := by
    rw [hC_eq]
    refine div_nonneg (by linarith) (by linarith)
  have hC_le_one : C ≤ 1 := by
    dsimp [C]
    exact Real.cos_le_one _
  have hS_sq_eq : S ^ 2 = 1 - C ^ 2 := by
    dsimp [S]
    rw [Real.sin_sq]
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hC_ge : (2 * e1 ^ 2 - 1) / e1 ≤ C := by
    rw [hC_eq, hc_eq]
    -- Goal: (2*e1^2-1)/e1 ≤ (2*e^2-1)/e
    field_simp [ne_of_gt he10, ne_of_gt he_pos]
    -- Goal: (2*e1^2-1)*e ≤ (2*e^2-1)*e1
    have h_diff : (2 * e ^ 2 - 1) * e1 - (2 * e1 ^ 2 - 1) * e = (e - e1) * (2 * e * e1 + 1) := by ring
    have h_nonneg : 0 ≤ (2 * e ^ 2 - 1) * e1 - (2 * e1 ^ 2 - 1) * e := by
      rw [h_diff]
      have h1 : 0 ≤ e - e1 := by linarith
      have h2 : 0 ≤ 2 * e * e1 + 1 := by nlinarith
      exact mul_nonneg h1 h2
    linarith
  have hS_sq_le : S ^ 2 ≤ s2 ^ 2 := by
    rw [hS_sq_eq]
    -- Goal: 1 - C^2 ≤ s2^2
    -- From hC_ge: (2*e1^2-1)/e1 ≤ C, both sides nonnegative
    have h_nonneg : 0 ≤ (2 * e1 ^ 2 - 1) / e1 := by
      refine div_nonneg ?_ (by linarith)
      linarith
    have hC_sq_ge : ((2 * e1 ^ 2 - 1) / e1) ^ 2 ≤ C ^ 2 := by
      nlinarith
    have h_sq_eq : (2 * e1 ^ 2 - 1) ^ 2 / e1 ^ 2 = ((2 * e1 ^ 2 - 1) / e1) ^ 2 := by ring
    have h1 : 1 - C ^ 2 ≤ 1 - ((2 * e1 ^ 2 - 1) / e1) ^ 2 := by nlinarith
    have h2 : 1 - ((2 * e1 ^ 2 - 1) / e1) ^ 2 ≤ s2 ^ 2 := by
      rw [← h_sq_eq]
      exact hs2'
    linarith
  have hS_le_s2 : S ≤ s2 := by
    have := (sq_le_sq₀ hS_nonneg hs2).mp
    exact this hS_sq_le
  have hc_ge : 2 * e1 ^ 2 - 1 ≤ c := by
    rw [hc_eq]
    have he_sq_ge : e1 ^ 2 ≤ e ^ 2 := by
      nlinarith
    nlinarith
  have h_tan_prod : tan (hrad l) * tan (l / 2) = S * f / c := by
    calc
      tan (hrad l) * tan (l / 2) = (sin (hrad l) / cos (hrad l)) * (sin (l / 2) / cos (l / 2)) := by
        simp_rw [Real.tan_eq_sin_div_cos]
      _ = (S / C) * (f / e) := by simp_rw [S, C, f, e]
      _ = S * f / (C * e) := by ring
      _ = S * f / c := by
        rw [hC_eq]
        field_simp [ne_of_gt he_pos]
  rw [h_tan_prod]
  have hpos_denom : 0 < 2 * e1 ^ 2 - 1 := hc1
  field_simp [ne_of_gt hc_pos, ne_of_gt hpos_denom]
  -- Goal: S * f * (2 * e1 ^ 2 - 1) ≤ c * s2 * f2
  have h_mul : S * f ≤ s2 * f2 := by
    have hf_nonneg : 0 ≤ f := by linarith
    exact mul_le_mul hS_le_s2 hf2 hf_nonneg hs2
  have h_nonneg_denom : 0 ≤ 2 * e1 ^ 2 - 1 := by linarith
  have h_nonneg_s2f2 : 0 ≤ s2 * f2 := by
    have hf2_nonneg : 0 ≤ f2 := by linarith
    exact mul_nonneg hs2 hf2_nonneg
  have h_final : S * f * (2 * e1 ^ 2 - 1) ≤ s2 * f2 * c := by
    have h := mul_le_mul h_mul hc_ge h_nonneg_denom h_nonneg_s2f2
    -- h: (S*f)*(2*e1^2-1) ≤ (s2*f2)*c
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_final

/-- A lower bound of `sin h(l)` from `cos (l / 2) ≤ e2`. -/
theorem le_sin_hrad {l e2 s1 : ℝ} (hl0 : 0 < l) (hl : l < π / 2) (he2 : cos (l / 2) ≤ e2)
    (he20 : 0 < 2 * e2 ^ 2 - 1) (hs1 : 0 ≤ s1) (hs1' : s1 ^ 2 ≤ 1 - (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2) :
    s1 ≤ sin (hrad l) := by
  set e := cos (l / 2) with he
  have he_pos : 0 < e := by
    rw [he]
    exact cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : cos l = 2 * e ^ 2 - 1 := by
    calc
      cos l = cos (2 * (l / 2)) := by ring_nf
      _ = 2 * cos (l / 2) ^ 2 - 1 := by rw [Real.cos_two_mul]
      _ = 2 * e ^ 2 - 1 := by rw [he]
  have hc_pos : 0 < cos l :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h_ratio_pos : 0 < cos l / cos (l / 2) := div_pos hc_pos he_pos
  have h_ratio_lt_one : cos l / cos (l / 2) < 1 := by
    refine (div_lt_one ?_).mpr ?_
    · exact he_pos
    · have : cos l < cos (l / 2) := by
        refine cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) ?_
        linarith
      linarith
  have h_ratio_ge_neg_one : -1 ≤ cos l / cos (l / 2) := by
    linarith
  have hcos_hrad : cos (hrad l) = cos l / cos (l / 2) :=
    Real.cos_arccos h_ratio_ge_neg_one (by linarith)
  have hsin_hrad_nonneg : 0 ≤ sin (hrad l) := by
    have h0 : 0 ≤ hrad l := Real.arccos_nonneg _
    have hpi : hrad l ≤ π := Real.arccos_le_pi _
    exact Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi
  have h_sq_eq : sin (hrad l) ^ 2 = 1 - (cos l / cos (l / 2)) ^ 2 := by
    rw [Real.sin_sq, hcos_hrad]
  have hC_le_Cmax : cos l / cos (l / 2) ≤ (2 * e2 ^ 2 - 1) / e2 := by
    have he2_pos : 0 < e2 := by
      by_contra! h
      have : e ≤ 0 := by linarith
      have : 0 < e := he_pos
      linarith
    rw [hc, he]
    have h_mul : (2 * e ^ 2 - 1) * e2 ≤ (2 * e2 ^ 2 - 1) * e := by
      have : (e - e2) * (2 * e * e2 + 1) ≤ 0 := by
        have h_nonpos : e - e2 ≤ 0 := by linarith
        have h_pos' : 0 ≤ 2 * e * e2 + 1 := by nlinarith
        nlinarith
      nlinarith
    have h := calc
      ((2 * e ^ 2 - 1) / e) * (e * e2) = (2 * e ^ 2 - 1) * e2 := by field_simp [he_pos.ne.symm]
      _ ≤ (2 * e2 ^ 2 - 1) * e := h_mul
      _ = ((2 * e2 ^ 2 - 1) / e2) * (e * e2) := by field_simp [he2_pos.ne.symm]
    exact le_of_mul_le_mul_right h (by positivity : 0 < e * e2)
  have hS_sq_ge : s1 ^ 2 ≤ sin (hrad l) ^ 2 := by
    have h_sq_le' : (cos l / cos (l / 2)) ^ 2 ≤ (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2 := by
      have h_sq_le : (cos l / cos (l / 2)) ^ 2 ≤ ((2 * e2 ^ 2 - 1) / e2) ^ 2 := by
        have hpos_ratio : 0 ≤ cos l / cos (l / 2) := by linarith
        have hpos_max : 0 ≤ (2 * e2 ^ 2 - 1) / e2 := by
          have hpos_e2 : 0 < e2 := by
            by_contra! h
            have : 2 * e2 ^ 2 - 1 ≤ 0 := by nlinarith
            linarith
          positivity
        nlinarith
      have h_eq : ((2 * e2 ^ 2 - 1) / e2) ^ 2 = (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2 := by ring
      rw [h_eq] at h_sq_le
      exact h_sq_le
    calc
      s1 ^ 2 ≤ 1 - (2 * e2 ^ 2 - 1) ^ 2 / e2 ^ 2 := hs1'
      _ ≤ 1 - (cos l / cos (l / 2)) ^ 2 := by linarith
      _ = sin (hrad l) ^ 2 := by rw [h_sq_eq]
  exact le_of_sq_le_sq hS_sq_ge hsin_hrad_nonneg

end Tammes15.Params
