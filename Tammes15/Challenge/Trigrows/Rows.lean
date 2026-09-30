import Tammes15.Challenge.Trigrows.Mono

/-!
# Rows 5.2, (T1) to (T4), Lemma alpha, Lemma edge: the real part

`rhombus_rows` gives the rhombus rows of Section 5.2; the four
`rhombus_row_*` lemmas are its cut points.
-/

open Real

namespace Tammes15

theorem alpha_bounds (d : ℝ) (hd : 0 < d ∧ d < π / 2) : π / 3 < alpha d ∧ alpha d < π / 2 := by
  rcases hd with ⟨hd_left, hd_right⟩
  have hc_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc_lt_one : cos d < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) hd_left
    simpa [Real.cos_zero] using this
  have h_denom_pos : 0 < 1 + cos d := by linarith
  have ht_pos : 0 < cos d / (1 + cos d) := div_pos hc_pos h_denom_pos
  have ht_lt_half : cos d / (1 + cos d) < 1/2 := by
    apply (div_lt_div_iff₀ h_denom_pos (by norm_num : 0 < (2 : ℝ))).mpr
    nlinarith
  have ht_le_one : cos d / (1 + cos d) ≤ 1 := by
    rw [div_le_one h_denom_pos]
    linarith
  have harccos_half : arccos (1/2 : ℝ) = π/3 := by
    refine Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) ?_
    rw [Real.cos_pi_div_three]
  have h_lower : π/3 < alpha d := by
    rw [alpha, ← harccos_half]
    exact Real.arccos_lt_arccos (by linarith) ht_lt_half (by linarith)
  have h_upper : alpha d < π/2 := by
    rw [alpha, ← Real.arccos_zero]
    exact Real.arccos_lt_arccos (by linarith) ht_pos ht_le_one
  exact And.intro h_lower h_upper

theorem ebase_mem_Ioo (d u : ℝ) (hd : 0 < d ∧ d < π / 2) (hu : 0 < u ∧ u ≤ π) :
    0 < ebase d u ∧ ebase d u < π := by
  rcases hd with ⟨hd_left, hd_right⟩
  rcases hu with ⟨hu_left, hu_right⟩
  have hd_pos : 0 < sin d := by
    have hx : -(π / 2) ≤ (0 : ℝ) := by linarith [pi_pos]
    have hy : d ≤ π / 2 := hd_right.le
    have hlt : (0 : ℝ) < d := hd_left
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two hx hy hlt
    simpa [Real.sin_zero] using this
  have hd_lt_one : sin d < 1 := by
    have hx : -(π / 2) ≤ d := by linarith [pi_pos]
    have hy : π / 2 ≤ π / 2 := le_refl _
    have hlt : d < π / 2 := hd_right
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hx hy hlt
    simpa [Real.sin_pi_div_two] using h
  have hhalf_pos : 0 < u / 2 := by linarith
  have hhalf_lt_pi : u / 2 < π := by linarith
  have hhalf_u_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt_pi
  have hhalf_u_le_one : sin (u / 2) ≤ 1 := Real.sin_le_one _
  have hy_pos : 0 < sin d * sin (u / 2) := mul_pos hd_pos hhalf_u_pos
  have hy_lt_one : sin d * sin (u / 2) < 1 := by
    calc
      sin d * sin (u / 2) < 1 * sin (u / 2) := by
        exact mul_lt_mul_of_pos_right hd_lt_one hhalf_u_pos
      _ = sin (u / 2) := by simp
      _ ≤ 1 := hhalf_u_le_one
  have h_arcsin_pos : 0 < Real.arcsin (sin d * sin (u / 2)) :=
    (Real.arcsin_pos.mpr hy_pos)
  have h_arcsin_lt : Real.arcsin (sin d * sin (u / 2)) < π / 2 :=
    (Real.arcsin_lt_pi_div_two.mpr hy_lt_one)
  have h_ebase_pos : 0 < ebase d u := by
    unfold ebase
    nlinarith
  have h_ebase_lt : ebase d u < π := by
    unfold ebase
    nlinarith
  exact And.intro h_ebase_pos h_ebase_lt

/-- (T1) the base angle as the angle of the isosceles triangle opposite a leg. -/
theorem gam_isosceles_eq_bangle (d u : ℝ) (hd : 0 < d ∧ d < π / 2) (hu : 0 < u ∧ u ≤ π) :
    gam d d (ebase d u) = bangle d u := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hu with ⟨hupos, hule⟩
  set sd := sin d with hsd
  set cd := cos d with hcd
  set su := sin (u / 2) with hsu
  set cu := cos (u / 2) with hcu
  have hdpos' : 0 < d := hdpos
  have hupos' : 0 < u := hupos
  have hd_lt_pi_div_two : d < π / 2 := hdlt
  have hu_le_pi : u ≤ π := hule
  have hsdpos : 0 < sd := sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  have hcdpos : 0 < cd := cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hsu_pos : 0 < su := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcu_nonneg : 0 ≤ cu := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hprod_pos : 0 < sd * su := mul_pos hsdpos hsu_pos
  have hprod_lt_one : sd * su < 1 := by
    have hsd_lt_one : sd < 1 := by
      have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hdlt
      rwa [Real.sin_pi_div_two] at h
    have hsu_le_one : su ≤ 1 := sin_le_one (u / 2)
    nlinarith
  have hprod_ge_neg_one : -1 ≤ sd * su := by linarith
  have hprod_le_one : sd * su ≤ 1 := by linarith
  set e := ebase d u with he
  have he_eq : e = 2 * arcsin (sd * su) := by
    dsimp [e, ebase, sd, su]
  have hsin_half_e : sin (e / 2) = sd * su := by
    rw [he_eq]
    have : (2 * arcsin (sd * su)) / 2 = arcsin (sd * su) := by ring
    rw [this]
    exact Real.sin_arcsin hprod_ge_neg_one hprod_le_one
  have hcos_half_e : cos (e / 2) = Real.sqrt (1 - (sd * su) ^ 2) := by
    rw [he_eq]
    have : (2 * arcsin (sd * su)) / 2 = arcsin (sd * su) := by ring
    rw [this]
    exact Real.cos_arcsin (sd * su)
  have hcos_e : cos e = 1 - 2 * (sd * su) ^ 2 := by
    calc
      cos e = cos (2 * (e / 2)) := by ring_nf
      _ = 2 * cos (e / 2) ^ 2 - 1 := Real.cos_two_mul (e / 2)
      _ = 2 * (Real.sqrt (1 - (sd * su) ^ 2)) ^ 2 - 1 := by rw [hcos_half_e]
      _ = 2 * (1 - (sd * su) ^ 2) - 1 := by
        rw [Real.sq_sqrt (by nlinarith)]
      _ = 1 - 2 * (sd * su) ^ 2 := by ring_nf
  have hsin_e_pos : 0 < sin e := by
    have hsin_e_eq : sin e = 2 * (sd * su) * Real.sqrt (1 - (sd * su) ^ 2) := by
      calc
        sin e = sin (2 * (e / 2)) := by ring_nf
        _ = 2 * sin (e / 2) * cos (e / 2) := Real.sin_two_mul (e / 2)
        _ = 2 * (sd * su) * cos (e / 2) := by rw [hsin_half_e]
        _ = 2 * (sd * su) * Real.sqrt (1 - (sd * su) ^ 2) := by rw [hcos_half_e]
    rw [hsin_e_eq]
    have hsqrt_pos : 0 < Real.sqrt (1 - (sd * su) ^ 2) := by
      refine Real.sqrt_pos.mpr ?_
      nlinarith
    positivity
  have h_sqrt_eq : Real.sqrt (1 - sd ^ 2 * su ^ 2) = Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2) := by
    congr 1
    have h_sd_sq_add_cd_sq : sd ^ 2 + cd ^ 2 = 1 := Real.sin_sq_add_cos_sq d
    have h_su_sq_add_cu_sq : su ^ 2 + cu ^ 2 = 1 := Real.sin_sq_add_cos_sq (u / 2)
    nlinarith
  have h_denom_sin_e : sin e = 2 * (sd * su) * Real.sqrt (1 - (sd * su) ^ 2) := by
    calc
      sin e = sin (2 * (e / 2)) := by ring_nf
      _ = 2 * sin (e / 2) * cos (e / 2) := Real.sin_two_mul (e / 2)
      _ = 2 * (sd * su) * cos (e / 2) := by rw [hsin_half_e]
      _ = 2 * (sd * su) * Real.sqrt (1 - (sd * su) ^ 2) := by rw [hcos_half_e]
  have h_sqrt_eq' : Real.sqrt (1 - (sd * su) ^ 2) = Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2) := by
    have : (sd * su) ^ 2 = sd ^ 2 * su ^ 2 := by ring
    rw [← this] at h_sqrt_eq
    exact h_sqrt_eq
  have h_eta : eta d d e = cd * su / Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2) := by
    dsimp [eta]
    rw [hcos_e, h_denom_sin_e, h_sqrt_eq']
    have h_denom_pos : 0 < sin d * (2 * (sd * su) * Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2)) := by
      positivity
    field_simp [h_denom_pos.ne']
    dsimp [sd, cd]
    have h_sin_d_ne_zero : sin d ≠ 0 := by linarith
    field_simp [h_sin_d_ne_zero]
    ring
  have h_bangle_nonneg : 0 ≤ bangle d u := by
    dsimp [bangle]
    refine arctan_nonneg.mpr ?_
    refine div_nonneg hcu_nonneg (mul_nonneg (by linarith) (by linarith))
  have h_bangle_lt_pi_div_two : bangle d u < π / 2 := by
    dsimp [bangle]
    exact Real.arctan_lt_pi_div_two _
  have h_bangle_le_pi : bangle d u ≤ π := by linarith
  have h_bangle_nonneg' : 0 ≤ bangle d u := h_bangle_nonneg
  have h_cos_bangle : cos (bangle d u) = cd * su / Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2) := by
    dsimp [bangle]
    rw [Real.cos_arctan]
    have hpos_cd_su : 0 < cd * su := mul_pos hcdpos hsu_pos
    have h_denom : Real.sqrt (1 + (cu / (cd * su)) ^ 2) = Real.sqrt (cd ^ 2 * su ^ 2 + cu ^ 2) / (cd * su) := by
      have h_eq : 1 + (cu / (cd * su)) ^ 2 = (cd ^ 2 * su ^ 2 + cu ^ 2) / (cd * su) ^ 2 := by
        field_simp [hpos_cd_su.ne']
      rw [h_eq]
      rw [Real.sqrt_div (by nlinarith) _]
      rw [Real.sqrt_sq (by linarith)]
    rw [h_denom]
    field_simp [hcdpos.ne', hsu_pos.ne']
  have h_eta_eq_cos_bangle : eta d d e = cos (bangle d u) := by
    rw [h_eta, h_cos_bangle]
  dsimp [gam]
  rw [h_eta_eq_cos_bangle]
  rw [Real.arccos_cos h_bangle_nonneg' h_bangle_le_pi]

/-- (T4) the rhombus corner is twice the base angle of its isosceles half. -/
theorem rho_eq_two_bangle (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    rho d x = 2 * bangle d x := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hx with ⟨hx_pos, hx_lt⟩
  have hcos_d_pos : 0 < cos d := cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  have hx2_pos : 0 < x / 2 := by linarith
  have hx2_lt : x / 2 < π / 2 := by linarith
  have hcos_x2_pos : 0 < cos (x / 2) := cos_pos_of_mem_Ioo ⟨by linarith, hx2_lt⟩
  have hsin_x2_pos : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx2_pos (by linarith)
  have htan_x2_pos : 0 < tan (x / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin_x2_pos hcos_x2_pos
  have hcos_d_mul_tan_pos : 0 < cos d * tan (x / 2) := mul_pos hcos_d_pos htan_x2_pos
  dsimp [rho, bangle]
  have h_eq : cos (x / 2) / (cos d * sin (x / 2)) = (cos d * tan (x / 2))⁻¹ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos_d_pos.ne.symm, hsin_x2_pos.ne.symm, hcos_x2_pos.ne.symm]
  rw [h_eq]
  rw [Real.arctan_inv_of_pos hcos_d_mul_tan_pos]
  ring

theorem rho_mem_Ioo (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    0 < rho d x ∧ rho d x < π := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hx with ⟨hxpos, hxlt⟩
  have hcos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hxhalf_pos : 0 < x / 2 := by linarith
  have hxhalf_lt_pi_div_two : x / 2 < π / 2 := by linarith
  have htan_pos : 0 < tan (x / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hxhalf_pos hxhalf_lt_pi_div_two
  have hprod_pos : 0 < cos d * tan (x / 2) := mul_pos hcos_pos htan_pos
  have harctan_pos : 0 < arctan (cos d * tan (x / 2)) :=
    (Real.arctan_pos.mpr hprod_pos)
  have harctan_lt_pi_div_two : arctan (cos d * tan (x / 2)) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have hrho_lt_pi : rho d x < π := by
    dsimp [rho]
    linarith
  have hrho_pos : 0 < rho d x := by
    dsimp [rho]
    linarith
  exact And.intro hrho_pos hrho_lt_pi

theorem rhombus_row_y_le (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : alpha d ≤ x ∧ x < π) :
    rho d x ≤ 2 * alpha d := by
  rcases hd with ⟨hd_left, hd_right⟩
  rcases hx with ⟨hx_left, hx_right⟩
  have halpha_bounds := alpha_bounds d ⟨hd_left, hd_right⟩
  rcases halpha_bounds with ⟨h_alpha_gt_pi_third, h_alpha_lt_pi_div_two⟩
  have h_alpha_pos : 0 < alpha d := by linarith
  have h_alpha_lt_pi : alpha d < π := by linarith
  have hx_pos : 0 < x := by linarith
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) π := by
    exact Set.mem_Ioo.mpr ⟨hx_pos, hx_right⟩
  have halpha_mem : alpha d ∈ Set.Ioo (0 : ℝ) π := by
    exact Set.mem_Ioo.mpr ⟨h_alpha_pos, h_alpha_lt_pi⟩
  have h_rho_anti : StrictAntiOn (rho d) (Set.Ioo (0 : ℝ) π) :=
    rho_strictAntiOn_x d ⟨hd_left, hd_right⟩
  by_cases h_eq : alpha d = x
  · subst h_eq
    have h_rho_alpha := rho_alpha d ⟨hd_left, hd_right⟩
    linarith
  · have h_lt : alpha d < x := by
      exact lt_of_le_of_ne hx_left h_eq
    have h_rho_le := h_rho_anti halpha_mem hx_mem h_lt
    have h_rho_alpha := rho_alpha d ⟨hd_left, hd_right⟩
    linarith

theorem rhombus_row_x_le (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : alpha d ≤ x ∧ x < π)
    (hy : alpha d ≤ rho d x) : x ≤ 2 * alpha d := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hx with ⟨hxle, hxlt⟩
  have h_alpha := alpha_bounds d ⟨hdpos, hdlt⟩
  have h_alpha_pos : 0 < alpha d := by linarith
  have hxpos : 0 < x := by linarith
  have h_rho_mem := rho_mem_Ioo d x ⟨hdpos, hdlt⟩ ⟨hxpos, hxlt⟩
  rcases h_rho_mem with ⟨hrhopos, hrholt⟩
  have h_rho_le := rhombus_row_y_le d (rho d x) ⟨hdpos, hdlt⟩ ⟨hy, hrholt⟩
  have h_rho_rho : rho d (rho d x) = x := rho_rho d x ⟨hdpos, hdlt⟩ ⟨hxpos, hxlt⟩
  linarith

theorem rhombus_row_sum_ge (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : alpha d ≤ x ∧ x < π)
    (hy : alpha d ≤ rho d x) : 3 * alpha d ≤ x + rho d x := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hx with ⟨hx_le, hx_lt⟩
  set a := alpha d with ha_def
  have ha_bounds := alpha_bounds d ⟨hd_pos, hd_lt⟩
  rcases ha_bounds with ⟨ha_gt_pi_div_3, ha_lt_pi_div_2⟩
  have ha_pos : 0 < a := by linarith [Real.pi_pos]
  have ha_lt_pi : a < π := by linarith
  have h_rho_a : rho d a = 2 * a := by
    rw [ha_def]
    exact rho_alpha d ⟨hd_pos, hd_lt⟩
  have h_rho_2a : rho d (2 * a) = a := by
    rw [← h_rho_a]
    exact rho_rho d a ⟨hd_pos, hd_lt⟩ ⟨ha_pos, ha_lt_pi⟩
  have hx_le_2a : x ≤ 2 * a := by
    rw [ha_def]
    exact rhombus_row_x_le d x ⟨hd_pos, hd_lt⟩ ⟨hx_le, hx_lt⟩ hy
  have h_concave : ConcaveOn ℝ (Set.Ioo (0 : ℝ) π) (rho d) := rho_concaveOn d ⟨hd_pos, hd_lt⟩
  have ha_mem : a ∈ Set.Ioo (0 : ℝ) π := ⟨ha_pos, ha_lt_pi⟩
  have h2a_mem : 2 * a ∈ Set.Ioo (0 : ℝ) π := by
    have hpos : 0 < 2 * a := by nlinarith
    have hlt : 2 * a < π := by nlinarith
    exact ⟨hpos, hlt⟩
  set t := (x - a) / a with ht_def
  have ht_nonneg : 0 ≤ t := by
    rw [ht_def]
    refine div_nonneg ?_ (by linarith)
    linarith
  have h_one_minus_t_nonneg : 0 ≤ 1 - t := by
    rw [ht_def]
    have h_num : 0 ≤ 2 * a - x := by linarith
    have h_denom : 0 ≤ a := by linarith
    have h_eq : 1 - (x - a) / a = (2 * a - x) / a := by
      field_simp [ha_pos.ne.symm]
      ring
    rw [h_eq]
    exact div_nonneg h_num h_denom
  have h_sum : (1 - t) + t = 1 := by ring
  have hx_eq : x = (1 - t) * a + t * (2 * a) := by
    rw [ht_def]
    field_simp [ha_pos.ne.symm]
    ring
  have h_concave_ineq := h_concave.2 ha_mem h2a_mem h_one_minus_t_nonneg ht_nonneg h_sum
  have h_ineq_simp : (1 - t) * (2 * a) + t * a ≤ rho d x := by
    simpa [smul_eq_mul, h_rho_a, h_rho_2a, hx_eq] using h_concave_ineq
  have h_final : x + ((1 - t) * (2 * a) + t * a) = 3 * a := by
    rw [hx_eq]
    ring
  linarith

theorem rhombus_row_sum_le (d x : ℝ) (hd : 0 < d ∧ d < π / 2) (hx : 0 < x ∧ x < π) :
    x + rho d x ≤ Ssum d := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hx with ⟨hxpos, hxlt⟩
  set c := cos d with hc_def
  set s := Real.sqrt c with hs_def
  set t := tan (x / 2) with ht_def
  have hc_pos : 0 < c := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hc_lt_one : c < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) hdpos
    simpa [hc_def, cos_zero] using h
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hc_pos
  have ht_pos : 0 < t := by
    apply Real.tan_pos_of_pos_of_lt_pi_div_two
    · linarith
    · linarith
  -- Express x as 2*arctan t
  have hx_eq : x = 2 * arctan t := by
    have hx2_range : -(π / 2) < x / 2 ∧ x / 2 < π / 2 := by
      constructor <;> linarith
    calc
      x = 2 * (x / 2) := by ring
      _ = 2 * arctan (tan (x / 2)) := by
        rw [Real.arctan_tan hx2_range.1 hx2_range.2]
      _ = 2 * arctan t := by rw [ht_def]
  -- Express rho d x
  have hrho_eq : rho d x = π - 2 * arctan (c * t) := by
    rw [Tammes15.rho, hc_def, ht_def]
  -- Express Ssum d
  have hSsum_eq : Ssum d = 4 * arctan (1 / s) := by
    rw [Tammes15.Ssum, hs_def]
  -- Express π as 2*arctan(1/s) + 2*arctan(s)
  have hpi_eq : π = 2 * arctan (1 / s) + 2 * arctan s := by
    have h := Real.arctan_inv_of_pos hs_pos
    -- h: arctan (s⁻¹) = π/2 - arctan s
    have h' : arctan (1 / s) = π / 2 - arctan s := by
      simpa [one_div] using h
    linarith
  -- Left side: arctan t - arctan(c*t) = arctan((t - c*t)/(1 + c*t²))
  have hleft : arctan t - arctan (c * t) = arctan ((t - c * t) / (1 + c * t ^ 2)) := by
    have h_cond : t * (-(c * t)) < 1 := by
      have h_nonneg : 0 ≤ c * t ^ 2 := by positivity
      nlinarith
    calc
      arctan t - arctan (c * t) = arctan t + arctan (-(c * t)) := by
        rw [sub_eq_add_neg, Real.arctan_neg (c * t)]
      _ = arctan ((t + (-(c * t))) / (1 - t * (-(c * t)))) := by rw [Real.arctan_add h_cond]
      _ = arctan ((t - c * t) / (1 + c * t ^ 2)) := by ring
  -- Right side: arctan(1/s) - arctan s = arctan((1-c)/(2*s))
  have hright : arctan (1 / s) - arctan s = arctan (((1 : ℝ) - c) / (2 * s)) := by
    have h_cond : (1 / s) * (-s) < 1 := by
      field_simp [hs_pos.ne.symm]
      nlinarith
    calc
      arctan (1 / s) - arctan s = arctan (1 / s) + arctan (-s) := by
        rw [sub_eq_add_neg, Real.arctan_neg s]
      _ = arctan (((1 / s) + (-s)) / (1 - (1 / s) * (-s))) := by rw [Real.arctan_add h_cond]
      _ = arctan (((1 - s ^ 2) / s) / 2) := by
        field_simp [hs_pos.ne.symm]
        ring
      _ = arctan ((1 - s ^ 2) / (2 * s)) := by ring
      _ = arctan (((1 : ℝ) - c) / (2 * s)) := by
        rw [hs_def, Real.sq_sqrt hc_pos.le]
  -- The key inequality
  have h_ineq : (t - c * t) / (1 + c * t ^ 2) ≤ ((1 : ℝ) - c) / (2 * s) := by
    have h_denom1_pos : 0 < 1 + c * t ^ 2 := by nlinarith
    have h_denom2_pos : 0 < 2 * s := by nlinarith
    rw [div_le_div_iff₀ h_denom1_pos h_denom2_pos]
    have h_one_minus_c_pos : 0 < 1 - c := by linarith
    have h_main : (t - c * t) * (2 * s) ≤ ((1 : ℝ) - c) * (1 + c * t ^ 2) := by
      have h_eq : (t - c * t) * (2 * s) = (1 - c) * (2 * s * t) := by ring
      rw [h_eq]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      -- Goal: 2*s*t ≤ 1 + c*t²
      -- i.e., 0 ≤ 1 - 2*s*t + c*t² = (s*t - 1)²
      have h_sq_eq : (s * t - 1) ^ 2 = 1 - 2 * s * t + c * t ^ 2 := by
        dsimp [s]
        calc
          (Real.sqrt c * t - 1) ^ 2 = (Real.sqrt c * t) ^ 2 - 2 * (Real.sqrt c * t) + 1 := by ring
          _ = ((Real.sqrt c) ^ 2) * t ^ 2 - 2 * Real.sqrt c * t + 1 := by ring
          _ = c * t ^ 2 - 2 * Real.sqrt c * t + 1 := by rw [Real.sq_sqrt hc_pos.le]
          _ = 1 - 2 * Real.sqrt c * t + c * t ^ 2 := by ring
      have h_nonneg_sq : 0 ≤ (s * t - 1) ^ 2 := sq_nonneg _
      linarith
    exact h_main
  have h_final : arctan t - arctan (c * t) ≤ arctan (1 / s) - arctan s := by
    rw [hleft, hright]
    exact Real.arctan_mono h_ineq
  calc
    x + rho d x = (2 * arctan t) + (π - 2 * arctan (c * t)) := by rw [hrho_eq, hx_eq]
    _ = 2 * arctan t + π - 2 * arctan (c * t) := by ring
    _ = 2 * arctan t + (2 * arctan (1 / s) + 2 * arctan s) - 2 * arctan (c * t) := by rw [hpi_eq]
    _ = 2 * (arctan t + arctan s - arctan (c * t)) + 2 * arctan (1 / s) := by ring
    _ ≤ 2 * arctan (1 / s) + 2 * arctan (1 / s) := by
      nlinarith
    _ = 4 * arctan (1 / s) := by ring
    _ = Ssum d := by rw [hSsum_eq]

/-- Row (2) for a rhombus with corners `x, y` (every realisation). -/
theorem rhombus_rows (d x y : ℝ) (hd : 0 < d ∧ d < π / 2) (hy : y = rho d x)
    (hx : alpha d ≤ x ∧ x < π) (hy' : alpha d ≤ y) :
    x ≤ 2 * alpha d ∧ y ≤ 2 * alpha d ∧ 3 * alpha d ≤ x + y ∧ x + y ≤ Ssum d := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hx with ⟨hxalpha, hxlt⟩
  subst hy
  have halpha_pos : π / 3 < alpha d := (alpha_bounds d ⟨hdpos, hdlt⟩).1
  have hxpos : 0 < x := by linarith
  have hyrho_alpha : alpha d ≤ rho d x := hy'
  have hx_le : x ≤ 2 * alpha d := rhombus_row_x_le d x ⟨hdpos, hdlt⟩ ⟨hxalpha, hxlt⟩ hyrho_alpha
  have hy_le : rho d x ≤ 2 * alpha d := rhombus_row_y_le d x ⟨hdpos, hdlt⟩ ⟨hxalpha, hxlt⟩
  have hsum_ge : 3 * alpha d ≤ x + rho d x := rhombus_row_sum_ge d x ⟨hdpos, hdlt⟩ ⟨hxalpha, hxlt⟩ hyrho_alpha
  have hsum_le : x + rho d x ≤ Ssum d := rhombus_row_sum_le d x ⟨hdpos, hdlt⟩ ⟨hxpos, hxlt⟩
  exact ⟨hx_le, hy_le, hsum_ge, hsum_le⟩

/-- (T3) `d = arccos (cos a / (1 - cos a))` is increasing in `a`. -/
theorem dOfAlpha_strictMonoOn :
    StrictMonoOn (fun a => arccos (cos a / (1 - cos a))) (Set.Ioo (π / 3) (π / 2)) := by
  -- Step 1: cos is strictAntiOn on Ioo (π/3) (π/2)
  have h_cos_anti : StrictAntiOn cos (Set.Ioo (π / 3) (π / 2)) := by
    refine Real.strictAntiOn_cos.mono ?_
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩
    have hx_nonneg : 0 ≤ x := by linarith [pi_pos]
    have hx_le_pi : x ≤ π := by linarith [pi_pos]
    exact ⟨hx_nonneg, hx_le_pi⟩
  -- Step 2: t/(1-t) is strictMonoOn on Ioo (0) 1
  have h_div_mono : StrictMonoOn (fun t : ℝ => t / (1 - t)) (Set.Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    rcases hx with ⟨hx₀, hx₁⟩
    rcases hy with ⟨hy₀, hy₁⟩
    have hpos_denom1 : 0 < 1 - x := by linarith
    have hpos_denom2 : 0 < 1 - y := by linarith
    field_simp [hpos_denom1.ne', hpos_denom2.ne']
    nlinarith
  -- Step 3: MapsTo for cos
  have h_maps_cos : Set.MapsTo cos (Set.Ioo (π / 3) (π / 2)) (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩
    have hcos_pos : 0 < cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [pi_pos]
      · linarith
    have hcos_lt_one : cos x < 1 := by
      have h0 : (0 : ℝ) < x := by linarith [pi_pos]
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ (0 : ℝ)) (by linarith [pi_pos] : x ≤ π) h0
      simpa [cos_zero] using h
    exact ⟨hcos_pos, hcos_lt_one⟩
  -- Step 4: (t/(1-t)) ∘ cos is strictAntiOn
  have h_comp_anti : StrictAntiOn (fun a => cos a / (1 - cos a)) (Set.Ioo (π / 3) (π / 2)) :=
    h_div_mono.comp_strictAntiOn h_cos_anti h_maps_cos
  -- Step 5: MapsTo for the composition into Icc (-1) 1
  have h_maps_div : Set.MapsTo (fun a => cos a / (1 - cos a)) (Set.Ioo (π / 3) (π / 2)) (Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩
    have hcos_pos : 0 < cos x := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [pi_pos]
      · linarith
    have hcos_lt_one : cos x < 1 := by
      have h0 : (0 : ℝ) < x := by linarith [pi_pos]
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ (0 : ℝ)) (by linarith [pi_pos] : x ≤ π) h0
      simpa [cos_zero] using h
    have h_div_pos : 0 < cos x / (1 - cos x) := by
      apply div_pos hcos_pos
      linarith
    have h_div_le_one : cos x / (1 - cos x) ≤ 1 := by
      have hcos_lt_half : cos x < 1/2 := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ (π/3)) (by linarith [pi_pos] : x ≤ π) hx₁
        simpa [Real.cos_pi_div_three] using h
      have hineq : cos x ≤ 1 - cos x := by linarith
      have hpos : 0 < 1 - cos x := by linarith
      apply (div_le_one hpos).mpr hineq
    exact ⟨by linarith, h_div_le_one⟩
  -- Step 6: Final composition
  exact Real.strictAntiOn_arccos.comp h_comp_anti h_maps_div

/-- (T2) derivative of `η` in `f`, with the sign of `cos e - cos f cos g`. -/
theorem eta_hasDerivAt_f (g e f : ℝ) (he : 0 < e ∧ e < π) (hf : 0 < f ∧ f < π) :
    HasDerivAt (fun f => eta g e f)
      (sin e * (cos e - cos f * cos g) / (sin e * sin f) ^ 2) f := by
  rcases he with ⟨he0, heπ⟩
  rcases hf with ⟨hf0, hfπ⟩
  have hsin_e_pos : sin e > 0 := Real.sin_pos_of_pos_of_lt_pi he0 heπ
  have hsin_f_pos : sin f > 0 := Real.sin_pos_of_pos_of_lt_pi hf0 hfπ
  have hsin_e_ne_zero : sin e ≠ 0 := by linarith
  have hsin_f_ne_zero : sin f ≠ 0 := by linarith
  have h_denom_ne_zero : sin e * sin f ≠ 0 := mul_ne_zero hsin_e_ne_zero hsin_f_ne_zero
  have h_denom_sq_ne_zero : (sin e * sin f) ^ 2 ≠ 0 := pow_ne_zero 2 h_denom_ne_zero
  -- derivative of numerator: N(x) = cos g - cos e * cos x
  have hN_deriv : HasDerivAt (fun x => cos g - cos e * cos x) (cos e * sin f) f := by
    have h_const : HasDerivAt (fun _ : ℝ => cos g) 0 f := hasDerivAt_const _ _
    have h_cos : HasDerivAt (fun x : ℝ => cos e * cos x) (-cos e * sin f) f := by
      simpa [mul_comm] using ((Real.hasDerivAt_cos f).const_mul (cos e))
    have h := h_const.sub h_cos
    convert h using 1
    ring
  -- derivative of denominator: D(x) = sin e * sin x
  have hD_deriv : HasDerivAt (fun x : ℝ => sin e * sin x) (sin e * cos f) f := by
    simpa [mul_comm] using ((Real.hasDerivAt_sin f).const_mul (sin e))
  -- apply quotient rule
  have h_eta_deriv : HasDerivAt (fun x : ℝ => eta g e x)
      (((cos e * sin f) * (sin e * sin f) - (cos g - cos e * cos f) * (sin e * cos f)) / (sin e * sin f) ^ 2) f := by
    have h_eta_eq : (fun x : ℝ => eta g e x) = (fun x : ℝ => (cos g - cos e * cos x) / (sin e * sin x)) := by
      ext x; simp [eta]
    rw [h_eta_eq]
    exact hN_deriv.div hD_deriv h_denom_ne_zero
  -- simplify the resulting expression
  have h_simplify : ((cos e * sin f) * (sin e * sin f) - (cos g - cos e * cos f) * (sin e * cos f)) / (sin e * sin f) ^ 2
      = sin e * (cos e - cos f * cos g) / (sin e * sin f) ^ 2 := by
    field_simp [h_denom_sq_ne_zero]
    ring_nf
    calc
      cos e * sin f ^ 2 + cos e * cos f ^ 2 - cos f * cos g
          = cos e * (sin f ^ 2 + cos f ^ 2) - cos f * cos g := by ring
      _ = cos e * 1 - cos f * cos g := by rw [Real.sin_sq_add_cos_sq f]
      _ = cos e - cos f * cos g := by ring
  simpa [h_simplify] using h_eta_deriv

/-- Lemma edge, last step: `cos d ≥ cos s cos t` with `t ≤ d/2` gives `s ≥ h(d)`. -/
theorem edge_bound_real (d s t : ℝ) (hd : 0 < d ∧ d < π / 2) (hs : 0 ≤ s ∧ s ≤ π)
    (ht : 0 ≤ t ∧ t ≤ d / 2) (h : cos s * cos t ≤ cos d) : hrad d ≤ s := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases hs with ⟨hs_left, hs_right⟩
  rcases ht with ⟨ht_left, ht_right⟩
  have hcosd_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hcos_half_pos : 0 < cos (d / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  have hcost_ge_cos_half : cos (d / 2) ≤ cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht_left (by linarith) ht_right
  have h_cos_s_mul_cos_half_le_cos_d : cos s * cos (d / 2) ≤ cos d := by
    by_cases h_cos_s_nonneg : 0 ≤ cos s
    · have h1 : cos s * cos (d / 2) ≤ cos s * cos t :=
        mul_le_mul_of_nonneg_left hcost_ge_cos_half h_cos_s_nonneg
      linarith
    · have h_cos_s_neg : cos s < 0 := by linarith
      have h_neg : cos s * cos (d / 2) < 0 := mul_neg_of_neg_of_pos h_cos_s_neg hcos_half_pos
      linarith
  have h_cos_s_le : cos s ≤ cos d / cos (d / 2) := by
    rw [le_div_iff₀ hcos_half_pos]
    exact h_cos_s_mul_cos_half_le_cos_d
  have h_arccos : arccos (cos d / cos (d / 2)) ≤ arccos (cos s) :=
    Real.arccos_le_arccos h_cos_s_le
  have h_arccos_cos_s : arccos (cos s) = s :=
    Real.arccos_cos hs_left hs_right
  rw [h_arccos_cos_s] at h_arccos
  unfold hrad
  exact h_arccos

end Tammes15
