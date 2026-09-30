import Tammes15.Trigrows.Sphere
import Tammes15.Trigrows.Rows

/-!
# Law of cosines, (T1), (T2), Lemma alpha: the part on points

Corners are unoriented here: `angle (tdir v a) (tdir v b) ∈ [0, π]`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

theorem sdist_comm (p q : E3) : sdist p q = sdist q p := by
  unfold sdist; rw [real_inner_comm]

theorem cos_sdist (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : cos (sdist p q) = ⟪p, q⟫ := by
  unfold sdist
  have hbound : -1 ≤ ⟪p, q⟫ ∧ ⟪p, q⟫ ≤ 1 := by
    have h := abs_real_inner_le_norm p q
    rw [hp, hq, mul_one] at h
    exact abs_le.mp h
  rcases hbound with ⟨hl, hr⟩
  rw [Real.cos_arccos hl hr]

theorem inner_tdir (v a b : E3) (hv : ‖v‖ = 1) :
    ⟪tdir v a, tdir v b⟫ = ⟪a, b⟫ - ⟪v, a⟫ * ⟪v, b⟫ := by
  simp only [tdir, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hv]
  rw [real_inner_comm v a]
  ring

theorem tdir_norm (v w : E3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖tdir v w‖ = sin (sdist v w) := by
  have h_inner_vv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have h_inner_ww : ⟪w, w⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hw]
    norm_num
  have h_norm_sq : ‖tdir v w‖ ^ 2 = 1 - ⟪v, w⟫ ^ 2 := by
    calc
      ‖tdir v w‖ ^ 2 = ⟪tdir v w, tdir v w⟫ := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪w - ⟪v, w⟫ • v, w - ⟪v, w⟫ • v⟫ := rfl
      _ = ⟪w - ⟪v, w⟫ • v, w⟫ - ⟪w - ⟪v, w⟫ • v, ⟪v, w⟫ • v⟫ := by rw [inner_sub_right]
      _ = (⟪w, w⟫ - ⟪⟪v, w⟫ • v, w⟫) - (⟪w, ⟪v, w⟫ • v⟫ - ⟪⟪v, w⟫ • v, ⟪v, w⟫ • v⟫) := by
        rw [inner_sub_left, inner_sub_left]
      _ = (⟪w, w⟫ - ⟪v, w⟫ * ⟪v, w⟫) - (⟪v, w⟫ * ⟪w, v⟫ - (⟪v, w⟫ * ⟪v, w⟫) * ⟪v, v⟫) := by
        simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_id_of_comm, mul_assoc]
      _ = (1 - ⟪v, w⟫ * ⟪v, w⟫) - (⟪v, w⟫ * ⟪w, v⟫ - (⟪v, w⟫ * ⟪v, w⟫) * 1) := by
        rw [h_inner_ww, h_inner_vv]
      _ = (1 - ⟪v, w⟫ ^ 2) - (⟪v, w⟫ * ⟪w, v⟫ - ⟪v, w⟫ ^ 2) := by ring
      _ = 1 - ⟪v, w⟫ ^ 2 - ⟪v, w⟫ * ⟪w, v⟫ + ⟪v, w⟫ ^ 2 := by ring
      _ = 1 - ⟪v, w⟫ * ⟪w, v⟫ := by ring
      _ = 1 - ⟪v, w⟫ ^ 2 := by
        rw [real_inner_comm v w]
        ring
  have h_norm_nonneg : 0 ≤ ‖tdir v w‖ := norm_nonneg _
  have h_sdist : sdist v w = arccos ⟪v, w⟫ := rfl
  calc
    ‖tdir v w‖ = Real.sqrt (‖tdir v w‖ ^ 2) := by rw [Real.sqrt_sq h_norm_nonneg]
    _ = Real.sqrt (1 - ⟪v, w⟫ ^ 2) := by rw [h_norm_sq]
    _ = Real.sin (arccos ⟪v, w⟫) := by rw [Real.sin_arccos]
    _ = sin (sdist v w) := by rw [h_sdist]

/-- The spherical law of cosines at `A`, for any three unit vectors. -/
theorem slc_tangent (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    cos (sdist B C) = cos (sdist A B) * cos (sdist A C) +
      sin (sdist A B) * sin (sdist A C) * cos (angle (tdir A B) (tdir A C)) := by
  have hcosBC : cos (sdist B C) = ⟪B, C⟫ := cos_sdist B C hB hC
  have hcosAB : cos (sdist A B) = ⟪A, B⟫ := cos_sdist A B hA hB
  have hcosAC : cos (sdist A C) = ⟪A, C⟫ := cos_sdist A C hA hC
  have hsinAB : sin (sdist A B) = ‖tdir A B‖ := by rw [tdir_norm A B hA hB]
  have hsinAC : sin (sdist A C) = ‖tdir A C‖ := by rw [tdir_norm A C hA hC]
  have hinner_tdir : ⟪tdir A B, tdir A C⟫ = ⟪B, C⟫ - ⟪A, B⟫ * ⟪A, C⟫ := inner_tdir A B C hA
  have hcos_angle : cos (angle (tdir A B) (tdir A C)) * (‖tdir A B‖ * ‖tdir A C‖) = ⟪tdir A B, tdir A C⟫ :=
    InnerProductGeometry.cos_angle_mul_norm_mul_norm (tdir A B) (tdir A C)
  have htemp : ‖tdir A B‖ * ‖tdir A C‖ * cos (angle (tdir A B) (tdir A C)) = ⟪tdir A B, tdir A C⟫ := by
    calc
      ‖tdir A B‖ * ‖tdir A C‖ * cos (angle (tdir A B) (tdir A C)) = cos (angle (tdir A B) (tdir A C)) * (‖tdir A B‖ * ‖tdir A C‖) := by ring
      _ = ⟪tdir A B, tdir A C⟫ := hcos_angle
  calc
    cos (sdist B C) = ⟪B, C⟫ := hcosBC
    _ = ⟪A, B⟫ * ⟪A, C⟫ + (⟪B, C⟫ - ⟪A, B⟫ * ⟪A, C⟫) := by ring
    _ = ⟪A, B⟫ * ⟪A, C⟫ + ⟪tdir A B, tdir A C⟫ := by rw [hinner_tdir]
    _ = cos (sdist A B) * cos (sdist A C) + ⟪tdir A B, tdir A C⟫ := by rw [hcosAB, hcosAC]
    _ = cos (sdist A B) * cos (sdist A C) + (‖tdir A B‖ * ‖tdir A C‖ * cos (angle (tdir A B) (tdir A C))) := by rw [htemp]
    _ = cos (sdist A B) * cos (sdist A C) + sin (sdist A B) * sin (sdist A C) * cos (angle (tdir A B) (tdir A C)) := by rw [hsinAB, hsinAC]

/-- (T2) the corner at `A` is `γ` of the three sides. -/
theorem angle_tdir_eq_gam (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hAB : 0 < sdist A B ∧ sdist A B < π) (hAC : 0 < sdist A C ∧ sdist A C < π) :
    angle (tdir A B) (tdir A C) = gam (sdist B C) (sdist A B) (sdist A C) := by
  set θ := angle (tdir A B) (tdir A C) with hθ
  set a := sdist A B with ha
  set b := sdist A C with hb
  set c := sdist B C with hc
  have ha_pos : 0 < a := hAB.1
  have ha_lt_pi : a < π := hAB.2
  have hb_pos : 0 < b := hAC.1
  have hb_lt_pi : b < π := hAC.2
  have hsin_a_pos : 0 < sin a := Real.sin_pos_of_pos_of_lt_pi ha_pos ha_lt_pi
  have hsin_b_pos : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb_pos hb_lt_pi
  have hsin_a_ne_zero : sin a ≠ 0 := by linarith
  have hsin_b_ne_zero : sin b ≠ 0 := by linarith
  have h_slc := slc_tangent A B C hA hB hC
  have h_eq : cos θ = eta c a b := by
    dsimp [eta]
    have h_slc' := h_slc
    rw [← hc, ← hb, ← ha] at h_slc'
    have hcos_eq : cos c - cos a * cos b = sin a * sin b * cos θ := by
      linarith
    field_simp [hsin_a_ne_zero, hsin_b_ne_zero]
    nlinarith
  have h_angle_range : θ ∈ Set.Icc (0 : ℝ) π :=
    ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  rw [hc, hb, ha]
  dsimp [gam]
  rw [← h_eq]
  exact (Real.arccos_cos h_angle_range.1 h_angle_range.2).symm

/-- (T2) the sides of a triangle give `η ∈ [-1, 1]`. -/
theorem eta_mem_Icc (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hAB : 0 < sdist A B ∧ sdist A B < π) (hAC : 0 < sdist A C ∧ sdist A C < π) :
    -1 ≤ eta (sdist B C) (sdist A B) (sdist A C) ∧ eta (sdist B C) (sdist A B) (sdist A C) ≤ 1 := by
  rcases hAB with ⟨hAB_left, hAB_right⟩
  rcases hAC with ⟨hAC_left, hAC_right⟩
  have hsinAB : sin (sdist A B) > 0 := Real.sin_pos_of_pos_of_lt_pi hAB_left hAB_right
  have hsinAC : sin (sdist A C) > 0 := Real.sin_pos_of_pos_of_lt_pi hAC_left hAC_right
  have h_eq : eta (sdist B C) (sdist A B) (sdist A C) = cos (angle (tdir A B) (tdir A C)) := by
    unfold eta
    have h := slc_tangent A B C hA hB hC
    field_simp [hsinAB.ne', hsinAC.ne']
    linarith
  have h_lower : -1 ≤ eta (sdist B C) (sdist A B) (sdist A C) := by
    rw [h_eq]
    exact Real.neg_one_le_cos _
  have h_upper : eta (sdist B C) (sdist A B) (sdist A C) ≤ 1 := by
    rw [h_eq]
    exact Real.cos_le_one _
  exact And.intro h_lower h_upper

/-- Lemma alpha. -/
theorem alpha_le_angle (d : ℝ) (hd : 0 < d ∧ d < π / 2) (v w₁ w₂ : E3) (hv : ‖v‖ = 1)
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (h₁ : sdist v w₁ = d) (h₂ : sdist v w₂ = d)
    (h₁₂ : d ≤ sdist w₁ w₂) : alpha d ≤ angle (tdir v w₁) (tdir v w₂) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hd_nonneg : 0 ≤ d := le_of_lt hdpos
  have hd_le_pi : d ≤ π := by
    have hpi_pos : 0 < π := Real.pi_pos
    linarith
  have hc_pos : 0 < cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hc_lt_one : cos d < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hd_le_pi hdpos
    simpa [Real.cos_zero] using this
  set c := cos d with hc_def
  set θ := angle (tdir v w₁) (tdir v w₂) with hθ_def
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθ_le_pi : θ ≤ π := InnerProductGeometry.angle_le_pi _ _
  have h_slc := slc_tangent v w₁ w₂ hv hw₁ hw₂
  rw [h₁, h₂, ← hθ_def] at h_slc
  rw [← hc_def] at h_slc
  have h_sdist_nonneg : 0 ≤ sdist w₁ w₂ := Real.arccos_nonneg _
  have h_sdist_le_pi : sdist w₁ w₂ ≤ π := Real.arccos_le_pi _
  have h_cos_sdist_le_c : cos (sdist w₁ w₂) ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hd_nonneg h_sdist_le_pi h₁₂
  rw [h_slc] at h_cos_sdist_le_c
  have h_sin_sq_eq : sin d ^ 2 = (1 - c) * (1 + c) := by
    have := Real.sin_sq_add_cos_sq d
    rw [← hc_def] at this
    linarith
  have h_one_minus_c_pos : 0 < 1 - c := by linarith
  have h_one_plus_c_pos : 0 < 1 + c := by linarith
  have h_ineq1 : sin d ^ 2 * cos θ ≤ c - c ^ 2 := by
    linarith
  rw [h_sin_sq_eq] at h_ineq1
  have h_c_minus_c_sq : c - c ^ 2 = c * (1 - c) := by ring
  rw [h_c_minus_c_sq] at h_ineq1
  have h_cos_θ_le : cos θ ≤ c / (1 + c) := by
    have h_temp : (1 + c) * cos θ ≤ c := by
      nlinarith
    calc
      cos θ = ((1 + c) * cos θ) / (1 + c) := by field_simp [ne_of_gt h_one_plus_c_pos]
      _ ≤ c / (1 + c) := div_le_div_of_nonneg_right h_temp h_one_plus_c_pos.le
  have h_alpha_eq : alpha d = Real.arccos (c / (1 + c)) := by
    rw [Tammes15.alpha, hc_def]
  rw [h_alpha_eq]
  have h_arccos_cos : Real.arccos (cos θ) = θ :=
    Real.arccos_cos hθ_nonneg hθ_le_pi
  calc
    Real.arccos (c / (1 + c)) ≤ Real.arccos (cos θ) :=
      Real.arccos_le_arccos h_cos_θ_le
    _ = θ := h_arccos_cos

/-- (T1) the base of the isosceles triangle with legs `d`. -/
theorem T1_isosceles_base (d : ℝ) (hd : 0 < d ∧ d < π / 2) (A B C : E3) (hA : ‖A‖ = 1)
    (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) (hAB : sdist A B = d) (hAC : sdist A C = d) :
    sdist B C = ebase d (angle (tdir A B) (tdir A C)) := by
  rcases hd with ⟨hdpos, hdlt⟩
  set u := angle (tdir A B) (tdir A C) with hu_def
  have hu_nonneg : 0 ≤ u := InnerProductGeometry.angle_nonneg _ _
  have hu_le_pi : u ≤ π := InnerProductGeometry.angle_le_pi _ _
  have hdpos' : 0 ≤ d := le_of_lt hdpos
  have h_sin_d_nonneg : 0 ≤ sin d :=
    Real.sin_nonneg_of_nonneg_of_le_pi hdpos' (by linarith)
  have h_sin_d_lt_one : sin d < 1 := by
    have hmem : d ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> linarith
    have h := Real.mapsTo_sin_Ioo hmem
    rcases h with ⟨_, hhi⟩
    exact hhi
  have h_sin_u_half_nonneg : 0 ≤ sin (u / 2) := by
    have hhalf_nonneg : 0 ≤ u / 2 := by nlinarith
    have hhalf_le_pi : u / 2 ≤ π := by nlinarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi hhalf_nonneg hhalf_le_pi
  set y := sin d * sin (u / 2) with hy_def
  have hy_nonneg : 0 ≤ y := mul_nonneg h_sin_d_nonneg h_sin_u_half_nonneg
  have hy_lt_one : y < 1 := by
    rw [hy_def]
    have h1 : sin d * sin (u / 2) ≤ sin d * 1 :=
      mul_le_mul_of_nonneg_left (Real.sin_le_one _) h_sin_d_nonneg
    have h2 : sin d * 1 < 1 := by
      nlinarith
    linarith
  have h_one_minus_y_sq_nonneg : 0 ≤ 1 - y ^ 2 := by
    have hy_sq_le_one : y ^ 2 ≤ 1 := by
      have hy_le_one : y ≤ 1 := le_of_lt hy_lt_one
      nlinarith
    nlinarith
  have h_cos_u : cos u = 1 - 2 * sin (u / 2) ^ 2 := by
    calc
      cos u = cos (2 * (u / 2)) := by ring_nf
      _ = cos (u / 2) ^ 2 - sin (u / 2) ^ 2 := by rw [Real.cos_two_mul']
      _ = (1 - sin (u / 2) ^ 2) - sin (u / 2) ^ 2 := by rw [Real.cos_sq']
      _ = 1 - 2 * sin (u / 2) ^ 2 := by ring_nf
  have h_cos_ebase : cos (ebase d u) = 1 - 2 * y ^ 2 := by
    rw [ebase, ← hy_def]
    rw [Real.cos_two_mul]
    rw [Real.cos_arcsin]
    rw [Real.sq_sqrt h_one_minus_y_sq_nonneg]
    ring_nf
  have h_cos_sdist : cos (sdist B C) = 1 - 2 * y ^ 2 := by
    have h_slc := slc_tangent A B C hA hB hC
    rw [hAB, hAC, ← hu_def] at h_slc
    rw [h_slc]
    rw [h_cos_u]
    rw [hy_def]
    nlinarith [Real.cos_sq_add_sin_sq d]
  have h_cos_eq : cos (sdist B C) = cos (ebase d u) := by
    rw [h_cos_sdist, h_cos_ebase]
  have h_sdist_nonneg : 0 ≤ sdist B C := Real.arccos_nonneg _
  have h_sdist_le_pi : sdist B C ≤ π := Real.arccos_le_pi _
  have h_ebase_nonneg : 0 ≤ ebase d u := by
    rw [ebase, ← hy_def]
    have h_arcsin_nonneg : 0 ≤ arcsin y := by
      rw [Real.arcsin_nonneg]
      exact hy_nonneg
    nlinarith
  have h_ebase_le_pi : ebase d u ≤ π := by
    rw [ebase, ← hy_def]
    have h_arcsin_le : arcsin y ≤ π / 2 := Real.arcsin_le_pi_div_two _
    nlinarith
  have h_inj := Real.injOn_cos (Set.mem_Icc.mpr ⟨h_sdist_nonneg, h_sdist_le_pi⟩)
    (Set.mem_Icc.mpr ⟨h_ebase_nonneg, h_ebase_le_pi⟩) h_cos_eq
  exact h_inj

/-- (T1) the base angle of the isosceles triangle with legs `d`. -/
theorem T1_isosceles_angle (d : ℝ) (hd : 0 < d ∧ d < π / 2) (A B C : E3) (hA : ‖A‖ = 1)
    (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) (hAB : sdist A B = d) (hAC : sdist A C = d)
    (hu : 0 < angle (tdir A B) (tdir A C)) :
    angle (tdir B A) (tdir B C) = bangle d (angle (tdir A B) (tdir A C)) := by
  let u := angle (tdir A B) (tdir A C)
  have hu_pos : 0 < u := hu
  have hu_le_pi : u ≤ π := InnerProductGeometry.angle_le_pi _ _
  have h_base : sdist B C = ebase d u := T1_isosceles_base d hd A B C hA hB hC hAB hAC
  have h_sdist_BA : sdist B A = d := by
    rw [sdist_comm B A, hAB]
  have h_sdist_BA_pos : 0 < sdist B A ∧ sdist B A < π := by
    rw [h_sdist_BA]
    exact ⟨hd.1, by linarith⟩
  have h_sdist_BC_pos : 0 < sdist B C ∧ sdist B C < π := by
    rw [h_base]
    exact ebase_mem_Ioo d u hd ⟨hu_pos, hu_le_pi⟩
  have h_gam : angle (tdir B A) (tdir B C) = gam (sdist A C) (sdist B A) (sdist B C) :=
    angle_tdir_eq_gam B A C hB hA hC h_sdist_BA_pos h_sdist_BC_pos
  rw [h_gam, hAC, h_sdist_BA, h_base]
  exact gam_isosceles_eq_bangle d u hd ⟨hu_pos, hu_le_pi⟩

/-- Lemma edge, Pythagoras step: a right corner at `x`. -/
theorem pythagoras_tangent (p x v : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (hperp : ⟪tdir x p, tdir x v⟫ = 0) :
    cos (sdist p v) = cos (sdist x p) * cos (sdist x v) := by
  have hcos_pv := cos_sdist p v hp hv
  have hcos_xp := cos_sdist x p hx hp
  have hcos_xv := cos_sdist x v hx hv
  have hinner := inner_tdir x p v hx
  have hzero : ⟪p, v⟫ - ⟪x, p⟫ * ⟪x, v⟫ = 0 := by
    linarith
  have h_eq : ⟪p, v⟫ = ⟪x, p⟫ * ⟪x, v⟫ := by
    linarith
  calc
    cos (sdist p v) = ⟪p, v⟫ := hcos_pv
    _ = ⟪x, p⟫ * ⟪x, v⟫ := h_eq
    _ = cos (sdist x p) * cos (sdist x v) := by rw [hcos_xp, hcos_xv]

end Tammes15
