import Tammes15.Trigrows.Points
import Tammes15.Trigrows.Margins

/-!
# Lemma edge and the first step of Proposition nor

`edge_distance` is Lemma edge with a direct proof (no nearest point): the
point of the arc `[v w]` at distance `t` from `v` is `(sin (d - t) v + sin t w) / sin d`, and
`⟪p, x⟫ ≤ cos d · cos (d/2 - t) / cos (d/2) ≤ cos (h d)`. `eta_ge_cos_alpha` and
`gam_le_alpha` are the two-variable bound of Proposition nor (`β ≤ α(d)` when both distances lie
in `[d, π/2]`), by `√((1 - x²)(1 - y²)) ≤ 1 - x y`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- The point of the minor arc from `v` to `w` at distance `t` from `v` (for `sdist v w = d`). -/
noncomputable def arcPt (d : ℝ) (v w : E3) (t : ℝ) : E3 :=
  (sin (d - t) / sin d) • v + (sin t / sin d) • w

theorem norm_arcPt (d : ℝ) (hd : 0 < d ∧ d < π) (v w : E3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : ⟪v, w⟫ = cos d) (t : ℝ) : ‖arcPt d v w t‖ = 1 := by
  have hpos : sin d > 0 := Real.sin_pos_of_pos_of_lt_pi hd.1 hd.2
  have hpos' : sin d ≠ 0 := by linarith
  have habs_sind : |sin d| = sin d := abs_of_pos hpos
  have hsq : ‖arcPt d v w t‖ ^ 2 = 1 := by
    dsimp [arcPt]
    have h := norm_add_sq_real ((sin (d - t) / sin d) • v) ((sin t / sin d) • w)
    rw [h]
    simp [norm_smul, hv, hw, hvw, inner_smul_left, inner_smul_right, habs_sind]
    simp [sq_abs, div_pow]
    ring_nf
    field_simp [hpos']
    have hsin_sub : sin (d - t) = sin d * cos t - cos d * sin t := by exact Real.sin_sub d t
    rw [hsin_sub]
    nlinarith [Real.sin_sq_add_cos_sq d, Real.sin_sq_add_cos_sq t]
  have h_nonneg : 0 ≤ ‖arcPt d v w t‖ := norm_nonneg _
  have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
  nlinarith

theorem sin_sub_add_sin (d t : ℝ) (hd : 0 < d ∧ d < π) :
    (sin (d - t) + sin t) / sin d = cos (d / 2 - t) / cos (d / 2) := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hd2pos : 0 < d / 2 := by linarith
  have hd2_lt_pi_div_two : d / 2 < π / 2 := by linarith
  have hd2_lt_pi : d / 2 < π := by linarith
  have hsin_pos : sin (d / 2) > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨hd2pos, hd2_lt_pi⟩
  have hcos_pos : cos (d / 2) > 0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hd2_lt_pi_div_two⟩
  have hsin_ne_zero : sin (d / 2) ≠ 0 := by linarith
  have hcos_ne_zero : cos (d / 2) ≠ 0 := by linarith
  have h_sin_sum : sin (d - t) + sin t = 2 * sin (d / 2) * cos (d / 2 - t) := by
    calc
      sin (d - t) + sin t = 2 * sin (((d - t) + t) / 2) * cos (((d - t) - t) / 2) := by
        rw [Real.sin_add_sin]
      _ = 2 * sin (d / 2) * cos (d / 2 - t) := by ring
  have h_sin_d : sin d = 2 * sin (d / 2) * cos (d / 2) := by
    calc
      sin d = sin (2 * (d / 2)) := by ring
      _ = 2 * sin (d / 2) * cos (d / 2) := by rw [Real.sin_two_mul]
  rw [h_sin_sum, h_sin_d]
  field_simp [hsin_ne_zero, hcos_ne_zero]

/-- Lemma edge: a point at distance at least `d` from both ends of an edge is at distance at least
`h(d)` from every point of the edge. -/
theorem edge_distance (d : ℝ) (hd : 0 < d ∧ d < π / 2) (v w p : E3) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (hp : ‖p‖ = 1) (hvw : sdist v w = d) (hpv : d ≤ sdist p v)
    (hpw : d ≤ sdist p w) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ d) : hrad d ≤ sdist p (arcPt d v w t) := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases ht with ⟨htpos, htle⟩
  have hd_lt_pi : d < π := by linarith
  have hsin_d_pos : 0 < sin d := by
    refine Real.sin_pos_of_mem_Ioo ?_
    exact ⟨hdpos, hd_lt_pi⟩
  have hcos_d_pos : 0 < cos d := by
    refine Real.cos_pos_of_mem_Ioo ?_
    constructor <;> linarith
  have hcos_d_div_2_pos : 0 < cos (d / 2) := by
    refine Real.cos_pos_of_mem_Ioo ?_
    constructor <;> linarith
  have hvw_inner : ⟪v, w⟫ = cos d := by
    calc
      ⟪v, w⟫ = cos (sdist v w) := by symm; exact cos_sdist v w hv hw
      _ = cos d := by rw [hvw]
  have hnorm_arc : ‖arcPt d v w t‖ = 1 :=
    norm_arcPt d ⟨hdpos, hd_lt_pi⟩ v w hv hw hvw_inner t
  have hsin_dt_nonneg : 0 ≤ sin (d - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsin_t_nonneg : 0 ≤ sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi htpos (by linarith)
  have hcos_sdist_pv : cos (sdist p v) = ⟪p, v⟫ := cos_sdist p v hp hv
  have hpv_range : sdist p v ≤ π := Real.arccos_le_pi _
  have hcos_pv_le_cos_d : cos (sdist p v) ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hdpos.le hpv_range hpv
  have hpv_inner_le_cos_d : ⟪p, v⟫ ≤ cos d := by
    linarith
  have hcos_sdist_pw : cos (sdist p w) = ⟪p, w⟫ := cos_sdist p w hp hw
  have hpw_range : sdist p w ≤ π := Real.arccos_le_pi _
  have hcos_pw_le_cos_d : cos (sdist p w) ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hdpos.le hpw_range hpw
  have hpw_inner_le_cos_d : ⟪p, w⟫ ≤ cos d := by
    linarith
  have hinner_arc : ⟪p, arcPt d v w t⟫ =
      (sin (d - t) / sin d) * ⟪p, v⟫ + (sin t / sin d) * ⟪p, w⟫ := by
    calc
      ⟪p, arcPt d v w t⟫ =
          ⟪p, (sin (d - t) / sin d) • v + (sin t / sin d) • w⟫ := rfl
      _ = (sin (d - t) / sin d) * ⟪p, v⟫ + (sin t / sin d) * ⟪p, w⟫ := by
        simp [inner_add_right, inner_smul_right]
  have hinner_bound : ⟪p, arcPt d v w t⟫ ≤ cos d / cos (d / 2) := by
    rw [hinner_arc]
    have hdiv_nonneg : 0 ≤ sin (d - t) / sin d :=
      div_nonneg hsin_dt_nonneg (by linarith)
    have hdiv2_nonneg : 0 ≤ sin t / sin d :=
      div_nonneg hsin_t_nonneg (by linarith)
    have h1 : (sin (d - t) / sin d) * ⟪p, v⟫ ≤ (sin (d - t) / sin d) * cos d :=
      mul_le_mul_of_nonneg_left hpv_inner_le_cos_d hdiv_nonneg
    have h2 : (sin t / sin d) * ⟪p, w⟫ ≤ (sin t / sin d) * cos d :=
      mul_le_mul_of_nonneg_left hpw_inner_le_cos_d hdiv2_nonneg
    have hsum_le : (sin (d - t) / sin d) * ⟪p, v⟫ + (sin t / sin d) * ⟪p, w⟫ ≤
        (sin (d - t) / sin d) * cos d + (sin t / sin d) * cos d :=
      add_le_add h1 h2
    have hsum_eq : (sin (d - t) / sin d) * cos d + (sin t / sin d) * cos d =
        cos d * (sin (d - t) + sin t) / sin d := by
      ring
    have hsin_sum_eq : cos d * (sin (d - t) + sin t) / sin d =
        cos d * cos (d / 2 - t) / cos (d / 2) := by
      have h := sin_sub_add_sin d t ⟨hdpos, hd_lt_pi⟩
      calc
        cos d * (sin (d - t) + sin t) / sin d =
            cos d * ((sin (d - t) + sin t) / sin d) := by ring
        _ = cos d * (cos (d / 2 - t) / cos (d / 2)) := by rw [h]
        _ = cos d * cos (d / 2 - t) / cos (d / 2) := by ring
    have hcos_dt_le_one : cos (d / 2 - t) ≤ 1 := Real.cos_le_one _
    have hfinal : cos d * cos (d / 2 - t) / cos (d / 2) ≤ cos d / cos (d / 2) := by
      have h_mul : cos d * cos (d / 2 - t) ≤ cos d * 1 :=
        mul_le_mul_of_nonneg_left hcos_dt_le_one (by linarith)
      have h_div : cos d * cos (d / 2 - t) / cos (d / 2) ≤ cos d * 1 / cos (d / 2) :=
        div_le_div_of_nonneg_right h_mul (by linarith)
      simpa using h_div
    linarith
  have hrad_def : hrad d = arccos (cos d / cos (d / 2)) := rfl
  have hsdist_arc : sdist p (arcPt d v w t) = arccos ⟪p, arcPt d v w t⟫ := rfl
  rw [hrad_def, hsdist_arc]
  exact Real.arccos_le_arccos hinner_bound

theorem eta_ge_cos_alpha (d a b : ℝ) (hd : 0 < d ∧ d < π / 2) (ha : d ≤ a ∧ a ≤ π / 2)
    (hb : d ≤ b ∧ b ≤ π / 2) : cos d / (1 + cos d) ≤ eta d a b := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases ha with ⟨hdlea, hale⟩
  rcases hb with ⟨hdleb, hble⟩
  -- cos d > 0
  have hcosd_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith
  have hcosd_nonneg : 0 ≤ cos d := le_of_lt hcosd_pos
  -- cos d < 1
  have hcosd_lt_one : cos d < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by nlinarith) hdpos
    simpa [Real.cos_zero] using h
  -- cos a ≥ 0
  have hcosa_nonneg : 0 ≤ cos a := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith
  -- cos b ≥ 0
  have hcosb_nonneg : 0 ≤ cos b := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith
  -- cos a ≤ cos d
  have hcosa_le_cosd : cos a ≤ cos d := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) hdlea
  -- cos b ≤ cos d
  have hcosb_le_cosd : cos b ≤ cos d := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) hdleb
  -- sin a > 0
  have hsina_pos : 0 < sin a := by
    apply Real.sin_pos_of_mem_Ioo
    constructor <;> nlinarith
  have hsina_nonneg : 0 ≤ sin a := le_of_lt hsina_pos
  -- sin b > 0
  have hsinb_pos : 0 < sin b := by
    apply Real.sin_pos_of_mem_Ioo
    constructor <;> nlinarith
  have hsinb_nonneg : 0 ≤ sin b := le_of_lt hsinb_pos
  -- Key inequality: sin a * sin b ≤ 1 - cos a * cos b
  have hkey : sin a * sin b ≤ 1 - cos a * cos b := by
    have hsq : (sin a * sin b) ^ 2 ≤ (1 - cos a * cos b) ^ 2 := by
      have h1 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
      have h2 : sin b ^ 2 + cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
      have hsin_sq_a : sin a ^ 2 = 1 - cos a ^ 2 := by linarith
      have hsin_sq_b : sin b ^ 2 = 1 - cos b ^ 2 := by linarith
      calc
        (sin a * sin b) ^ 2 = (sin a ^ 2) * (sin b ^ 2) := by ring
        _ = (1 - cos a ^ 2) * (1 - cos b ^ 2) := by rw [hsin_sq_a, hsin_sq_b]
        _ = 1 - cos a ^ 2 - cos b ^ 2 + cos a ^ 2 * cos b ^ 2 := by ring
        _ ≤ 1 - 2 * cos a * cos b + cos a ^ 2 * cos b ^ 2 := by
          have hsqdiff : (cos a - cos b) ^ 2 ≥ 0 := sq_nonneg _
          nlinarith
        _ = (1 - cos a * cos b) ^ 2 := by ring
    have hnonneg_left : 0 ≤ sin a * sin b := mul_nonneg hsina_nonneg hsinb_nonneg
    have hnonneg_right : 0 ≤ 1 - cos a * cos b := by
      have hcosaprod_le_one : cos a * cos b ≤ 1 := by
        nlinarith [Real.cos_le_one a, Real.cos_le_one b]
      nlinarith
    exact ((sq_le_sq₀ hnonneg_left hnonneg_right).mp hsq)
  -- Second inequality: cos d * (1 - cos a * cos b) ≤ (cos d - cos a * cos b) * (1 + cos d)
  have hsecond : cos d * (1 - cos a * cos b) ≤ (cos d - cos a * cos b) * (1 + cos d) := by
    nlinarith
  -- Combine: cos d * (sin a * sin b) ≤ (cos d - cos a * cos b) * (1 + cos d)
  have hcombined : cos d * (sin a * sin b) ≤ (cos d - cos a * cos b) * (1 + cos d) := by
    nlinarith
  -- Now use div_le_div_iff₀
  have hden1 : 0 < 1 + cos d := by nlinarith
  have hden2 : 0 < sin a * sin b := mul_pos hsina_pos hsinb_pos
  rw [eta]
  rw [div_le_div_iff₀ hden1 hden2]
  -- Goal is now: cos d * (sin a * sin b) ≤ (cos d - cos a * cos b) * (1 + cos d)
  -- But we need to be careful: div_le_div_iff₀ gives a / b ≤ c / d ↔ a * d ≤ c * b
  -- So a = cos d, b = 1 + cos d, c = cos d - cos a * cos b, d = sin a * sin b
  -- a * d = cos d * (sin a * sin b)
  -- c * b = (cos d - cos a * cos b) * (1 + cos d)
  -- This matches hcombined
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcombined

theorem gam_le_alpha (d a b : ℝ) (hd : 0 < d ∧ d < π / 2) (ha : d ≤ a ∧ a ≤ π / 2)
    (hb : d ≤ b ∧ b ≤ π / 2) : gam d a b ≤ alpha d := by
  unfold gam alpha
  exact Real.arccos_le_arccos (eta_ge_cos_alpha d a b hd ha hb)

/-- The pigeonhole step of Proposition nor. -/
theorem exists_ge_two_pi_div_five {m : ℕ} (hm : 0 < m ∧ m ≤ 5) (β : Fin m → ℝ)
    (hβ : ∑ i, β i = 2 * π) : ∃ i, 2 * π / 5 ≤ β i := by
  rcases hm with ⟨hm_pos, hm_le⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
  by_contra! h
  -- h : ∀ i, β i < 2 * π / 5
  have hsum_lt : (∑ i, β i) < (∑ _i : Fin m, 2 * π / 5) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
    intro i hi
    exact h i
  have hsum_const : (∑ _i : Fin m, 2 * π / 5) = (m : ℝ) * (2 * π / 5) := by
    simpa [nsmul_eq_mul] using Fin.sum_const (2 * π / 5) (m := m)
  have hm_le' : (m : ℝ) ≤ 5 := by exact mod_cast hm_le
  have h_mul_le : (m : ℝ) * (2 * π / 5) ≤ 2 * π := by
    nlinarith [Real.pi_pos]
  have h_contra : (∑ i, β i) < 2 * π := by
    linarith
  linarith [hβ, h_contra]

theorem two_pi_lt_six_alpha (d : ℝ) (hd : 0 < d ∧ d < π / 2) : 2 * π < 6 * alpha d := by
  rcases alpha_bounds d hd with ⟨hlo, _⟩
  have h : π / 3 < alpha d := hlo
  nlinarith

/-- Faces have at most six sides: `m d < 2π` and `7 dlo > 2π`. -/
theorem face_size_le_six (m : ℕ) (d : ℝ) (hd : dlo ≤ d) (hm : m * d < 2 * π) : m ≤ 6 := by
  by_contra! h
  have hm7 : 7 ≤ m := by omega
  have hdlo_pos : 0 < dlo := by
    unfold dlo
    positivity
  have hdpos : 0 < d := by linarith
  have h7d : (7 : ℝ) * dlo ≤ (7 : ℝ) * d :=
    mul_le_mul_of_nonneg_left hd (by norm_num)
  have h7dpos : (7 : ℝ) * dlo > 2 * π := by
    linarith [two_pi_lt_seven_dlo]
  have hm_real : (m : ℝ) ≥ 7 := by exact_mod_cast hm7
  have hmd_ge : (m : ℝ) * d ≥ (7 : ℝ) * d :=
    mul_le_mul_of_nonneg_right hm_real (by linarith)
  have hmd_gt : (m : ℝ) * d > 2 * π := by
    linarith
  linarith

end Tammes15
