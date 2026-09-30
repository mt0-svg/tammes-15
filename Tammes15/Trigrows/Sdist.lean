import Tammes15.Trigrows.Rows
import Tammes15.Trigrows.Points

/-!
# Sphere basics: the spherical distance, equilateral pieces, T7, Lemmas shift and minimal


Basic facts on `sdist`; `T7_iff`, the trigonometric core of the long diagonal
relation (T7) with `θ = u₂ - b₁`; the equilateral triangle and the rhombus of Lemma faces;
`degree_le_five`, `exists_ge_pi_of_le_two` (the counts of Lemma minimal); `shift_move`, the first
variation step of Lemma shift for the curve `cos s • v + sin s • t`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace Topology

namespace Tammes15

theorem sdist_self (p : E3) (hp : ‖p‖ = 1) : sdist p p = 0 := by
  rw [sdist, real_inner_self_eq_norm_sq p, hp, one_pow]
  exact Real.arccos_one

theorem sdist_mem_Icc (p q : E3) : 0 ≤ sdist p q ∧ sdist p q ≤ π := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

theorem sdist_eq_zero_iff (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : sdist p q = 0 ↔ p = q := by
  have h_inner_le : inner ℝ p q ≤ 1 := real_inner_le_one_of_norm_eq_one hp hq
  have h_inner_eq_one_iff : inner ℝ p q = 1 ↔ p = q := inner_eq_one_iff_of_norm_eq_one hp hq
  constructor
  · intro h_sdist
    have h_arccos_zero : Real.arccos (inner ℝ p q) = 0 := h_sdist
    have h_one_le : 1 ≤ inner ℝ p q := ((Real.arccos_eq_zero).mp h_arccos_zero)
    have h_inner_eq_one : inner ℝ p q = 1 := le_antisymm h_inner_le h_one_le
    exact (h_inner_eq_one_iff.mp h_inner_eq_one)
  · intro h_eq
    have h_inner_eq_one : inner ℝ p q = 1 := by
      rw [← h_eq]
      exact inner_self_eq_one_of_norm_eq_one (𝕜 := ℝ) (x := p) hp
    have h_arccos_zero : Real.arccos (inner ℝ p q) = 0 := by
      rw [h_inner_eq_one, Real.arccos_one]
    exact h_arccos_zero

theorem le_sdist_iff (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (d : ℝ) (hd : 0 ≤ d ∧ d ≤ π) :
    d ≤ sdist p q ↔ ⟪p, q⟫ ≤ cos d := by
  rcases hd with ⟨hd0, hdπ⟩
  have hinner_abs : |⟪p, q⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm p q
    rw [hp, hq] at h
    rw [one_mul] at h
    exact h
  have hx_low : -1 ≤ ⟪p, q⟫ := by
    linarith [abs_le.mp hinner_abs]
  have hx_high : ⟪p, q⟫ ≤ 1 := by
    linarith [abs_le.mp hinner_abs]
  constructor
  · intro h
    have h_arccos_le_pi : arccos ⟪p, q⟫ ≤ π := Real.arccos_le_pi _
    have h_cos_le : cos (arccos ⟪p, q⟫) ≤ cos d :=
      Real.cos_le_cos_of_nonneg_of_le_pi hd0 h_arccos_le_pi h
    rw [Real.cos_arccos hx_low hx_high] at h_cos_le
    exact h_cos_le
  · intro h
    have h_arccos_le : arccos (cos d) ≤ arccos ⟪p, q⟫ :=
      Real.arccos_le_arccos h
    rw [Real.arccos_cos hd0 hdπ] at h_arccos_le
    exact h_arccos_le

theorem sdist_eq_angle (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : sdist p q = angle p q := by
  have h_inner : ⟪p, q⟫ = Real.cos (angle p q) :=
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hp hq
  unfold sdist
  rw [h_inner]
  have h0 : 0 ≤ angle p q := InnerProductGeometry.angle_nonneg p q
  have h1 : angle p q ≤ Real.pi := InnerProductGeometry.angle_le_pi p q
  rw [Real.arccos_cos h0 h1]

theorem sdist_neg_right (p q : E3) : sdist p (-q) = π - sdist p q := by
  unfold sdist
  rw [inner_neg_right, Real.arccos_neg]

theorem sdist_linearIsometry (O : E3 →ₗᵢ[ℝ] E3) (p q : E3) : sdist (O p) (O q) = sdist p q := by
  unfold sdist; rw [LinearIsometry.inner_map_map]

theorem norm_sub_sq_unit (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p - q‖ ^ 2 = 2 - 2 * cos (sdist p q) := by
  rw [cos_sdist p q hp hq, norm_sub_sq_real, hp, hq]
  ring

/-- (T7): with `θ` the angle at `A₂` between `A₂A₀` and `A₂A₃`, `e = dist(A₀, A₂)`, the condition
`dist(A₀, A₃) ≥ d` by the law of cosines. -/
theorem T7_iff (d e θ : ℝ) (hd : 0 < d ∧ d < π / 2) (he : 0 < e ∧ e < π) (hθ : 0 ≤ θ ∧ θ ≤ π) :
    cos e * cos d + sin e * sin d * cos θ ≤ cos d ↔ arccos (min 1 (cot d * tan (e / 2))) ≤ θ := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases he with ⟨he_pos, he_lt⟩
  rcases hθ with ⟨hθ_nonneg, hθ_le⟩
  have hd_sin_pos : 0 < sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd_pos (by linarith)
  have he_sin_pos : 0 < sin e :=
    Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
  have hd_cos_pos : 0 < cos d := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have he_half_pos : 0 < e / 2 := by linarith
  have he_half_lt_pi_div_two : e / 2 < π / 2 := by linarith
  have hcos_half_pos : 0 < cos (e / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, he_half_lt_pi_div_two⟩
  have hsin_half_pos : 0 < sin (e / 2) :=
    Real.sin_pos_of_pos_of_lt_pi he_half_pos (by linarith)
  set c := cot d * tan (e / 2) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    exact mul_pos (div_pos hd_cos_pos hd_sin_pos) (div_pos hsin_half_pos hcos_half_pos)
  have hc_eq : c = cos d * (1 - cos e) / (sin e * sin d) := by
    rw [hc_def, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    have h_sin_e : sin e = 2 * sin (e / 2) * cos (e / 2) := by
      calc
        sin e = sin (2 * (e / 2)) := by rw [show (2 : ℝ) * (e / 2) = e by ring]
        _ = 2 * sin (e / 2) * cos (e / 2) := by rw [Real.sin_two_mul]
    have h_one_minus_cos_e : 1 - cos e = 2 * sin (e / 2) ^ 2 := by
      have h := Real.cos_two_mul (e / 2)
      have hcos2 : cos (2 * (e / 2)) = cos e := by rw [show (2 : ℝ) * (e / 2) = e by ring]
      rw [hcos2] at h
      rw [h]
      have hsq := Real.sin_sq_add_cos_sq (e / 2)
      linarith
    rw [h_sin_e, h_one_minus_cos_e]
    field_simp [hd_sin_pos.ne.symm, he_sin_pos.ne.symm]
  have hpos_denom : 0 < sin e * sin d := mul_pos he_sin_pos hd_sin_pos
  constructor
  · intro h
    have hineq : sin e * sin d * cos θ ≤ cos d * (1 - cos e) := by linarith
    have hcosθ_le_c : cos θ ≤ c := by
      rw [hc_eq]
      rw [le_div_iff₀' hpos_denom]
      -- goal: (sin e * sin d) * cos θ ≤ cos d * (1 - cos e)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    by_cases hc_one : 1 ≤ c
    · have hmin : min 1 c = 1 := min_eq_left hc_one
      rw [hmin, Real.arccos_one]
      exact hθ_nonneg
    · have hc_lt_one : c < 1 := by linarith
      have hmin : min 1 c = c := min_eq_right (by linarith)
      rw [hmin]
      have harccos_c_le_arccos_cosθ : arccos c ≤ arccos (cos θ) :=
        Real.arccos_le_arccos hcosθ_le_c
      have harccos_cosθ_eq_θ : arccos (cos θ) = θ :=
        Real.arccos_cos hθ_nonneg hθ_le
      rw [harccos_cosθ_eq_θ] at harccos_c_le_arccos_cosθ
      exact harccos_c_le_arccos_cosθ
  · intro h
    by_cases hc_one : 1 ≤ c
    · have hmin : min 1 c = 1 := min_eq_left hc_one
      rw [hmin, Real.arccos_one] at h
      have hcosθ_le_one : cos θ ≤ 1 := Real.cos_le_one θ
      have h_key : sin e * sin d * cos θ ≤ cos d * (1 - cos e) := by
        calc
          sin e * sin d * cos θ ≤ sin e * sin d * 1 := by nlinarith
          _ = sin e * sin d := by ring
          _ ≤ cos d * (1 - cos e) := by
            rw [hc_eq] at hc_one
            have := (one_le_div hpos_denom).mp hc_one
            -- this: sin e * sin d ≤ cos d * (1 - cos e)
            exact this
      linarith
    · have hc_lt_one : c < 1 := by linarith
      have hmin : min 1 c = c := min_eq_right (by linarith)
      rw [hmin] at h
      have hc_nonneg : 0 ≤ c := by linarith
      have hc_le_one : c ≤ 1 := by linarith
      have hcosθ_le_c : cos θ ≤ c := by
        have h_arccos_c_le_θ : arccos c ≤ θ := h
        have h_cos_arccos_c : cos (arccos c) = c := Real.cos_arccos (by linarith) hc_le_one
        have h_cos_θ_le_cos_arccos_c : cos θ ≤ cos (arccos c) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg c) hθ_le h_arccos_c_le_θ
        rw [h_cos_arccos_c] at h_cos_θ_le_cos_arccos_c
        exact h_cos_θ_le_cos_arccos_c
      have h_key : sin e * sin d * cos θ ≤ cos d * (1 - cos e) := by
        rw [hc_eq] at hcosθ_le_c
        rw [le_div_iff₀' hpos_denom] at hcosθ_le_c
        -- hcosθ_le_c: (sin e * sin d) * cos θ ≤ cos d * (1 - cos e)
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcosθ_le_c
      linarith

theorem gam_equilateral (d : ℝ) (hd : 0 < d ∧ d < π) : gam d d d = alpha d := by
  rcases hd with ⟨hdpos, hdlt⟩
  unfold gam eta alpha
  congr 1
  have hsin_pos : sin d > 0 := Real.sin_pos_of_pos_of_lt_pi hdpos hdlt
  have hsin_sq_ne_zero : sin d * sin d ≠ 0 := mul_ne_zero hsin_pos.ne.symm hsin_pos.ne.symm
  have hcos_lt_one : cos d < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : 0 ≤ (0 : ℝ)) hdlt.le hdpos
    simpa [Real.cos_zero] using h
  have h_one_minus_cos_ne_zero : 1 - cos d ≠ 0 := by linarith
  have hcos_gt_neg_one : -1 < cos d := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hdpos.le (by linarith) hdlt
    rw [Real.cos_pi] at h
    linarith
  have h_one_plus_cos_ne_zero : 1 + cos d ≠ 0 := by linarith
  field_simp [hsin_sq_ne_zero, h_one_plus_cos_ne_zero]
  rw [Real.sin_sq]
  ring

theorem equilateral_angle (d : ℝ) (hd : 0 < d ∧ d < π) (v w₁ w₂ : E3) (hv : ‖v‖ = 1)
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (h₁ : sdist v w₁ = d) (h₂ : sdist v w₂ = d)
    (h₁₂ : sdist w₁ w₂ = d) : angle (tdir v w₁) (tdir v w₂) = alpha d := by
  rw [angle_tdir_eq_gam v w₁ w₂ hv hw₁ hw₂ (by rw [h₁]; exact hd) (by rw [h₂]; exact hd), h₁, h₂, h₁₂, gam_equilateral d hd]

/-- Lemma faces: in a rhombus opposite corners are equal. -/
theorem rhombus_opposite_angle (d : ℝ) (hd : 0 < d ∧ d < π) (v₁ v₂ v₃ v₄ : E3) (h₁ : ‖v₁‖ = 1)
    (h₂ : ‖v₂‖ = 1) (h₃ : ‖v₃‖ = 1) (h₄ : ‖v₄‖ = 1) (h₁₂ : sdist v₁ v₂ = d) (h₁₄ : sdist v₁ v₄ = d)
    (h₃₂ : sdist v₃ v₂ = d) (h₃₄ : sdist v₃ v₄ = d) :
    angle (tdir v₁ v₂) (tdir v₁ v₄) = angle (tdir v₃ v₂) (tdir v₃ v₄) := by
  have hdpos : 0 < d := hd.1
  have hdlt : d < π := hd.2
  have h₁₂_lt : sdist v₁ v₂ < π := by
    rw [h₁₂]
    exact hdlt
  have h₁₂_pos : 0 < sdist v₁ v₂ := by
    rw [h₁₂]
    exact hdpos
  have h₁₄_lt : sdist v₁ v₄ < π := by
    rw [h₁₄]
    exact hdlt
  have h₁₄_pos : 0 < sdist v₁ v₄ := by
    rw [h₁₄]
    exact hdpos
  have h₃₂_lt : sdist v₃ v₂ < π := by
    rw [h₃₂]
    exact hdlt
  have h₃₂_pos : 0 < sdist v₃ v₂ := by
    rw [h₃₂]
    exact hdpos
  have h₃₄_lt : sdist v₃ v₄ < π := by
    rw [h₃₄]
    exact hdlt
  have h₃₄_pos : 0 < sdist v₃ v₄ := by
    rw [h₃₄]
    exact hdpos
  calc
    angle (tdir v₁ v₂) (tdir v₁ v₄)
        = gam (sdist v₂ v₄) (sdist v₁ v₂) (sdist v₁ v₄) := by
      rw [angle_tdir_eq_gam v₁ v₂ v₄ h₁ h₂ h₄ ⟨h₁₂_pos, h₁₂_lt⟩ ⟨h₁₄_pos, h₁₄_lt⟩]
    _ = gam (sdist v₂ v₄) d d := by rw [h₁₂, h₁₄]
    _ = gam (sdist v₂ v₄) (sdist v₃ v₂) (sdist v₃ v₄) := by rw [h₃₂, h₃₄]
    _ = angle (tdir v₃ v₂) (tdir v₃ v₄) := by
      rw [angle_tdir_eq_gam v₃ v₂ v₄ h₃ h₂ h₄ ⟨h₃₂_pos, h₃₂_lt⟩ ⟨h₃₄_pos, h₃₄_lt⟩]

/-- Lemma minimal: corners at least `alpha d` summing to `2π` are at most five. -/
theorem degree_le_five (d : ℝ) (hd : 0 < d ∧ d < π / 2) (m : ℕ) (β : Fin m → ℝ)
    (hβ : ∀ i, alpha d ≤ β i) (hsum : ∑ i, β i = 2 * π) : m ≤ 5 := by
  by_contra! h
  -- h : ¬ m ≤ 5, i.e. 5 < m
  have h6m : 6 ≤ m := by omega
  rcases alpha_bounds d hd with ⟨h_alpha_gt, h_alpha_lt⟩
  -- h_alpha_gt: π/3 < alpha d, h_alpha_lt: alpha d < π/2
  have h_sum_le : (m : ℝ) * alpha d ≤ 2 * π := by
    calc
      (m : ℝ) * alpha d = (∑ i : Fin m, alpha d) := by
        simp
      _ ≤ ∑ i : Fin m, β i := Finset.sum_le_sum fun i _ => hβ i
      _ = 2 * π := hsum
  have h_ineq : (6 : ℝ) * (π / 3) < (m : ℝ) * alpha d := by
    have h6m' : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h6m
    nlinarith
  have h_six : (6 : ℝ) * (π / 3) = 2 * π := by ring
  linarith

/-- Lemma minimal: a vertex of degree one or two has a corner at least `π`. -/
theorem exists_ge_pi_of_le_two (m : ℕ) (hm : 0 < m ∧ m ≤ 2) (β : Fin m → ℝ)
    (hsum : ∑ i, β i = 2 * π) : ∃ i, π ≤ β i := by
  by_contra h
  push_neg at h
  have h_nonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    exact ⟨⟨0, hm.1⟩, Finset.mem_univ _⟩
  have h_sum_lt : (∑ i : Fin m, β i) < (∑ i : Fin m, π) :=
    Finset.sum_lt_sum_of_nonempty h_nonempty (fun i hi => h i)
  have h_sum_pi : (∑ i : Fin m, π) = (m : ℝ) * π := by
    simp
  have hm_le_2 : (m : ℝ) ≤ 2 := by
    exact mod_cast hm.2
  have h_mul : (m : ℝ) * π ≤ 2 * π := by
    nlinarith [Real.pi_pos]
  have h_lt : (∑ i : Fin m, β i) < 2 * π := by
    linarith
  linarith [hsum, h_lt]

theorem norm_cos_sin_unit (v t : E3) (hv : ‖v‖ = 1) (ht : ‖t‖ = 1) (hvt : ⟪v, t⟫ = 0) (s : ℝ) :
    ‖cos s • v + sin s • t‖ = 1 := by
  have h_nonneg : 0 ≤ ‖cos s • v + sin s • t‖ := norm_nonneg _
  have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
  apply (sq_eq_sq₀ h_nonneg h_one_nonneg).mp
  calc
    ‖cos s • v + sin s • t‖ ^ 2 = ‖cos s • v‖ ^ 2 + 2 * inner ℝ (cos s • v) (sin s • t) + ‖sin s • t‖ ^ 2 := by
      rw [norm_add_sq_real]
    _ = (‖cos s‖ * ‖v‖) ^ 2 + 2 * inner ℝ (cos s • v) (sin s • t) + (‖sin s‖ * ‖t‖) ^ 2 := by
      simp [norm_smul]
    _ = (‖cos s‖ * ‖v‖) ^ 2 + 2 * (cos s * (sin s * inner ℝ v t)) + (‖sin s‖ * ‖t‖) ^ 2 := by
      simp [inner_smul_left, inner_smul_right, mul_left_comm]
    _ = (‖cos s‖ * ‖v‖) ^ 2 + 2 * (cos s * (sin s * 0)) + (‖sin s‖ * ‖t‖) ^ 2 := by rw [hvt]
    _ = (‖cos s‖ * ‖v‖) ^ 2 + 2 * 0 + (‖sin s‖ * ‖t‖) ^ 2 := by ring
    _ = (‖cos s‖ * ‖v‖) ^ 2 + (‖sin s‖ * ‖t‖) ^ 2 := by ring
    _ = (‖cos s‖ * 1) ^ 2 + (‖sin s‖ * 1) ^ 2 := by rw [hv, ht]
    _ = ‖cos s‖ ^ 2 + ‖sin s‖ ^ 2 := by ring
    _ = |cos s| ^ 2 + |sin s| ^ 2 := by simp
    _ = (cos s) ^ 2 + (sin s) ^ 2 := by simp [sq_abs]
    _ = 1 := by rw [Real.cos_sq_add_sin_sq]
    _ = 1 ^ 2 := by norm_num

/-- Lemma shift, first variation: moving `v` along `cos s • v + sin s • t` for small `s > 0`
takes it strictly farther than `d` from each `w j`. -/
theorem shift_move {ι : Type*} [Fintype ι] (d : ℝ) (v t : E3) (w : ι → E3)
    (hw : ∀ j, ⟪v, w j⟫ < cos d ∨ (⟪v, w j⟫ = cos d ∧ ⟪t, w j⟫ < 0) ∨
      (⟪v, w j⟫ = cos d ∧ ⟪t, w j⟫ = 0 ∧ 0 < cos d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ ∀ j, ⟪cos s • v + sin s • t, w j⟫ < cos d := by
  set f : ι → ℝ → ℝ := fun j s => ⟪cos s • v + sin s • t, w j⟫
  have hf_cont (j : ι) : ContinuousAt (f j) 0 := by
    dsimp [f]
    have h_inner : ContinuousAt (fun (s : ℝ) => ⟪cos s • v + sin s • t, w j⟫) 0 := by
      refine ContinuousAt.inner ?_ ?_
      · have h_cos : ContinuousAt (fun (s : ℝ) => cos s • v) 0 :=
          ContinuousAt.smul (f := fun s : ℝ => cos s) (g := fun _ : ℝ => v)
            Real.continuous_cos.continuousAt continuousAt_const
        have h_sin : ContinuousAt (fun (s : ℝ) => sin s • t) 0 :=
          ContinuousAt.smul (f := fun s : ℝ => sin s) (g := fun _ : ℝ => t)
            Real.continuous_sin.continuousAt continuousAt_const
        exact ContinuousAt.add h_cos h_sin
      · exact continuousAt_const
    exact h_inner
  have hf0 (j : ι) : f j 0 = ⟪v, w j⟫ := by
    dsimp [f]
    simp [Real.cos_zero, Real.sin_zero]
  have h_event (j : ι) : ∀ᶠ s in 𝓝[>] 0, f j s < cos d := by
    rcases hw j with (hlt | hcase | hcase)
    · -- Case 1: ⟪v, w j⟫ < cos d
      have h0 : f j 0 < cos d := by
        rw [hf0 j]
        exact hlt
      have h_lt_nhds : ∀ᶠ s in 𝓝 0, f j s < cos d :=
        ContinuousAt.eventually_lt (hf_cont j) (continuousAt_const (x := 0) (y := cos d)) h0
      exact nhdsWithin_le_nhds (a := 0) (s := Set.Ioi 0) h_lt_nhds
    · -- Case 2: ⟪v, w j⟫ = cos d ∧ ⟪t, w j⟫ < 0
      rcases hcase with ⟨hav, hb⟩
      set b := ⟪t, w j⟫ with hb_def
      have hb_neg' : b < 0 := hb
      have hsin_ge (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 2 ≤ sin s := by
        have h := Real.sin_gt_sub_cube hs
        have hcube : s^3/6 ≤ s/6 := by
          have hsq : s^2 ≤ 1 := by
            nlinarith
          have : s^3 ≤ s := by
            calc
              s^3 = s * s^2 := by ring
              _ ≤ s * 1 := mul_le_mul_of_nonneg_left hsq (by linarith)
              _ = s := by simp
          nlinarith
        have : s - s^3/6 ≥ s/2 := by
          nlinarith
        linarith
      have hcos_bound (s : ℝ) : cos d * (cos s - 1) ≤ s^2/2 := by
        have h_abs : |cos d * (cos s - 1)| ≤ s^2/2 := by
          calc
            |cos d * (cos s - 1)| = |cos d| * |cos s - 1| := abs_mul _ _
            _ ≤ 1 * |cos s - 1| := by
              have h_abs_cos := Real.abs_cos_le_one d
              have h_nonneg : 0 ≤ |cos s - 1| := abs_nonneg _
              nlinarith
            _ = |cos s - 1| := by simp
            _ = -(cos s - 1) := by
              rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one s))]
            _ = 1 - cos s := by ring
            _ ≤ s^2/2 := by
              linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
        nlinarith [abs_le.mp h_abs]
      set δ : ℝ := min ε (min 1 (-b / 2)) with hδ_def
      have hδ_pos : 0 < δ := by
        refine lt_min_iff.mpr ⟨hε, lt_min_iff.mpr ⟨by norm_num, ?_⟩⟩
        linarith
      have h_main : ∀ s, 0 < s → s < δ → f j s < cos d := by
        intro s hs hsδ
        have hs1 : s ≤ 1 := by
          have : δ ≤ 1 := by
            rw [hδ_def]
            exact le_trans (min_le_right ε (min 1 (-b / 2))) (min_le_left 1 (-b / 2))
          linarith
        have hs_negb : s < -b := by
          have : δ ≤ -b / 2 := by
            rw [hδ_def]
            exact le_trans (min_le_right ε (min 1 (-b / 2))) (min_le_right 1 (-b / 2))
          linarith
        dsimp [f]
        simp [inner_add_left, inner_smul_left, hav]
        rw [← hb_def]
        have hgoal : cos d * (cos s - 1) + sin s * b < 0 := by
          have h1 : cos d * (cos s - 1) ≤ s^2/2 := hcos_bound s
          have h2 : sin s * b ≤ (s/2) * b := by
            have hsin := hsin_ge s hs hs1
            nlinarith
          have h3 : (s/2) * b < s^2/2 + s^2/2 := by
            nlinarith
          nlinarith
        nlinarith
      have h_mem : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] 0 := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.Ioo (-1 : ℝ) δ, Ioo_mem_nhds (by norm_num) hδ_pos, ?_⟩
        intro x hx
        rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
        exact ⟨hx3, hx2⟩
      refine Filter.mem_of_superset h_mem ?_
      intro s hs
      rcases hs with ⟨hs_left, hs_right⟩
      exact h_main s hs_left hs_right
    · -- Case 3: ⟪v, w j⟫ = cos d ∧ ⟪t, w j⟫ = 0 ∧ 0 < cos d
      rcases hcase with ⟨hav, ht, hcos_pos⟩
      have h_main : ∀ s, 0 < s → s < π → f j s < cos d := by
        intro s hs hsπ
        dsimp [f]
        simp [inner_add_left, inner_smul_left, hav, ht]
        have hcos_lt_one : cos s < 1 := by
          have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) hs
          simpa [Real.cos_zero] using h
        nlinarith
      set δ : ℝ := min ε π with hδ_def
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨hε, Real.pi_pos⟩
      have h_mem : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] 0 := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.Ioo (-1 : ℝ) δ, Ioo_mem_nhds (by norm_num) hδ_pos, ?_⟩
        intro x hx
        rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
        exact ⟨hx3, hx2⟩
      refine Filter.mem_of_superset h_mem ?_
      intro s hs
      rcases hs with ⟨hs_left, hs_right⟩
      have hsπ : s < π := by
        have : δ ≤ π := min_le_right ε π
        linarith
      exact h_main s hs_left hsπ
  have h_all : ∀ᶠ s in 𝓝[>] 0, ∀ j, f j s < cos d := by
    rw [Filter.eventually_all]
    intro j
    exact h_event j
  have h_pos : ∀ᶠ s in 𝓝[>] 0, (0 : ℝ) < s :=
    self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)
  have h_lt_eps : ∀ᶠ s in 𝓝[>] 0, s < ε :=
    nhdsWithin_le_nhds (a := 0) (s := Set.Ioi 0)
      (isOpen_Iio.mem_nhds (by linarith : (0 : ℝ) < ε))
  have h_inter : ∀ᶠ s in 𝓝[>] 0, (0 < s ∧ s < ε ∧ ∀ j, f j s < cos d) := by
    filter_upwards [h_pos, h_lt_eps, h_all] with s hpos hlt hall
    exact ⟨hpos, hlt, hall⟩
  obtain ⟨s, hs⟩ := Filter.nonempty_of_mem h_inter
  refine ⟨s, hs.1, hs.2.1, hs.2.2⟩

end Tammes15
