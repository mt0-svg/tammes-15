import Tammes15.Geom.Nor
import Tammes15.Rattlers.HexPoly
import Tammes15.Rattlers.HexChord
import Tammes15.Geom.Frame

/-!
# The ten vertex polygon of Proposition 4.6

Two circles of radius `h = h(d)` about `C` and `R`, `sdist C R = d`; with `γ = tanAng d h` and
`s = (π - γ) / 2`, five vertices on the outer arc of each circle, at the angles
`ψ_j = -(π - γ) + j s = (j - 2) s`, `j = 0, …, 4`, in the frames `(T, F, C)` and
`(-(cos d • T + sin d • C), -F, R)`.

The polygon is the image under a rotation of the model polygon `qm d` in coordinates
(`qpoly_eq_map`). In the model, `smap d` is the rotation by `π` exchanging the two circles and
`qm d (j + 5) = smap d (qm d j)`, so strict support reduces to the sides `0, …, 4`:

* a chord of the circle about `C` against the other vertices of that circle (`chord_CC`: the pole
  of the chord between the angles `μ ∓ δ` is `2 sin h sin δ • (-(cos h cos μ), -(cos h sin μ),
  sin h cos δ)`, `cross_mpt`);
* such a chord against the disc about `R` (`chord_CR`, from `onehex_chord_margin` and the Cauchy
  Schwarz bound `cap_real`);
* the common tangent side, whose pole is a positive multiple of the tangent pole `nhat h γ` at both
  ends (`tangent_T`, from the tangency relation `cos h cos γ (1 + cos d) = -(sin h sin d)`).

The perimeter is `8 chordC h s + 2 tanLen d h = hexPoly d h` (`qpoly_perim`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- The step `s = (π - γ) / 2` between consecutive vertices on one circle. -/
noncomputable def qstep (d : ℝ) : ℝ := (π - tanAng d (hrad d)) / 2

/-- The angle `ψ_j = -(π - γ) + j s` of the `j`-th vertex on its circle. -/
noncomputable def qang (d : ℝ) (j : ℕ) : ℝ := -(π - tanAng d (hrad d)) + j * qstep d

/-- The point of angle `ψ` on the circle of radius `h` about `C`, in the frame `(T, F, C)`. -/
noncomputable def cpt (h ψ : ℝ) (T F C : E3) : E3 := cos h • C + sin h • (cos ψ • T + sin ψ • F)

/-- The ten vertex polygon of Proposition 4.6, read modulo 10. -/
noncomputable def qpoly (d : ℝ) (T F C : E3) (j : ℕ) : E3 :=
  if j % 10 < 5 then cpt (hrad d) (qang d (j % 10)) T F C
  else cpt (hrad d) (qang d (j % 10 - 5)) (-(cos d • T + sin d • C)) (-F) (cos d • C - sin d • T)

/-! ## Bounds on `[dlo, dhi]` -/

/-- `tan h(d) tan (d / 2) < 1` below `π / 3`. -/
theorem tan_hrad_mul_tan_half_lt_one (d : ℝ) (hd : 0 < d ∧ d < π / 3) :
    tan (hrad d) * tan (d / 2) < 1 := by
  have hc2 : 0 < cos (d / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs2 : 0 < sin (d / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hcd : 1 / 2 < cos d := by
    rw [← cos_pi_div_three]
    exact cos_lt_cos_of_nonneg_of_le_pi hd.1.le (by linarith [pi_pos]) hd.2
  have e1 : cos d = 2 * cos (d / 2) ^ 2 - 1 := by rw [← cos_two_mul]; ring_nf
  have hsc : sin (d / 2) ^ 2 = 1 - cos (d / 2) ^ 2 := by
    have := sin_sq_add_cos_sq (d / 2); linarith
  have hy : 3 / 4 < cos (d / 2) ^ 2 := by linarith
  have hx0 : 0 < cos d / cos (d / 2) := div_pos (by linarith) hc2
  unfold hrad
  rw [tan_arccos, tan_eq_sin_div_cos, div_mul_div_comm, div_lt_one (mul_pos hx0 hc2)]
  have hxc : cos d / cos (d / 2) * cos (d / 2) = cos d := by field_simp
  rw [hxc]
  have h1x : 1 - (cos d / cos (d / 2)) ^ 2 = (cos (d / 2) ^ 2 - cos d ^ 2) / cos (d / 2) ^ 2 := by
    field_simp
  have hrw : √(1 - (cos d / cos (d / 2)) ^ 2) * sin (d / 2) =
      √((1 - (cos d / cos (d / 2)) ^ 2) * sin (d / 2) ^ 2) := by
    rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hs2.le]
  rw [hrw, Real.sqrt_lt' (by linarith), h1x, div_mul_eq_mul_div, div_lt_iff₀ (by positivity), hsc,
    e1]
  nlinarith [sq_nonneg (cos (d / 2) ^ 2 - 3 / 4)]

/-- The angle `γ = tanAng d h(d)` lies in `(π/2, π)` and its cosine is `-(tan h tan (d/2))`. -/
theorem tanAng_facts (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) :
    π / 2 < tanAng d (hrad d) ∧ tanAng d (hrad d) < π ∧
      cos (tanAng d (hrad d)) = -(tan (hrad d) * tan (d / 2)) := by
  have hdpos : 0 < d := by
    have h : π / 4 < d := lt_of_lt_of_le pi_div_four_lt_dlo hlo
    have hpi_pos : 0 < π := by exact Real.pi_pos
    linarith
  have hd_lt_pi_div_three : d < π / 3 := lt_of_le_of_lt hhi dhi_lt_pi_div_three
  have hrad_pos : 0 < hrad d := by
    have hmem := hrad_mem_of_Icc hlo (le_refl d) (le_refl d) hhi
    exact hmem.1
  have hrad_lt_pi_div_two : hrad d < π / 2 := by
    have hmem := hrad_mem_of_Icc hlo (le_refl d) (le_refl d) hhi
    exact hmem.2.2.2
  have hd2_pos : 0 < d / 2 := by linarith
  have hd2_lt_pi_div_two : d / 2 < π / 2 := by linarith
  have ht_pos : 0 < tan (hrad d) * tan (d / 2) := by
    have h1 : 0 < tan (hrad d) := Real.tan_pos_of_pos_of_lt_pi_div_two hrad_pos hrad_lt_pi_div_two
    have h2 : 0 < tan (d / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two hd2_pos hd2_lt_pi_div_two
    exact mul_pos h1 h2
  have ht_lt_one : tan (hrad d) * tan (d / 2) < 1 :=
    tan_hrad_mul_tan_half_lt_one d ⟨hdpos, hd_lt_pi_div_three⟩
  have hcos_eq : cos (tanAng d (hrad d)) = -(tan (hrad d) * tan (d / 2)) := by
    rw [tanAng]
    have hneg_t_ge_neg_one : -1 ≤ -(tan (hrad d) * tan (d / 2)) := by
      linarith
    have hneg_t_le_one : -(tan (hrad d) * tan (d / 2)) ≤ 1 := by
      linarith
    rw [Real.cos_arccos hneg_t_ge_neg_one hneg_t_le_one]
  have hpi_div_two_lt : π / 2 < tanAng d (hrad d) := by
    rw [tanAng]
    have h_neg_t_lt_zero : -(tan (hrad d) * tan (d / 2)) < 0 := by linarith
    have h_neg_t_ge_neg_one : -1 ≤ -(tan (hrad d) * tan (d / 2)) := by
      linarith
    have h_zero_le_one : (0 : ℝ) ≤ 1 := by norm_num
    have h_arccos_lt : Real.arccos 0 < Real.arccos (-(tan (hrad d) * tan (d / 2))) :=
      Real.arccos_lt_arccos h_neg_t_ge_neg_one h_neg_t_lt_zero h_zero_le_one
    rw [Real.arccos_zero] at h_arccos_lt
    exact h_arccos_lt
  have h_lt_pi : tanAng d (hrad d) < π := by
    rw [tanAng]
    have h_le : Real.arccos (-(tan (hrad d) * tan (d / 2))) ≤ π := Real.arccos_le_pi _
    have h_ne : Real.arccos (-(tan (hrad d) * tan (d / 2))) ≠ π := by
      intro h_eq
      have h_le_neg_one : -(tan (hrad d) * tan (d / 2)) ≤ -1 := by
        rwa [Real.arccos_eq_pi] at h_eq
      have : tan (hrad d) * tan (d / 2) ≥ 1 := by linarith
      linarith
    exact lt_of_le_of_ne h_le h_ne
  exact ⟨hpi_div_two_lt, h_lt_pi, hcos_eq⟩

/-- The tangency relation. -/
theorem tangency_rel (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) :
    cos (hrad d) * cos (tanAng d (hrad d)) * (1 + cos d) = -(sin (hrad d) * sin d) := by
  obtain ⟨-, -, hcos⟩ := tanAng_facts d hlo hhi
  obtain ⟨hh0, -, -, hh2⟩ := hrad_mem_of_Icc hlo le_rfl le_rfl hhi
  have hd0 : 0 < d := by linarith [pi_div_four_lt_dlo, pi_pos]
  have hd1 : d < π / 3 := by linarith [dhi_lt_pi_div_three]
  have hc2 : 0 < cos (d / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hch : 0 < cos (hrad d) := cos_pos_of_mem_Ioo ⟨by linarith, hh2⟩
  have e1 : cos d = 2 * cos (d / 2) ^ 2 - 1 := by rw [← cos_two_mul]; ring_nf
  have e2 : sin d = 2 * sin (d / 2) * cos (d / 2) := by rw [← sin_two_mul]; ring_nf
  rw [hcos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, e1, e2]
  field_simp
  ring

theorem qstep_mem (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) : 0 < qstep d ∧ qstep d < π / 4 := by
  obtain ⟨h1, h2, -⟩ := tanAng_facts d hlo hhi
  unfold qstep
  constructor <;> linarith

theorem qang_eq (d : ℝ) (j : ℕ) : qang d j = ((j : ℝ) - 2) * qstep d := by
  unfold qang qstep; ring

/-! ## The model in coordinates -/

/-- The model polygon. -/
noncomputable abbrev qm (d : ℝ) : ℕ → E3 := qpoly d ex ey ez

/-- A point of the circle of radius `h` about `ez`. -/
noncomputable def mpt (h ψ : ℝ) : E3 := !₂[sin h * cos ψ, sin h * sin ψ, cos h]

/-- The rotation by `π` exchanging `ez` and `cos d • ez - sin d • ex`. -/
noncomputable def smap (d : ℝ) (v : E3) : E3 :=
  !₂[-(cos d * v 0) - sin d * v 2, -v 1, -(sin d * v 0) + cos d * v 2]

theorem cpt_model (h ψ : ℝ) : cpt h ψ ex ey ez = mpt h ψ := by
  ext i; fin_cases i <;> simp [cpt, mpt, ex, ey, ez]

theorem smap_cpt_model (d h ψ : ℝ) :
    smap d (cpt h ψ ex ey ez) =
      cpt h ψ (-(cos d • ex + sin d • ez)) (-ey) (cos d • ez - sin d • ex) := by
  ext i; fin_cases i <;> simp [cpt, smap, ex, ey, ez] <;> ring

theorem smap_smap (d : ℝ) (v : E3) : smap d (smap d v) = v := by
  ext i; fin_cases i <;> simp [smap]
  · linear_combination (v 0) * sin_sq_add_cos_sq d
  · linear_combination (v 2) * sin_sq_add_cos_sq d

theorem inner_smap_left (d : ℝ) (a b : E3) : ⟪smap d a, b⟫ = ⟪a, smap d b⟫ := by
  simp only [inner_coords, smap]; simp; ring

theorem inner_smap (d : ℝ) (a b : E3) : ⟪smap d a, smap d b⟫ = ⟪a, b⟫ := by
  rw [inner_smap_left, smap_smap]

theorem norm_smap (d : ℝ) (a : E3) : ‖smap d a‖ = ‖a‖ := by
  have h := inner_smap d a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem triple_smap (d : ℝ) (a b c : E3) :
    ⟪cross (smap d a) (smap d b), smap d c⟫ = ⟪cross a b, c⟫ := by
  simp only [inner_coords, cross_coords, smap]; simp
  linear_combination (a 0 * b 1 * c 2 - a 0 * b 2 * c 1 - a 1 * b 0 * c 2 + a 1 * b 2 * c 0 +
    a 2 * b 0 * c 1 - a 2 * b 1 * c 0) * (sin_sq_add_cos_sq d)

theorem sdist_smap (d : ℝ) (a b : E3) : sdist (smap d a) (smap d b) = sdist a b := by
  unfold sdist; rw [inner_smap]

theorem qm_lt5 (d : ℝ) (j : ℕ) (hj : j < 5) : qm d j = mpt (hrad d) (qang d j) := by
  simp only [qm, qpoly, Nat.mod_eq_of_lt (show j < 10 by omega), ite_eq_left hj, cpt_model]

theorem qm_mod (d : ℝ) (j : ℕ) : qm d j = qm d (j % 10) := by
  simp only [qm, qpoly, Nat.mod_mod]

theorem qm_add5 (d : ℝ) (j : ℕ) : qm d (j + 5) = smap d (qm d j) := by
  simp only [qm, qpoly]
  by_cases hj : j % 10 < 5
  · have h1 : (j + 5) % 10 = j % 10 + 5 := by omega
    rw [ite_eq_left hj, h1, ite_eq_right (by omega), Nat.add_sub_cancel, smap_cpt_model]
  · have h1 : (j + 5) % 10 = j % 10 - 5 := by omega
    rw [ite_eq_right hj, h1, ite_eq_left (by omega), ← smap_cpt_model, smap_smap]

theorem qm_ge5 (d : ℝ) (j : ℕ) (hj : j < 5) :
    qm d (j + 5) = smap d (mpt (hrad d) (qang d j)) := by
  rw [qm_add5, qm_lt5 d j hj]

theorem qm_periodic (d : ℝ) (j : ℕ) : qm d (j + 10) = qm d j := by
  rw [qm_mod d (j + 10), qm_mod d j, Nat.add_mod_right]

theorem norm_mpt (h ψ : ℝ) : ‖mpt h ψ‖ = 1 := by
  have h2 : ‖mpt h ψ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_coords]; simp [mpt]
    linear_combination (sin h ^ 2) * sin_sq_add_cos_sq ψ + sin_sq_add_cos_sq h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

theorem norm_qm (d : ℝ) (j : ℕ) : ‖qm d j‖ = 1 := by
  rw [qm_mod]
  by_cases hj : j % 10 < 5
  · rw [qm_lt5 d _ hj, norm_mpt]
  · obtain ⟨t, ht⟩ : ∃ t, j % 10 = t + 5 := ⟨j % 10 - 5, by omega⟩
    rw [ht, qm_ge5 d t (by omega), norm_smap, norm_mpt]

/-! ## Strict support in the model -/

/-- The pole of a chord of the circle about `ez`. -/
theorem cross_mpt (h μ δ : ℝ) :
    cross (mpt h (μ - δ)) (mpt h (μ + δ)) =
      (2 * sin h * sin δ) • !₂[-(cos h * cos μ), -(cos h * sin μ), sin h * cos δ] := by
  rw [cross_coords]
  ext i; fin_cases i <;> simp [mpt, sin_add, sin_sub, cos_add, cos_sub]
  · ring
  · ring
  · linear_combination (2 * sin h ^ 2 * cos δ * sin δ) * sin_sq_add_cos_sq μ

theorem inner_chord_mpt (h μ δ ψ : ℝ) :
    ⟪!₂[-(cos h * cos μ), -(cos h * sin μ), sin h * cos δ], mpt h ψ⟫ =
      sin h * cos h * (cos δ - cos (ψ - μ)) := by
  rw [inner_coords]; simp [mpt, cos_sub]; ring

theorem inner_chord_smap_mpt (d h μ δ ψ : ℝ) :
    ⟪!₂[-(cos h * cos μ), -(cos h * sin μ), sin h * cos δ], smap d (mpt h ψ)⟫ =
      cos h * (cos h * sin d * cos μ + sin h * cos δ * cos d) +
        sin h * ((cos h * cos μ * cos d - sin h * cos δ * sin d) * cos ψ +
          (cos h * sin μ) * sin ψ) := by
  rw [inner_coords]; simp [mpt, smap]; ring

theorem chord_norm_sq (d h μ δ : ℝ) :
    (cos h * cos μ * cos d - sin h * cos δ * sin d) ^ 2 + (cos h * sin μ) ^ 2 +
      (cos h * sin d * cos μ + sin h * cos δ * cos d) ^ 2 = cos h ^ 2 + sin h ^ 2 * cos δ ^ 2 := by
  linear_combination (cos h ^ 2 * cos μ ^ 2 + sin h ^ 2 * cos δ ^ 2) * sin_sq_add_cos_sq d +
    cos h ^ 2 * sin_sq_add_cos_sq μ

/-- A disc strictly on one side of a plane, in coordinates. -/
theorem cap_real (c s X a b ψ : ℝ) (hc : 0 < c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hX : s * √(a ^ 2 + b ^ 2 + X ^ 2) < X) : 0 < c * X + s * (a * cos ψ + b * sin ψ) := by
  have hA : 0 ≤ a ^ 2 + b ^ 2 + X ^ 2 := by positivity
  have hsq := Real.sq_sqrt hA
  have hn : 0 ≤ s * √(a ^ 2 + b ^ 2 + X ^ 2) := mul_nonneg hs (Real.sqrt_nonneg _)
  have hX0 : 0 < X := lt_of_le_of_lt hn hX
  have h1 : (s * √(a ^ 2 + b ^ 2 + X ^ 2)) ^ 2 < X ^ 2 := pow_lt_pow_left₀ hX hn two_ne_zero
  rw [mul_pow, hsq] at h1
  have hw : (a * cos ψ + b * sin ψ) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (a * sin ψ - b * cos ψ), sin_sq_add_cos_sq ψ]
  have hw' : s ^ 2 * (a * cos ψ + b * sin ψ) ^ 2 ≤ s ^ 2 * (a ^ 2 + b ^ 2) :=
    mul_le_mul_of_nonneg_left hw (sq_nonneg s)
  have h2 : (s * (a * cos ψ + b * sin ψ)) ^ 2 < (c * X) ^ 2 := by
    rw [mul_pow, mul_pow]; nlinarith
  have := abs_lt_of_sq_lt_sq' h2 (by positivity)
  linarith [this.1]

/-- The tangent pole at the vertex `ψ_4 = π - γ` of the circle about `ez`. -/
noncomputable def nhat (h γ : ℝ) : E3 := !₂[cos h * cos γ, -(cos h * sin γ), sin h]

theorem norm_nhat (h γ : ℝ) : ‖nhat h γ‖ = 1 := by
  apply norm_eq_one_of_sq
  rw [← real_inner_self_eq_norm_sq, inner_coords]; simp [nhat]
  linear_combination cos h ^ 2 * sin_sq_add_cos_sq γ + sin_sq_add_cos_sq h

theorem inner_nhat_mpt (h γ ψ : ℝ) :
    ⟪nhat h γ, mpt h ψ⟫ = sin h * cos h * (1 - cos (ψ - (π - γ))) := by
  rw [inner_coords]; simp [nhat, mpt, cos_sub, sin_pi_sub]; ring

theorem smap_nhat (d h γ : ℝ) (hd : cos d ≠ -1)
    (htan : cos h * cos γ * (1 + cos d) = -(sin h * sin d)) :
    smap d (nhat h γ) = !₂[cos h * cos γ, cos h * sin γ, sin h] := by
  have hd' : 1 + cos d ≠ 0 := fun h0 => hd (by linarith)
  have h3 : -(sin d * (cos h * cos γ)) + cos d * sin h = sin h := by
    have key : (1 + cos d) * (-(sin d * (cos h * cos γ)) + cos d * sin h - sin h) = 0 := by
      linear_combination (-sin d) * htan + sin h * sin_sq_add_cos_sq d
    have := (mul_eq_zero.mp key).resolve_left hd'
    linarith
  ext i; fin_cases i <;> simp [smap, nhat]
  · linear_combination (-1 : ℝ) * htan
  · linarith

theorem inner_nhat'_mpt (h γ ψ : ℝ) :
    ⟪!₂[cos h * cos γ, cos h * sin γ, sin h], mpt h ψ⟫ =
      sin h * cos h * (1 - cos (ψ - (-(π - γ)))) := by
  rw [inner_coords, show ψ - -(π - γ) = (ψ - γ) + π by ring, cos_add_pi, cos_sub]
  simp [mpt]; ring

/-- The cross product of two vectors orthogonal to a unit vector is a multiple of it. -/
theorem cross_eq_smul_of_orth (a b n : E3) (hn : ‖n‖ = 1) (ha : ⟪a, n⟫ = 0) (hb : ⟪b, n⟫ = 0) :
    cross a b = ⟪cross a b, n⟫ • n := by
  have h1 : cross (cross a b) n = ⟪a, n⟫ • b - ⟪b, n⟫ • a := by
    simp only [cross_coords, inner_coords]
    ext i; fin_cases i <;> simp <;> ring
  have h2 : cross n (cross (cross a b) n) = ⟪n, n⟫ • cross a b - ⟪n, cross a b⟫ • n := by
    simp only [cross_coords, inner_coords]
    ext i; fin_cases i <;> simp <;> ring
  rw [ha, hb, zero_smul, zero_smul, sub_zero] at h1
  have h0 : cross n 0 = 0 := by rw [cross_coords]; ext i; fin_cases i <;> simp
  rw [h1, h0, real_inner_self_eq_norm_sq, hn, one_pow, one_smul, real_inner_comm] at h2
  exact (sub_eq_zero.mp h2.symm)

/-- The orientation of the tangent side. -/
theorem tangent_lambda_pos (d h γ : ℝ) (hh : 0 < h ∧ h < π / 2) (hγ : 0 < γ ∧ γ < π)
    (hd : 0 < d ∧ d < π) (htan : cos h * cos γ * (1 + cos d) = -(sin h * sin d)) :
    0 < ⟪cross (mpt h (π - γ)) (smap d (mpt h (-(π - γ)))), nhat h γ⟫ := by
  have hc : 0 < cos h := cos_pos_of_mem_Ioo ⟨by linarith, hh.2⟩
  have hsγ : 0 < sin γ := sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 hd.2
  have key : cos h * ⟪cross (mpt h (π - γ)) (smap d (mpt h (-(π - γ)))), nhat h γ⟫ =
      sin γ * sin d := by
    rw [inner_coords, cross_coords]
    simp [mpt, smap, nhat, cos_pi_sub, sin_pi_sub]
    linear_combination (-(sin γ * sin h * (cos h ^ 2 + sin h ^ 2))) * htan +
      (sin γ * sin d * (cos h ^ 2 + sin h ^ 2 + 1)) * sin_sq_add_cos_sq h
  have : 0 < cos h * ⟪cross (mpt h (π - γ)) (smap d (mpt h (-(π - γ)))), nhat h γ⟫ := by
    rw [key]; positivity
  exact (mul_pos_iff_of_pos_left hc).mp this

/-- `cos` separates an angle in `(δ, π]` in absolute value from `δ`. -/
theorem cos_lt_cos_abs (x δ : ℝ) (hδ : 0 ≤ δ) (hx1 : δ < |x|) (hx2 : |x| ≤ π) :
    cos x < cos δ := by
  rw [← cos_abs x]
  exact cos_lt_cos_of_nonneg_of_le_pi hδ hx2 hx1

theorem cos_lt_one_of_abs (x : ℝ) (h0 : 0 < |x|) (h1 : |x| ≤ π) : cos x < 1 := by
  have := cos_lt_cos_abs x 0 le_rfl h0 h1
  rwa [cos_zero] at this

/-- Side `i < 4` against a vertex `j` of the same circle. -/
theorem chord_CC (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (i j : ℕ) (hi : i < 4) (hj : j < 5)
    (hji : j ≠ i) (hji' : j ≠ i + 1) :
    0 < ⟪cross (qm d i) (qm d (i + 1)), qm d j⟫ := by
  obtain ⟨hh0, -, -, hh2⟩ := hrad_mem_of_Icc hlo le_rfl le_rfl hhi
  obtain ⟨hs0, hs4⟩ := qstep_mem d hlo hhi
  have hsh : 0 < sin (hrad d) := sin_pos_of_pos_of_lt_pi hh0 (by linarith [pi_pos])
  have hch : 0 < cos (hrad d) := cos_pos_of_mem_Ioo ⟨by linarith, hh2⟩
  have hsδ : 0 < sin (qstep d / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have e1 : qm d i = mpt (hrad d) (((i : ℝ) - 3 / 2) * qstep d - qstep d / 2) := by
    rw [qm_lt5 d i (by omega), qang_eq]; congr 1; ring
  have e2 : qm d (i + 1) = mpt (hrad d) (((i : ℝ) - 3 / 2) * qstep d + qstep d / 2) := by
    rw [qm_lt5 d (i + 1) (by omega), qang_eq]; congr 1; push_cast; ring
  rw [e1, e2, cross_mpt, real_inner_smul_left, qm_lt5 d j hj, qang_eq, inner_chord_mpt]
  have hi3 : (i : ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
  have hj4 : (j : ℝ) ≤ 4 := by exact_mod_cast (by omega : j ≤ 4)
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set x := ((j : ℝ) - 2) * qstep d - ((i : ℝ) - 3 / 2) * qstep d with hx
  have hb : qstep d / 2 < |x| ∧ |x| ≤ π := by
    rcases (by omega : j + 1 ≤ i ∨ i + 2 ≤ j) with hc | hc
    · have hc' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hc
      have hneg : x < 0 := by rw [hx]; nlinarith
      rw [abs_of_neg hneg, hx]; constructor <;> nlinarith [pi_pos]
    · have hc' : (i : ℝ) + 2 ≤ j := by exact_mod_cast hc
      have hpos : 0 < x := by rw [hx]; nlinarith
      rw [abs_of_pos hpos, hx]; constructor <;> nlinarith [pi_pos]
  have hcos := cos_lt_cos_abs x (qstep d / 2) (by linarith) hb.1 hb.2
  have : 0 < cos (qstep d / 2) - cos x := by linarith
  positivity

/-- Side `i < 4` against a vertex of the other circle. -/
theorem chord_CR (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (i j : ℕ) (hi : i < 4) (hj : j < 5) :
    0 < ⟪cross (qm d i) (qm d (i + 1)), qm d (j + 5)⟫ := by
  obtain ⟨hh0, -, -, hh2⟩ := hrad_mem_of_Icc hlo le_rfl le_rfl hhi
  obtain ⟨hs0, hs4⟩ := qstep_mem d hlo hhi
  have hd0 : 0 < d := by linarith [pi_div_four_lt_dlo, pi_pos]
  have hdπ : d < π := by linarith [dhi_lt_pi_div_three, pi_pos]
  have hsh : 0 < sin (hrad d) := sin_pos_of_pos_of_lt_pi hh0 (by linarith [pi_pos])
  have hch : 0 < cos (hrad d) := cos_pos_of_mem_Ioo ⟨by linarith, hh2⟩
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi hd0 hdπ
  have hsδ : 0 < sin (qstep d / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have e1 : qm d i = mpt (hrad d) (((i : ℝ) - 3 / 2) * qstep d - qstep d / 2) := by
    rw [qm_lt5 d i (by omega), qang_eq]; congr 1; ring
  have e2 : qm d (i + 1) = mpt (hrad d) (((i : ℝ) - 3 / 2) * qstep d + qstep d / 2) := by
    rw [qm_lt5 d (i + 1) (by omega), qang_eq]; congr 1; push_cast; ring
  rw [e1, e2, cross_mpt, real_inner_smul_left, qm_ge5 d j hj, inner_chord_smap_mpt]
  apply mul_pos (by positivity)
  apply cap_real _ _ _ _ _ _ hch hsh.le (by linear_combination cos_sq_add_sin_sq (hrad d))
  rw [chord_norm_sq]
  have hm := onehex_chord_margin d hlo hhi
  have e3 : (π - tanAng d (hrad d)) / 4 = qstep d / 2 := by unfold qstep; ring
  have e4 : 3 * ((π - tanAng d (hrad d)) / 2) / 2 = 3 * qstep d / 2 := by unfold qstep; ring
  rw [e3, e4] at hm
  have hi3 : (i : ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hμ : cos (3 * qstep d / 2) ≤ cos (((i : ℝ) - 3 / 2) * qstep d) := by
    rw [← cos_abs (((i : ℝ) - 3 / 2) * qstep d)]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
    rw [abs_le]; constructor <;> nlinarith
  have := mul_le_mul_of_nonneg_left hμ (le_of_lt (mul_pos hch hsd))
  linarith

/-- The tangent side `4, 5` against the other vertices. -/
theorem tangent_T (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (j : ℕ) (hj : j < 10) (hj4 : j ≠ 4)
    (hj5 : j ≠ 5) :
    0 < ⟪cross (qm d 4) (qm d 5), qm d j⟫ := by
  obtain ⟨hh0, -, -, hh2⟩ := hrad_mem_of_Icc hlo le_rfl le_rfl hhi
  obtain ⟨hs0, hs4⟩ := qstep_mem d hlo hhi
  obtain ⟨hγ1, hγ2, -⟩ := tanAng_facts d hlo hhi
  have htan := tangency_rel d hlo hhi
  have hd0 : 0 < d := by linarith [pi_div_four_lt_dlo, pi_pos]
  have hdπ : d < π := by linarith [dhi_lt_pi_div_three, pi_pos]
  have hcd : cos d ≠ -1 := by
    have := cos_pos_of_mem_Ioo ⟨(by linarith : -(π / 2) < d), (by linarith [dhi_lt_pi_div_three] : d < π / 2)⟩
    linarith
  have hsh : 0 < sin (hrad d) := sin_pos_of_pos_of_lt_pi hh0 (by linarith [pi_pos])
  have hch : 0 < cos (hrad d) := cos_pos_of_mem_Ioo ⟨by linarith, hh2⟩
  have hq : π - tanAng d (hrad d) = 2 * qstep d := by unfold qstep; ring
  have e4 : qm d 4 = mpt (hrad d) (π - tanAng d (hrad d)) := by
    rw [qm_lt5 d 4 (by norm_num), qang_eq, hq]; congr 1; norm_num
  have e5 : qm d 5 = smap d (mpt (hrad d) (-(π - tanAng d (hrad d)))) := by
    show qm d (0 + 5) = _
    rw [qm_ge5 d 0 (by norm_num), qang_eq, hq]; congr 2; norm_num
  set n := nhat (hrad d) (tanAng d (hrad d)) with hn
  have hsn := smap_nhat d (hrad d) (tanAng d (hrad d)) hcd htan
  have h4 : ⟪qm d 4, n⟫ = 0 := by
    rw [real_inner_comm, e4, hn, inner_nhat_mpt, sub_self, cos_zero]; ring
  have h5 : ⟪qm d 5, n⟫ = 0 := by
    rw [e5, inner_smap_left, real_inner_comm, hn, hsn, inner_nhat'_mpt, sub_self, cos_zero]; ring
  have hcr := cross_eq_smul_of_orth (qm d 4) (qm d 5) n (norm_nhat _ _) h4 h5
  have hlam : 0 < ⟪cross (qm d 4) (qm d 5), n⟫ := by
    rw [e4, e5, hn]
    have hγ0 : 0 < tanAng d (hrad d) := by linarith [pi_pos]
    exact tangent_lambda_pos d (hrad d) (tanAng d (hrad d)) ⟨hh0, hh2⟩ ⟨hγ0, hγ2⟩ ⟨hd0, hdπ⟩ htan
  rw [hcr, real_inner_smul_left]
  apply mul_pos hlam
  rcases Nat.lt_or_ge j 4 with hj4' | hj4'
  · rw [qm_lt5 d j (by omega), qang_eq, hn, inner_nhat_mpt, hq]
    have hj3 : (j : ℝ) ≤ 3 := by exact_mod_cast (by omega : j ≤ 3)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hx : ((j : ℝ) - 2) * qstep d - 2 * qstep d < 0 := by nlinarith
    have hc1 := cos_lt_one_of_abs (((j : ℝ) - 2) * qstep d - 2 * qstep d)
      (abs_pos.mpr hx.ne) (by rw [abs_of_neg hx]; nlinarith [pi_pos])
    have : 0 < 1 - cos (((j : ℝ) - 2) * qstep d - 2 * qstep d) := by linarith
    positivity
  · obtain ⟨u, rfl⟩ : ∃ u, j = u + 5 := ⟨j - 5, by omega⟩
    rw [qm_ge5 d u (by omega), ← inner_smap_left, hn, hsn, inner_nhat'_mpt, qang_eq, hq]
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (by omega : 1 ≤ u)
    have hu4 : (u : ℝ) ≤ 4 := by exact_mod_cast (by omega : u ≤ 4)
    have hx : 0 < ((u : ℝ) - 2) * qstep d - -(2 * qstep d) := by nlinarith
    have hc1 := cos_lt_one_of_abs (((u : ℝ) - 2) * qstep d - -(2 * qstep d))
      (abs_pos.mpr hx.ne') (by rw [abs_of_pos hx]; nlinarith [pi_pos])
    have : 0 < 1 - cos (((u : ℝ) - 2) * qstep d - -(2 * qstep d)) := by linarith
    positivity

/-- Strict support of the model polygon at the sides `0, …, 4`. -/
theorem qm_support_lt5 (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (i k : ℕ) (hi : i < 5)
    (h2 : 2 ≤ k) (hk : k < 10) : 0 < ⟪cross (qm d i) (qm d (i + 1)), qm d (i + k)⟫ := by
  rw [qm_mod d (i + k)]
  set t := (i + k) % 10 with ht
  have htl : t < 10 := Nat.mod_lt _ (by norm_num)
  have hti : t ≠ i := by omega
  have hti' : t ≠ i + 1 := by omega
  rcases Nat.lt_or_ge i 4 with hi4 | hi4
  · rcases Nat.lt_or_ge t 5 with ht5 | ht5
    · exact chord_CC d hlo hhi i t hi4 ht5 hti hti'
    · obtain ⟨u, hu⟩ : ∃ u, t = u + 5 := ⟨t - 5, by omega⟩
      rw [hu]
      exact chord_CR d hlo hhi i u hi4 (by omega)
  · have hi4' : i = 4 := by omega
    subst hi4'
    exact tangent_T d hlo hhi t htl hti hti'

theorem qm_isCPoly (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) : IsCPoly 10 (qm d) := by
  refine ⟨by norm_num, norm_qm d, qm_periodic d, fun i k h2 hk => ?_⟩
  have hmod : ∀ n, qm d (i + n) = qm d (i % 10 + n) := fun n => by
    rw [qm_mod d (i + n), qm_mod d (i % 10 + n)]; congr 1; omega
  have h0 := hmod 0
  rw [add_zero, add_zero] at h0
  rw [hmod 1, hmod k, h0]
  set i' := i % 10 with hi'
  have hi'l : i' < 10 := Nat.mod_lt _ (by norm_num)
  rcases Nat.lt_or_ge i' 5 with h5 | h5
  · exact qm_support_lt5 d hlo hhi i' k h5 h2 hk
  · obtain ⟨u, hu⟩ : ∃ u, i' = u + 5 := ⟨i' - 5, by omega⟩
    rw [hu, show u + 5 + 1 = (u + 1) + 5 by ring, show u + 5 + k = (u + k) + 5 by ring,
      qm_add5, qm_add5, qm_add5, triple_smap]
    exact qm_support_lt5 d hlo hhi u k (by omega) h2 hk

/-! ## Perimeter of the model -/

theorem sdist_chord (d : ℝ) (_hlo : dlo ≤ d) (_hhi : d ≤ dhi) (j : ℕ) (hj : j < 4) :
    sdist (qm d j) (qm d (j + 1)) = chordC (hrad d) ((2 * π - 2 * tanAng d (hrad d)) / 4) := by
  have hmm : ∀ h ψ ψ' : ℝ, ⟪mpt h ψ, mpt h ψ'⟫ = cos h ^ 2 + sin h ^ 2 * cos (ψ' - ψ) := by
    intro h ψ ψ'; rw [inner_coords]; simp [mpt, cos_sub]; ring
  unfold sdist chordC
  rw [qm_lt5 d j (by omega), qm_lt5 d (j + 1) (by omega), hmm, qang_eq, qang_eq]
  congr 3
  unfold qstep; push_cast; ring_nf

theorem sdist_tangent (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) :
    sdist (qm d 4) (qm d 5) = tanLen d (hrad d) := by
  obtain ⟨hh0, -, -, hh2⟩ := hrad_mem_of_Icc hlo le_rfl le_rfl hhi
  have htan := tangency_rel d hlo hhi
  have hcd : 0 < 1 + cos d := by
    have := cos_pos_of_mem_Ioo ⟨(by linarith [pi_div_four_lt_dlo, pi_pos] : -(π / 2) < d),
      (by linarith [dhi_lt_pi_div_three] : d < π / 2)⟩
    linarith
  have hch : 0 < cos (hrad d) := cos_pos_of_mem_Ioo ⟨by linarith, hh2⟩
  have hq : π - tanAng d (hrad d) = 2 * qstep d := by unfold qstep; ring
  have e4 : qm d 4 = mpt (hrad d) (π - tanAng d (hrad d)) := by
    rw [qm_lt5 d 4 (by norm_num), qang_eq, hq]; congr 1; norm_num
  have e5 : qm d 5 = smap d (mpt (hrad d) (-(π - tanAng d (hrad d)))) := by
    show qm d (0 + 5) = _
    rw [qm_ge5 d 0 (by norm_num), qang_eq, hq]; congr 2; norm_num
  set h := hrad d with hh
  set γ := tanAng d h with hγ
  have hsq : (cos h * cos γ * (1 + cos d)) ^ 2 = (sin h * sin d) ^ 2 := by rw [htan]; ring
  have h1' : (1 + cos d) * (cos h ^ 2 * cos γ ^ 2 * (1 + cos d) - sin h ^ 2 * (1 - cos d)) = 0 := by
    linear_combination hsq + sin h ^ 2 * sin_sq_add_cos_sq d
  have h1 : cos h ^ 2 * cos γ ^ 2 * (1 + cos d) = sin h ^ 2 * (1 - cos d) := by
    have := (mul_eq_zero.mp h1').resolve_left hcd.ne'
    linarith
  have h3 : sin h * sin d * (cos h * cos γ) = -(sin h ^ 2 * (1 - cos d)) := by
    linear_combination (cos h * cos γ) * htan - h1
  have key : cos h ^ 2 * ⟪qm d 4, qm d 5⟫ = cos d - sin h ^ 2 := by
    rw [e4, e5, inner_coords]
    simp [mpt, smap, cos_pi_sub, sin_pi_sub]
    linear_combination (sin h ^ 2 * cos h ^ 2) * sin_sq_add_cos_sq γ - sin h ^ 2 * h1 +
      (2 * cos h ^ 2) * h3 + (cos d * (cos h ^ 2 + 1 - sin h ^ 2) + sin h ^ 2 -
        2 * sin h ^ 2 * (1 - cos d)) * sin_sq_add_cos_sq h
  unfold sdist tanLen
  congr 1
  rw [eq_div_iff (by positivity), mul_comm, key]

theorem qm_perim (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) :
    perim 10 (qm d) = hexPoly d (hrad d) := by
  have hC := sdist_chord d hlo hhi
  have hT := sdist_tangent d hlo hhi
  have hS : ∀ j, sdist (qm d (j + 5)) (qm d (j + 5 + 1)) = sdist (qm d j) (qm d (j + 1)) := by
    intro j
    rw [show j + 5 + 1 = (j + 1) + 5 by ring, qm_add5, qm_add5, sdist_smap]
  have h9 : sdist (qm d 9) (qm d 10) = tanLen d (hrad d) := by
    have := hS 4
    rw [show (4 : ℕ) + 5 = 9 by rfl, show (4 : ℕ) + 5 + 1 = 10 by rfl] at this
    rw [this, hT]
  simp only [perim, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e5 := hS 0; have e6 := hS 1; have e7 := hS 2; have e8 := hS 3
  norm_num at e5 e6 e7 e8
  rw [e5, e6, e7, e8, h9, hC 0 (by norm_num), hC 1 (by norm_num), hC 2 (by norm_num),
    hC 3 (by norm_num)]
  norm_num at hT ⊢
  rw [hT]
  unfold hexPoly
  ring

/-! ## Transfer to a frame -/

theorem qpoly_eq_map (d : ℝ) (T F C : E3) (O : E3 ≃ₗᵢ[ℝ] E3) (hT : O ex = T) (hFe : O ey = F)
    (hC : O ez = C) (j : ℕ) : qpoly d T F C j = O (qm d j) := by
  simp only [qm, qpoly, cpt]
  split_ifs <;> simp [map_add, map_smul, map_neg, map_sub, hT, hFe, hC]

theorem isCPoly_map {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (O : E3 ≃ₗᵢ[ℝ] E3)
    (hO : ∀ a b, cross (O a) (O b) = O (cross a b)) : IsCPoly m (fun j => O (A j)) := by
  refine ⟨hA.three, fun i => by simp [hA.unit i], fun i => by simp [hA.periodic i],
    fun i k h2 hk => ?_⟩
  simp only [hO, LinearIsometryEquiv.inner_map_map]
  exact hA.support i k h2 hk

theorem perim_map (m : ℕ) (A : ℕ → E3) (O : E3 ≃ₗᵢ[ℝ] E3) :
    perim m (fun j => O (A j)) = perim m A := by
  simp only [perim, sdist, LinearIsometryEquiv.inner_map_map]

/-! ## The polygon in a frame -/

/-- The ten vertex polygon is in cone form. -/
theorem qpoly_isCPoly (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (T F C : E3) (hF : Frame3 T F C) :
    IsCPoly 10 (qpoly d T F C) := by
  obtain ⟨O, hT, hFe, hC, hO⟩ := frame_isometry T F C hF
  have h := isCPoly_map (qm_isCPoly d hlo hhi) O hO
  simpa [← qpoly_eq_map d T F C O hT hFe hC] using h

/-- The perimeter of the ten vertex polygon. -/
theorem qpoly_perim (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) (T F C : E3) (hF : Frame3 T F C) :
    perim 10 (qpoly d T F C) = hexPoly d (hrad d) := by
  obtain ⟨O, hT, hFe, hC, -⟩ := frame_isometry T F C hF
  have h := perim_map 10 (qm d) O
  simp only [← qpoly_eq_map d T F C O hT hFe hC] at h
  rw [show (qpoly d T F C) = fun j => qpoly d T F C j from rfl, h, qm_perim d hlo hhi]

end Tammes15.Geom
