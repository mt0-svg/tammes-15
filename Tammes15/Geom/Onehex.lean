import Tammes15.Geom.Crofton
import Tammes15.Geom.Qpoly

/-!
# Proposition onehex: two far points never share a hexagonal face

Let `A` be a hexagon in cone form with sides `d ∈ [dlo, dhi]`, and `r₁`, `r₂` two points inside it,
at distance at least `d` from each other and from every vertex. By Lemma disc (`disc_side`) both
lie at distance at least `h = h(d)` from the great circle of every side, and so does the point `c`
of the arc `r₁ r₂` at distance `d` from `r₁` (`onehex_inner`); the discs of radius `h` about `r₁`
and `c` lie in the closed face (`inClosed_of_disc`). The ten vertex polygon `qpoly` has five
vertices on the outer arc of each of the two circles, from tangency point to tangency point, so its
vertices lie in the closed face; it is in cone form (`qpoly_isCPoly`) with perimeter
`hexPoly d h` (`qpoly_perim`). Perimeter monotonicity (`perim_mono`) gives `hexPoly d h ≤ 6 d`,
against `margin_onehex_poly`.

The polygon is built in a right handed orthonormal frame `(T, F, C)` with `T` the tangent at `C`
pointing away from `R = cos d • C - sin d • T` (code/lean/geom/onehex_q.gp): the `j`-th vertex on
the circle about `C` is `cos h • C + sin h • (cos ψ_j • T + sin ψ_j • F)` with
`ψ_j = -(π - γ) + j s`, `γ = tanAng d h`, `s = (π - γ) / 2`, and likewise about `R` in the frame
`(-(cos d • T + sin d • C), -F, R)`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- A frame at `C` whose first axis points away from `R`. -/
theorem exists_frame_away (C R : E3) (hC : ‖C‖ = 1) (hR : ‖R‖ = 1) (d : ℝ)
    (_hd : 0 < d ∧ d < π) (hCR : sdist C R = d) :
    ∃ T F : E3, Frame3 T F C ∧ R = cos d • C - sin d • T := by
  obtain ⟨u, hu, hCu, hRu⟩ := exists_tangent_unit C R hC hR
  rw [hCR] at hRu
  have hT : ‖-u‖ = 1 := by rw [norm_neg, hu]
  have hCT : ⟪C, -u⟫ = 0 := by rw [inner_neg_right, hCu, neg_zero]
  have hF := frame_of_orth C (-u) hC hT hCT
  refine ⟨-u, cross C (-u), ⟨hT, hF.nC, hC, hF.FC, by rw [real_inner_comm]; exact hCT,
    by rw [real_inner_comm]; exact hF.TC, ?_⟩, ?_⟩
  · rw [triple_cycle, triple_cycle, real_inner_self_eq_norm_sq, hF.nC]; norm_num
  · rw [hRu, smul_neg, sub_neg_eq_add]

/-- Every vertex lies on one of the two circles. -/
theorem qpoly_near (d : ℝ) (hd : 0 < d ∧ d < π / 2) (T F C : E3) (hF : Frame3 T F C) (j : ℕ) :
    sdist C (qpoly d T F C j) ≤ hrad d ∨
      sdist (cos d • C - sin d • T) (qpoly d T F C j) ≤ hrad d := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hrad_nonneg : 0 ≤ hrad d := Real.arccos_nonneg _
  have hrad_le_pi : hrad d ≤ π := Real.arccos_le_pi _
  by_cases hj : j % 10 < 5
  · -- case j % 10 < 5: qpoly uses T, F, C
    have hqpoly : qpoly d T F C j = cpt (hrad d) (qang d (j % 10)) T F C := by
      dsimp [qpoly]
      rw [ite_eq_left hj]
    rw [hqpoly]
    dsimp [sdist, cpt]
    have h_inner : ⟪C, cos (hrad d) • C + sin (hrad d) • (cos (qang d (j % 10)) • T + sin (qang d (j % 10)) • F)⟫ = cos (hrad d) := by
      calc
        ⟪C, cos (hrad d) • C + sin (hrad d) • (cos (qang d (j % 10)) • T + sin (qang d (j % 10)) • F)⟫
            = cos (hrad d) * ⟪C, C⟫ + sin (hrad d) * (cos (qang d (j % 10)) * ⟪C, T⟫ + sin (qang d (j % 10)) * ⟪C, F⟫) := by
          simp [inner_add_right, inner_smul_right, mul_add]
        _ = cos (hrad d) * ⟪C, C⟫ + sin (hrad d) * (cos (qang d (j % 10)) * 0 + sin (qang d (j % 10)) * 0) := by
          rw [← real_inner_comm C T, hF.TC, ← real_inner_comm C F, hF.FC]
        _ = cos (hrad d) * ⟪C, C⟫ := by ring
        _ = cos (hrad d) * (‖C‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
        _ = cos (hrad d) * (1 ^ 2) := by rw [hF.nC]
        _ = cos (hrad d) := by norm_num
    rw [h_inner]
    rw [Real.arccos_cos hrad_nonneg hrad_le_pi]
    exact Or.inl (le_refl _)
  · -- case j % 10 ≥ 5: qpoly uses T', F', R
    have hqpoly : qpoly d T F C j = cpt (hrad d) (qang d (j % 10 - 5)) (-(cos d • T + sin d • C)) (-F) (cos d • C - sin d • T) := by
      dsimp [qpoly]
      rw [ite_eq_right (by omega)]
    rw [hqpoly]
    dsimp [sdist, cpt]
    set R := cos d • C - sin d • T with hR
    set T' := -(cos d • T + sin d • C) with hT'
    set F' := -F with hF'
    have hR_norm_sq : ‖R‖ ^ 2 = 1 := by
      dsimp [R]
      rw [← real_inner_self_eq_norm_sq]
      rw [inner_sub_left (cos d • C) (sin d • T) (cos d • C - sin d • T)]
      rw [inner_sub_right (cos d • C) (cos d • C) (sin d • T)]
      rw [inner_sub_right (sin d • T) (cos d • C) (sin d • T)]
      simp [inner_smul_left, inner_smul_right]
      have hcos_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin_pos : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith)
      simp [norm_smul, abs_of_pos hcos_pos, abs_of_pos hsin_pos, hF.nC, hF.nT]
      rw [← real_inner_comm C T, hF.TC]
      ring_nf
      rw [Real.cos_sq_add_sin_sq]
    have hR_norm : ‖R‖ = 1 := by
      have hpos : 0 ≤ ‖R‖ := norm_nonneg _
      have hsq : ‖R‖ ^ 2 = 1 ^ 2 := by rw [hR_norm_sq, one_pow]
      nlinarith
    have hRT' : ⟪R, T'⟫ = 0 := by
      dsimp [R, T']
      simp [inner_neg_right, inner_add_right, inner_smul_right, inner_sub_left, inner_smul_left]
      rw [hF.nC, hF.nT, ← real_inner_comm C T, hF.TC]
      ring
    have hRF' : ⟪R, F'⟫ = 0 := by
      dsimp [R, F']
      rw [inner_neg_right]
      rw [inner_sub_left (cos d • C) (sin d • T) F]
      simp [inner_smul_left, ← real_inner_comm C F, hF.FC, hF.TF]
    have h_inner : ⟪R, cos (hrad d) • R + sin (hrad d) • (cos (qang d (j % 10 - 5)) • T' + sin (qang d (j % 10 - 5)) • F')⟫ = cos (hrad d) := by
      calc
        ⟪R, cos (hrad d) • R + sin (hrad d) • (cos (qang d (j % 10 - 5)) • T' + sin (qang d (j % 10 - 5)) • F')⟫
            = cos (hrad d) * ⟪R, R⟫ + sin (hrad d) * (cos (qang d (j % 10 - 5)) * ⟪R, T'⟫ + sin (qang d (j % 10 - 5)) * ⟪R, F'⟫) := by
          simp [inner_add_right, inner_smul_right, mul_add]
        _ = cos (hrad d) * ⟪R, R⟫ + sin (hrad d) * (cos (qang d (j % 10 - 5)) * 0 + sin (qang d (j % 10 - 5)) * 0) := by
          rw [hRT', hRF']
        _ = cos (hrad d) * ⟪R, R⟫ := by ring
        _ = cos (hrad d) * (‖R‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
        _ = cos (hrad d) * 1 := by rw [hR_norm_sq]
        _ = cos (hrad d) := by ring
    rw [h_inner]
    rw [Real.arccos_cos hrad_nonneg hrad_le_pi]
    exact Or.inr (le_refl _)

/-- The point of the arc from `r₁` to `r₂` at distance `d` from `r₁` is a unit vector. -/
theorem slerp_unit (d : ℝ) (r₁ r₂ : E3) (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1)
    (hd : 0 < d ∧ d ≤ sdist r₁ r₂ ∧ sdist r₁ r₂ < π) :
    ‖(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂‖ = 1 := by
  rcases hd with ⟨hdpos, hdle, hdlt⟩
  set l := sdist r₁ r₂ with hl
  have hlpos : 0 < l := by linarith
  have hcos : cos l = ⟪r₁, r₂⟫ := cos_sdist r₁ r₂ h₁ h₂
  have hsinpos : 0 < sin l := Real.sin_pos_of_pos_of_lt_pi hlpos hdlt
  have hsinpos' : sin l ≠ 0 := by linarith
  have hnum : sin (l - d) ^ 2 + sin d ^ 2 + 2 * sin (l - d) * sin d * cos l = sin l ^ 2 := by
    rw [Real.sin_sub l d]
    nlinarith [Real.sin_sq_add_cos_sq l, Real.sin_sq_add_cos_sq d]
  have hnorm_sq : ‖(sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂‖ ^ 2 = 1 := by
    calc
      ‖(sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂‖ ^ 2
          = ‖(sin (l - d) / sin l) • r₁‖ ^ 2 + 2 * inner ℝ ((sin (l - d) / sin l) • r₁) ((sin d / sin l) • r₂) + ‖(sin d / sin l) • r₂‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = ((sin (l - d) / sin l) ^ 2) * ‖r₁‖ ^ 2 + 2 * (((sin (l - d) / sin l) * (sin d / sin l)) * inner ℝ r₁ r₂) + ((sin d / sin l) ^ 2) * ‖r₂‖ ^ 2 := by
        have hpos_sin_ld : 0 ≤ sin (l - d) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        have hpos_sin_d : 0 ≤ sin d :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [norm_smul, norm_smul, inner_smul_left, inner_smul_right]
        simp [abs_of_nonneg hpos_sin_ld, abs_of_nonneg hpos_sin_d, abs_of_pos hsinpos, h₁, h₂]
        ring
      _ = ((sin (l - d) / sin l) ^ 2) * 1 + 2 * (((sin (l - d) / sin l) * (sin d / sin l)) * cos l) + ((sin d / sin l) ^ 2) * 1 := by
        simp [h₁, h₂, hcos]
      _ = ((sin (l - d) ^ 2 + sin d ^ 2 + 2 * sin (l - d) * sin d * cos l) / (sin l ^ 2)) := by
        field_simp [hsinpos']
        ring
      _ = (sin l ^ 2 / sin l ^ 2) := by rw [hnum]
      _ = 1 := by field_simp [hsinpos']
  have hnorm_nonneg : 0 ≤ ‖(sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂‖ := norm_nonneg _
  nlinarith

theorem slerp_sdist (d : ℝ) (r₁ r₂ : E3) (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1)
    (hd : 0 < d ∧ d ≤ sdist r₁ r₂ ∧ sdist r₁ r₂ < π) :
    sdist r₁ ((sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂) = d := by
  rcases hd with ⟨hdpos, hdle, hdlt⟩
  set l := sdist r₁ r₂ with hl
  have h_inner_range : -1 ≤ ⟪r₁, r₂⟫ ∧ ⟪r₁, r₂⟫ ≤ 1 := by
    have h_abs := abs_real_inner_le_norm r₁ r₂
    have h_norm_prod : ‖r₁‖ * ‖r₂‖ = 1 := by rw [h₁, h₂, mul_one]
    have h_abs' : |⟪r₁, r₂⟫| ≤ 1 := by linarith
    exact abs_le.mp h_abs'
  have hcosl : cos l = ⟪r₁, r₂⟫ := by
    rw [hl, Tammes15.sdist]
    exact Real.cos_arccos h_inner_range.1 h_inner_range.2
  have hsinl_pos : 0 < sin l := by
    have hl_pos : 0 < l := by linarith
    have hl_mem : l ∈ Set.Ioo (0 : ℝ) π := ⟨hl_pos, hdlt⟩
    exact Real.sin_pos_of_mem_Ioo hl_mem
  have h_slerp_inner : ⟪r₁, (sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂⟫ = cos d := by
    calc
      ⟪r₁, (sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂⟫
          = ⟪r₁, (sin (l - d) / sin l) • r₁⟫ + ⟪r₁, (sin d / sin l) • r₂⟫ := by
            rw [inner_add_right]
      _ = (sin (l - d) / sin l) * ⟪r₁, r₁⟫ + (sin d / sin l) * ⟪r₁, r₂⟫ := by
            simp [inner_smul_right]
      _ = (sin (l - d) / sin l) * ‖r₁‖ ^ 2 + (sin d / sin l) * cos l := by
            rw [real_inner_self_eq_norm_sq, hcosl]
      _ = (sin (l - d) / sin l) * 1 ^ 2 + (sin d / sin l) * cos l := by rw [h₁]
      _ = (sin (l - d) / sin l) + (sin d / sin l) * cos l := by ring
      _ = (sin (l - d) + sin d * cos l) / sin l := by ring
      _ = (sin l * cos d - cos l * sin d + sin d * cos l) / sin l := by rw [Real.sin_sub l d]
      _ = (sin l * cos d) / sin l := by ring
      _ = cos d := by
            field_simp [ne_of_gt hsinl_pos]
  rw [hl, Tammes15.sdist, h_slerp_inner]
  exact Real.arccos_cos (by linarith) (by linarith)

/-- The disc of radius `h(d)` about a point satisfying the disc inequality at every side lies in
the closed face. -/
theorem inClosed_of_disc (d : ℝ) (hd : 0 < d ∧ d < π / 2) {m : ℕ} {A : ℕ → E3}
    (hA : IsCPoly m A) (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (c : E3) (hc : ‖c‖ = 1)
    (hdisc : ∀ i, sin d * sin (hrad d) ≤ ⟪cross (A i) (A (i + 1)), c⟫) (y : E3) (hy : ‖y‖ = 1)
    (hcy : sdist c y ≤ hrad d) : InClosed A y := by
  intro i
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 (by linarith [pi_pos])
  have hn : ‖cross (A i) (A (i + 1))‖ = sin d := by
    rw [norm_cross_unit _ _ (hA.unit i) (hA.unit (i + 1)), hside i]
  set n := (sin d)⁻¹ • cross (A i) (A (i + 1)) with hn_def
  have hn1 : ‖n‖ = 1 := by
    rw [hn_def, norm_smul, hn, norm_inv, Real.norm_of_nonneg hsd.le, inv_mul_cancel₀ hsd.ne']
  have hcn : sin (hrad d) ≤ ⟪c, n⟫ := by
    rw [hn_def, real_inner_smul_right, real_inner_comm, le_inv_mul_iff₀ hsd]
    exact hdisc i
  have hb := hrad_bounds d hd
  have h := cap_in_hemisphere (hrad d) ⟨by linarith, by linarith⟩ c n y hc hn1 hy hcn hcy
  rw [hn_def, real_inner_smul_right] at h
  rw [real_inner_comm]
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hsd)).mp h

/-- The disc inequality passes to the point `c` of the arc between two points satisfying it. -/
theorem disc_slerp (d : ℝ) (hd : 0 < d ∧ d < π / 2) (a b : E3) (_ha : ‖a‖ = 1) (_hb : ‖b‖ = 1)
    (_hab : sdist a b = d) (r₁ r₂ : E3) (hl : d ≤ sdist r₁ r₂ ∧ sdist r₁ r₂ < π)
    (h₁ : sin d * sin (hrad d) ≤ ⟪cross a b, r₁⟫) (h₂ : sin d * sin (hrad d) ≤ ⟪cross a b, r₂⟫) :
    sin d * sin (hrad d) ≤ ⟪cross a b, (sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂⟫ := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hl with ⟨hle, hlt⟩
  have hsinpos : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  set n := (sin d)⁻¹ • cross a b with hn
  have hn1 : sin (hrad d) ≤ ⟪r₁, n⟫ := by
    calc
      sin (hrad d) = (sin d)⁻¹ * (sin d * sin (hrad d)) := by field_simp [hsinpos.ne.symm]
      _ ≤ (sin d)⁻¹ * ⟪cross a b, r₁⟫ := by gcongr
      _ = (sin d)⁻¹ * ⟪r₁, cross a b⟫ := by rw [real_inner_comm]
      _ = ⟪r₁, (sin d)⁻¹ • cross a b⟫ := by rw [real_inner_smul_right]
      _ = ⟪r₁, n⟫ := by rw [hn]
  have hn2 : sin (hrad d) ≤ ⟪r₂, n⟫ := by
    calc
      sin (hrad d) = (sin d)⁻¹ * (sin d * sin (hrad d)) := by field_simp [hsinpos.ne.symm]
      _ ≤ (sin d)⁻¹ * ⟪cross a b, r₂⟫ := by gcongr
      _ = (sin d)⁻¹ * ⟪r₂, cross a b⟫ := by rw [real_inner_comm]
      _ = ⟪r₂, (sin d)⁻¹ • cross a b⟫ := by rw [real_inner_smul_right]
      _ = ⟪r₂, n⟫ := by rw [hn]
  have hsin_hrad_nonneg : 0 ≤ sin (hrad d) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hcomb := onehex_inner d (sdist r₁ r₂) (hrad d) ⟨hdpos, hle, hlt⟩ hsin_hrad_nonneg r₁ r₂ n hn1 hn2
  calc
    sin d * sin (hrad d) ≤ sin d * ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, n⟫ := by gcongr
    _ = sin d * ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, (sin d)⁻¹ • cross a b⟫ := by rw [hn]
    _ = sin d * ((sin d)⁻¹ * ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, cross a b⟫) := by rw [real_inner_smul_right]
    _ = (sin d * (sin d)⁻¹) * ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, cross a b⟫ := by ring
    _ = 1 * ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, cross a b⟫ := by field_simp [hsinpos.ne.symm]
    _ = ⟪(sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂, cross a b⟫ := by simp
    _ = ⟪cross a b, (sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ +
      (sin d / sin (sdist r₁ r₂)) • r₂⟫ := by rw [real_inner_comm]

/-- Two points inside a convex hexagon are not antipodal. -/
theorem sdist_lt_pi_of_inside {m : ℕ} {A : ℕ → E3} (_hA : IsCPoly m A) (r₁ r₂ : E3)
    (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1) (hin₁ : Inside A r₁) (hin₂ : Inside A r₂) :
    sdist r₁ r₂ < π := by
  by_contra! h
  -- h : π ≤ sdist r₁ r₂
  have h_le : sdist r₁ r₂ ≤ π := by
    simpa [sdist] using Real.arccos_le_pi ⟪r₁, r₂⟫
  have h_eq : sdist r₁ r₂ = π := le_antisymm h_le h
  have h_arccos_eq : Real.arccos ⟪r₁, r₂⟫ = π := by
    simpa [sdist] using h_eq
  have h_inner_le : ⟪r₁, r₂⟫ ≤ -1 :=
    (Real.arccos_eq_pi (x := ⟪r₁, r₂⟫)).mp h_arccos_eq
  have h_norm_sq : ‖r₁ + r₂‖ ^ 2 = 2 + 2 * ⟪r₁, r₂⟫ := by
    calc
      ‖r₁ + r₂‖ ^ 2 = ‖r₁‖ ^ 2 + 2 * ⟪r₁, r₂⟫ + ‖r₂‖ ^ 2 := by
        simpa using norm_add_sq_real r₁ r₂
      _ = 1 ^ 2 + 2 * ⟪r₁, r₂⟫ + 1 ^ 2 := by simp [h₁, h₂]
      _ = 2 + 2 * ⟪r₁, r₂⟫ := by ring
  have h_norm_sq_nonpos : ‖r₁ + r₂‖ ^ 2 ≤ 0 := by
    linarith
  have h_norm_sq_zero : ‖r₁ + r₂‖ ^ 2 = 0 := by
    linarith [sq_nonneg (‖r₁ + r₂‖)]
  have h_norm_zero : ‖r₁ + r₂‖ = 0 := by
    nlinarith [sq_nonneg (‖r₁ + r₂‖), h_norm_sq_zero]
  have h_sum_zero : r₁ + r₂ = 0 :=
    (norm_eq_zero (a := r₁ + r₂)).mp h_norm_zero
  have h_neg : r₂ = -r₁ :=
    (neg_eq_of_add_eq_zero_right h_sum_zero).symm
  have hpos₁ : 0 < ⟪cross (A 0) (A 1), r₁⟫ := hin₁ 0
  have hpos₂ : 0 < ⟪cross (A 0) (A 1), r₂⟫ := hin₂ 0
  have hpos₂' : 0 < ⟪cross (A 0) (A 1), -r₁⟫ := by
    simpa [h_neg] using hpos₂
  have h_neg_inner : ⟪cross (A 0) (A 1), -r₁⟫ = -⟪cross (A 0) (A 1), r₁⟫ := by
    exact inner_neg_right (cross (A 0) (A 1)) r₁
  rw [h_neg_inner] at hpos₂'
  linarith

/-- Proposition onehex. -/
theorem onehex (d : ℝ) (hlo : dlo ≤ d) (hhi : d ≤ dhi) {A : ℕ → E3} (hA : IsCPoly 6 A)
    (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (r₁ r₂ : E3) (h₁ : ‖r₁‖ = 1) (h₂ : ‖r₂‖ = 1)
    (hin₁ : Inside A r₁) (hin₂ : Inside A r₂) (hfar₁ : ∀ i, d ≤ sdist r₁ (A i))
    (hfar₂ : ∀ i, d ≤ sdist r₂ (A i)) (h12 : d ≤ sdist r₁ r₂) : False := by
  have hd : 0 < d ∧ d < π / 2 := ⟨by linarith [pi_div_four_lt_dlo, pi_pos],
    by linarith [dhi_lt_pi_div_three, pi_pos]⟩
  have hl : d ≤ sdist r₁ r₂ ∧ sdist r₁ r₂ < π := ⟨h12, sdist_lt_pi_of_inside hA r₁ r₂ h₁ h₂ hin₁ hin₂⟩
  set c := (sin (sdist r₁ r₂ - d) / sin (sdist r₁ r₂)) • r₁ + (sin d / sin (sdist r₁ r₂)) • r₂
    with hc_def
  have hc : ‖c‖ = 1 := slerp_unit d r₁ r₂ h₁ h₂ ⟨hd.1, hl.1, hl.2⟩
  have hr₁c : sdist r₁ c = d := slerp_sdist d r₁ r₂ h₁ h₂ ⟨hd.1, hl.1, hl.2⟩
  have hdisc₁ := disc_side d hd hA hside r₁ h₁ hin₁ hfar₁
  have hdisc₂ := disc_side d hd hA hside r₂ h₂ hin₂ hfar₂
  have hdiscc : ∀ i, sin d * sin (hrad d) ≤ ⟪cross (A i) (A (i + 1)), c⟫ := fun i =>
    disc_slerp d hd (A i) (A (i + 1)) (hA.unit i) (hA.unit (i + 1)) (hside i) r₁ r₂ hl
      (hdisc₁ i) (hdisc₂ i)
  obtain ⟨T, F, hF, hcT⟩ := exists_frame_away r₁ c h₁ hc d ⟨hd.1, by linarith [pi_pos]⟩ hr₁c
  have hQ := qpoly_isCPoly d hlo hhi T F r₁ hF
  have hQA : ∀ j, InClosed A (qpoly d T F r₁ j) := by
    intro j
    rcases qpoly_near d hd T F r₁ hF j with h | h
    · exact inClosed_of_disc d hd hA hside r₁ h₁ hdisc₁ _ (hQ.unit j) h
    · rw [← hcT] at h
      exact inClosed_of_disc d hd hA hside c hc hdiscc _ (hQ.unit j) h
  have hmono := perim_mono hA hQ hQA
  rw [qpoly_perim d hlo hhi T F r₁ hF] at hmono
  have hperim : perim 6 A = 6 * d := by
    simp only [perim, hside, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have := margin_onehex_poly d ⟨hlo, hhi⟩
  linarith

end Tammes15.Geom
