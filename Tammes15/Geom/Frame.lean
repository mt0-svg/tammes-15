import Tammes15.Geom.Basic
import Tammes15.Local41.Chain

/-!
# Right handed orthonormal frames of `E3`

A right handed orthonormal frame `(T, F, C)` is the image of the coordinate frame `(ex, ey, ez)`
under a linear isometry `O` of determinant one, which commutes with cross products
(`frame_isometry`, from `cross_isometry`). Every unit vector `a` starts such a frame, with any unit
`u ⊥ a` second (`frame_of_orth`), and a unit `b` lies in the plane of `a` and a unit tangent `u`
at `a`, `b = cos (sdist a b) • a + sin (sdist a b) • u` (`exists_tangent_unit`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- A right handed orthonormal frame. -/
structure Frame3 (T F C : E3) : Prop where
  nT : ‖T‖ = 1
  nF : ‖F‖ = 1
  nC : ‖C‖ = 1
  TF : ⟪T, F⟫ = 0
  TC : ⟪T, C⟫ = 0
  FC : ⟪F, C⟫ = 0
  orient : ⟪cross T F, C⟫ = 1

/-- The coordinate vectors. -/
noncomputable def ex : E3 := !₂[1, 0, 0]
noncomputable def ey : E3 := !₂[0, 1, 0]
noncomputable def ez : E3 := !₂[0, 0, 1]

theorem norm_eq_one_of_sq {v : E3} (h : ‖v‖ ^ 2 = 1) : ‖v‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- A unit vector orthogonal to a unit vector. -/
theorem exists_orth_unit (a : E3) : ∃ u : E3, ‖u‖ = 1 ∧ ⟪a, u⟫ = 0 := by
  by_cases h : a 0 = 0 ∧ a 1 = 0
  · refine ⟨ey, norm_eq_one_of_sq ?_, ?_⟩
    · rw [← real_inner_self_eq_norm_sq, inner_coords]; simp [ey]
    · rw [inner_coords]; simp [ey, h.2]
  · have ht : 0 < a 0 ^ 2 + a 1 ^ 2 := by
      rcases not_and_or.mp h with h0 | h1
      · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; positivity
      · have := pow_pos (abs_pos.mpr h1) 2; rw [sq_abs] at this; positivity
    set r := √(a 0 ^ 2 + a 1 ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr ht
    have hr2 : r ^ 2 = a 0 ^ 2 + a 1 ^ 2 := Real.sq_sqrt ht.le
    refine ⟨!₂[-(a 1) / r, a 0 / r, 0], norm_eq_one_of_sq ?_, ?_⟩
    · rw [← real_inner_self_eq_norm_sq, inner_coords]; simp
      field_simp
      linarith
    · rw [inner_coords]; simp
      field_simp
      ring

/-- A unit vector and a unit vector orthogonal to it start a right handed frame. -/
theorem frame_of_orth (a u : E3) (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (hau : ⟪a, u⟫ = 0) :
    Frame3 a u (cross a u) := by
  have hc2 : ‖cross a u‖ ^ 2 = 1 := by rw [norm_cross_sq, ha, hu, hau]; norm_num
  refine ⟨ha, hu, norm_eq_one_of_sq hc2, hau, inner_cross_self a u, inner_cross_right_self a u, ?_⟩
  rw [real_inner_self_eq_norm_sq, hc2]

/-- A unit vector `b` in the plane of a unit `a` and a unit tangent at `a`. -/
theorem exists_tangent_unit (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ u : E3, ‖u‖ = 1 ∧ ⟪a, u⟫ = 0 ∧ b = cos (sdist a b) • a + sin (sdist a b) • u := by
  have hc : cos (sdist a b) = ⟪a, b⟫ := cos_sdist a b ha hb
  have hs0 : 0 ≤ sin (sdist a b) := sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _)
    (arccos_le_pi _)
  set c := cos (sdist a b) with hc_def
  set s := sin (sdist a b) with hs_def
  have hcs : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  set v := b - c • a with hv
  have hav : ⟪a, v⟫ = 0 := by
    rw [hv, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha, ← hc]; ring
  have hv2 : ‖v‖ ^ 2 = s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hv, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb, real_inner_comm a b, ← hc]
    linear_combination -hcs
  rcases hs0.lt_or_eq with hs | hs
  · refine ⟨s⁻¹ • v, norm_eq_one_of_sq ?_, ?_, ?_⟩
    · rw [norm_smul, mul_pow, hv2, norm_inv, Real.norm_of_nonneg hs.le, inv_pow,
        inv_mul_cancel₀ (pow_pos hs 2).ne']
    · rw [real_inner_smul_right, hav, mul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, hv, add_sub_cancel]
  · obtain ⟨u, hu, hau⟩ := exists_orth_unit a
    refine ⟨u, hu, hau, ?_⟩
    have hv0 : v = 0 := by
      rw [← hs] at hv2
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by rw [hv2]; ring))
    rw [← hs, zero_smul, add_zero]
    rw [hv] at hv0
    exact sub_eq_zero.mp hv0

/-- The coordinate map of a frame. -/
noncomputable def frameMap (T F C : E3) : E3 →ₗ[ℝ] E3 where
  toFun a := a 0 • T + a 1 • F + a 2 • C
  map_add' a b := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' r a := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

/-- The rotation carrying the coordinate frame to a right handed orthonormal frame. -/
theorem frame_isometry (T F C : E3) (hF : Frame3 T F C) :
    ∃ O : E3 ≃ₗᵢ[ℝ] E3, O ex = T ∧ O ey = F ∧ O ez = C ∧
      ∀ a b, cross (O a) (O b) = O (cross a b) := by
  have hFT : ⟪F, T⟫ = 0 := by rw [real_inner_comm]; exact hF.TF
  have hCT : ⟪C, T⟫ = 0 := by rw [real_inner_comm]; exact hF.TC
  have hCF : ⟪C, F⟫ = 0 := by rw [real_inner_comm]; exact hF.FC
  have hTT : ⟪T, T⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hF.nT]; norm_num
  have hFF : ⟪F, F⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hF.nF]; norm_num
  have hCC : ⟪C, C⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hF.nC]; norm_num
  have hinner : ∀ a b, ⟪frameMap T F C a, frameMap T F C b⟫ = ⟪a, b⟫ := by
    intro a b
    simp only [frameMap, LinearMap.coe_mk, AddHom.coe_mk, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hTT, hFF, hCC, hF.TF, hF.TC, hF.FC, hFT, hCT,
      hCF, inner_coords]
    ring
  set O : E3 ≃ₗᵢ[ℝ] E3 := (LinearMap.isometryOfInner (frameMap T F C) hinner).toLinearIsometryEquiv
    rfl with hO
  have hOv : ∀ v, O v = v 0 • T + v 1 • F + v 2 • C := fun v => rfl
  have hex : O ex = T := by rw [hOv]; simp [ex]
  have hey : O ey = F := by rw [hOv]; simp [ey]
  have hez : O ez = C := by rw [hOv]; simp [ez]
  have hdet : LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
    have h1 : ⟪cross ex ey, ez⟫ = 1 := by
      rw [inner_coords, cross_coords]; simp [ex, ey, ez]
    have h := congrArg (fun v => ⟪v, O ez⟫) (cross_isometry O ex ey)
    rw [real_inner_smul_left, LinearIsometryEquiv.inner_map_map, hex, hey, hez, hF.orient, h1,
      mul_one] at h
    exact h.symm
  refine ⟨O, hex, hey, hez, fun a b => ?_⟩
  rw [cross_isometry, hdet, one_smul]

end Tammes15.Geom
