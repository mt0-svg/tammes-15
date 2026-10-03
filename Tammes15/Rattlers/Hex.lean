import Tammes15.Rattlers.Basic
import Tammes15.Trigrows.Sdist

/-!
# Proposition 4.6 and Corollary 4.7: point steps and the count


`arcPt_dist_left`, `arcPt_dist_right`: the parameter of `arcPt` is the distance
from `v` (so points of an edge are within `d/2` of an endpoint); `cap_in_hemisphere`: a disc of
radius `h` about `r` lies in the closed hemisphere of pole `n` when `⟪r, n⟫ ≥ sin h`;
`onehex_inner`: the point `c` of Proposition 4.6 keeps that bound; `k_le_three`: the count of
Corollary 4.7.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

theorem sdist_triangle (x y z : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    sdist x z ≤ sdist x y + sdist y z := by
  have hxz := sdist_eq_angle x z hx hz
  have hxy := sdist_eq_angle x y hx hy
  have hyz := sdist_eq_angle y z hy hz
  rw [hxz, hxy, hyz]
  exact InnerProductGeometry.angle_le_angle_add_angle x y z

theorem inner_arcPt_left (d : ℝ) (hd : 0 < d ∧ d < π) (v w : E3) (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫ = cos d) (t : ℝ) : ⟪arcPt d v w t, v⟫ = cos t := by
  rcases hd with ⟨hdpos, hdlt⟩
  have hsin_pos : sin d ≠ 0 := by
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hdpos hdlt)
  unfold arcPt
  simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, hv, hvw,
    real_inner_comm v w, RCLike.conj_to_real]
  field_simp [hsin_pos]
  rw [Real.sin_sub d t]
  ring

theorem arcPt_dist_left (d : ℝ) (hd : 0 < d ∧ d < π) (v w : E3) (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫ = cos d) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ π) : sdist (arcPt d v w t) v = t := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases ht with ⟨htpos, htle⟩
  unfold sdist
  have hinner : ⟪arcPt d v w t, v⟫ = cos t := inner_arcPt_left d ⟨hdpos, hdlt⟩ v w hv hvw t
  rw [hinner]
  exact Real.arccos_cos htpos htle

theorem arcPt_dist_right (d : ℝ) (hd : 0 < d ∧ d < π) (v w : E3) (hw : ‖w‖ = 1)
    (hvw : ⟪v, w⟫ = cos d) (t : ℝ) (ht : 0 ≤ d - t ∧ d - t ≤ π) :
    sdist (arcPt d v w t) w = d - t := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases ht with ⟨ht0, ht1⟩
  have hsinpos : sin d ≠ 0 := by
    have h := sin_pos_of_pos_of_lt_pi hdpos hdlt
    linarith
  have hinner : ⟪w, w⟫ = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℝ) (E := E3) w
    simpa [hw] using this
  have hcalc : ⟪arcPt d v w t, w⟫ = cos (d - t) := by
    unfold arcPt
    simp_rw [inner_add_left, inner_smul_left, hvw, hinner]
    simp
    field_simp [hsinpos]
    have := Real.sin_sub d (d - t)
    rw [sub_sub_cancel] at this
    linarith
  unfold sdist
  rw [hcalc]
  exact Real.arccos_cos ht0 ht1

theorem cap_in_hemisphere (h : ℝ) (hh : 0 ≤ h ∧ h ≤ π / 2) (r n x : E3) (hr : ‖r‖ = 1)
    (hn : ‖n‖ = 1) (hx : ‖x‖ = 1) (hrn : sin h ≤ ⟪r, n⟫) (hrx : sdist r x ≤ h) : 0 ≤ ⟪x, n⟫ := by
  rcases hh with ⟨hh0, hh1⟩
  set a := sdist r n with ha
  have ha_cos : cos a = ⟪r, n⟫ := cos_sdist r n hr hn
  have ha_nonneg : 0 ≤ a := by
    rw [ha, sdist]
    exact Real.arccos_nonneg _
  have ha_le_pi : a ≤ π := by
    rw [ha, sdist]
    exact Real.arccos_le_pi _
  have h_sin_eq : sin h = cos (π / 2 - h) := by
    calc
      sin h = sin (π / 2 - (π / 2 - h)) := by ring_nf
      _ = cos (π / 2 - h) := by rw [Real.sin_pi_div_two_sub]
  have h_cos_le : cos (π / 2 - h) ≤ cos a := by
    rw [← h_sin_eq]
    -- from hrn: sin h ≤ ⟪r, n⟫ and ha_cos: cos a = ⟪r, n⟫
    linarith [hrn, ha_cos]
  have h_pi_sub_nonneg : 0 ≤ π / 2 - h := by linarith
  have h_pi_sub_le_pi : π / 2 - h ≤ π := by linarith [pi_pos]
  have ha_le_pi_sub : a ≤ π / 2 - h := by
    have h_arccos_le : arccos (cos a) ≤ arccos (cos (π / 2 - h)) :=
      Real.arccos_le_arccos h_cos_le
    have h_arccos_a : arccos (cos a) = a := Real.arccos_cos ha_nonneg ha_le_pi
    have h_arccos_pi_sub : arccos (cos (π / 2 - h)) = π / 2 - h :=
      Real.arccos_cos h_pi_sub_nonneg h_pi_sub_le_pi
    linarith
  have h_sdist_symm : sdist r x = sdist x r := by
    simp [sdist, real_inner_comm]
  have h_sdist_triangle : sdist x n ≤ sdist x r + sdist r n :=
    sdist_triangle x r n hx hr hn
  have h_sdist_xn_le_pi_sub_two : sdist x n ≤ π / 2 := by
    calc
      sdist x n ≤ sdist x r + sdist r n := h_sdist_triangle
      _ = sdist r x + a := by rw [h_sdist_symm, ha]
      _ ≤ h + a := by nlinarith
      _ ≤ h + (π / 2 - h) := by nlinarith
      _ = π / 2 := by ring
  have h_sdist_xn_nonneg : 0 ≤ sdist x n := by
    rw [sdist]
    exact Real.arccos_nonneg _
  have h_cos_sdist_xn : cos (sdist x n) = ⟪x, n⟫ := cos_sdist x n hx hn
  rw [← h_cos_sdist_xn]
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · linarith
  · linarith

/-- Proposition 4.6: the point `c` of `[r₁ r₂]` at distance `d` from `r₁` keeps the bound. -/
theorem onehex_inner (d l h : ℝ) (hd : 0 < d ∧ d ≤ l ∧ l < π) (hsh : 0 ≤ sin h) (r₁ r₂ n : E3)
    (h₁ : sin h ≤ ⟪r₁, n⟫) (h₂ : sin h ≤ ⟪r₂, n⟫) :
    sin h ≤ ⟪(sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂, n⟫ := by
  rcases hd with ⟨hdpos, hdle, hlltpi⟩
  have hpos_l : 0 < l := by linarith
  have hpos_sin_l : 0 < sin l := sin_pos_of_pos_of_lt_pi hpos_l hlltpi
  have hsin_nd_nonneg : 0 ≤ sin (l - d) := by
    have h_nonneg : 0 ≤ l - d := by linarith
    have h_le_pi : l - d ≤ π := by linarith
    exact sin_nonneg_of_nonneg_of_le_pi h_nonneg h_le_pi
  have hsin_d_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  have hcoeff1_nonneg : 0 ≤ sin (l - d) / sin l := div_nonneg hsin_nd_nonneg (by linarith)
  have hcoeff2_nonneg : 0 ≤ sin d / sin l := div_nonneg (by linarith) (by linarith)
  have hinner_eq : ⟪(sin (l - d) / sin l) • r₁ + (sin d / sin l) • r₂, n⟫ =
      (sin (l - d) / sin l) * ⟪r₁, n⟫ + (sin d / sin l) * ⟪r₂, n⟫ := by
    simp [inner_add_left, inner_smul_left]
  rw [hinner_eq]
  have h1 : (sin (l - d) / sin l) * ⟪r₁, n⟫ ≥ (sin (l - d) / sin l) * sin h :=
    mul_le_mul_of_nonneg_left h₁ hcoeff1_nonneg
  have h2 : (sin d / sin l) * ⟪r₂, n⟫ ≥ (sin d / sin l) * sin h :=
    mul_le_mul_of_nonneg_left h₂ hcoeff2_nonneg
  have hsum : (sin (l - d) / sin l) * ⟪r₁, n⟫ + (sin d / sin l) * ⟪r₂, n⟫ ≥
      (sin (l - d) / sin l) * sin h + (sin d / sin l) * sin h := by linarith
  have hfactor : (sin (l - d) / sin l) * sin h + (sin d / sin l) * sin h = sin h * ((sin (l - d) + sin d) / sin l) := by
    ring
  rw [hfactor] at hsum
  have hratio : (sin (l - d) + sin d) / sin l = cos (l / 2 - d) / cos (l / 2) := by
    have h := sin_sub_add_sin l d ⟨hpos_l, hlltpi⟩
    simpa using h
  rw [hratio] at hsum
  have hcos_ratio_ge_one : 1 ≤ cos (l / 2 - d) / cos (l / 2) := by
    have hpos_cos_half : 0 < cos (l / 2) := by
      have hmem : l / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
        constructor <;> linarith
      exact Real.cos_pos_of_mem_Ioo hmem
    have h_cos_ge : cos (l / 2) ≤ cos (l / 2 - d) := by
      by_cases h_nonneg : 0 ≤ l / 2 - d
      · have h_le : l / 2 - d ≤ l / 2 := by linarith
        exact Real.cos_le_cos_of_nonneg_of_le_pi h_nonneg (by linarith) h_le
      · have h_nonneg' : 0 ≤ d - l / 2 := by linarith
        have h_le : d - l / 2 ≤ l / 2 := by linarith
        have h_cos_even : cos (l / 2 - d) = cos (d - l / 2) := by
          rw [show l / 2 - d = -(d - l / 2) by ring, Real.cos_neg]
        rw [h_cos_even]
        exact Real.cos_le_cos_of_nonneg_of_le_pi h_nonneg' (by linarith) h_le
    exact ((one_le_div hpos_cos_half).mpr h_cos_ge)
  have hfinal : sin h ≤ sin h * (cos (l / 2 - d) / cos (l / 2)) := by
    have := mul_le_mul_of_nonneg_left hcos_ratio_ge_one hsh
    simpa [mul_one] using this
  linarith

/-- Corollary 4.7: the count. -/
theorem k_le_three (k n E F : ℕ) (hn : n + k = 15) (h1 : 3 * F + 3 * k ≤ 2 * E)
    (h2 : F + n = E + 2) (h3 : 3 * n ≤ 2 * E) : k ≤ 3 := by
  omega

end Tammes15
