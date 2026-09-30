import Tammes15.Fans.Corners

/-!
# Fans: (T6) and the side corners of (T5)

`T6_corner`: at the corner `A₀` of a hexagon `A₀ … A₅` with the diagonals to
`A₂` and `A₄` inside it, `u₀ = b(u₁) + γ(dist(A₂, A₄); dist(A₀, A₂), dist(A₀, A₄)) + b(u₅)`, the
base angles `b` of (T1). `T5_side_corner`: at `A₂` of a pentagon with the diagonal to `A₀` inside
the corner, `u₂ = b(u₁) + γ(dist(A₀, A₃); dist(A₀, A₂), d)`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- (T6): the fan of a hexagon from `A₀` to the diagonals `A₀A₂`, `A₀A₄`. -/
theorem T6_corner (d : ℝ) (hd : 0 < d ∧ d < π / 2) (A₀ A₁ A₂ A₄ A₅ : E3) (h₀ : ‖A₀‖ = 1)
    (h₁ : ‖A₁‖ = 1) (h₂ : ‖A₂‖ = 1) (h₄ : ‖A₄‖ = 1) (h₅ : ‖A₅‖ = 1) (h₀₁ : sdist A₀ A₁ = d)
    (h₁₂ : sdist A₁ A₂ = d) (h₄₅ : sdist A₄ A₅ = d) (h₅₀ : sdist A₅ A₀ = d)
    (hu₁ : 0 < angle (tdir A₁ A₀) (tdir A₁ A₂)) (hu₅ : 0 < angle (tdir A₅ A₄) (tdir A₅ A₀))
    (he : 0 < sdist A₀ A₂ ∧ sdist A₀ A₂ < π) (hf : 0 < sdist A₀ A₄ ∧ sdist A₀ A₄ < π)
    (l₁ m₁ l₂ m₂ : ℝ) (hl₁ : 0 ≤ l₁) (hm₁ : 0 ≤ m₁) (hl₂ : 0 ≤ l₂) (hm₂ : 0 ≤ m₂)
    (hc₁ : tdir A₀ A₂ = l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₅)
    (hc₂ : tdir A₀ A₄ = l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₅) :
    angle (tdir A₀ A₁) (tdir A₀ A₅) = bangle d (angle (tdir A₁ A₀) (tdir A₁ A₂)) +
      gam (sdist A₂ A₄) (sdist A₀ A₂) (sdist A₀ A₄) +
        bangle d (angle (tdir A₅ A₄) (tdir A₅ A₀)) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases he with ⟨he_pos, he_lt⟩
  rcases hf with ⟨hf_pos, hf_lt⟩
  have hd_sin_pos : sin d > 0 := Real.sin_pos_of_pos_of_lt_pi hd_pos (by linarith)
  have h01_comm : sdist A₁ A₀ = d := by
    rw [← sdist_comm A₀ A₁, h₀₁]
  have h45_comm : sdist A₅ A₄ = d := by
    rw [← sdist_comm A₄ A₅, h₄₅]
  have h50_comm : sdist A₅ A₀ = d := h₅₀
  have h_tdir_A0A1_ne_zero : tdir A₀ A₁ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₁‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₁‖ = sin (sdist A₀ A₁) := tdir_norm A₀ A₁ h₀ h₁
    rw [hnorm'] at hnorm
    rw [h₀₁] at hnorm
    linarith
  have h_tdir_A0A5_ne_zero : tdir A₀ A₅ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₅‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₅‖ = sin (sdist A₀ A₅) := tdir_norm A₀ A₅ h₀ h₅
    rw [hnorm'] at hnorm
    rw [← sdist_comm A₅ A₀, h₅₀] at hnorm
    linarith
  have h_tdir_A0A2_ne_zero : tdir A₀ A₂ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₂‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₂‖ = sin (sdist A₀ A₂) := tdir_norm A₀ A₂ h₀ h₂
    rw [hnorm'] at hnorm
    have hpos : sin (sdist A₀ A₂) > 0 := Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
    linarith
  have h_tdir_A0A4_ne_zero : tdir A₀ A₄ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₄‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₄‖ = sin (sdist A₀ A₄) := tdir_norm A₀ A₄ h₀ h₄
    rw [hnorm'] at hnorm
    have hpos : sin (sdist A₀ A₄) > 0 := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt
    linarith
  have h_angle_add₁ : angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₅) = angle (tdir A₀ A₁) (tdir A₀ A₅) := by
    calc
      angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₅)
          = angle (tdir A₀ A₁) (l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₅) + angle (l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₅) (tdir A₀ A₅) := by rw [hc₁]
      _ = angle (tdir A₀ A₁) (tdir A₀ A₅) :=
        angle_add_of_cone (tdir A₀ A₁) (tdir A₀ A₅) h_tdir_A0A1_ne_zero h_tdir_A0A5_ne_zero l₁ m₁ hl₁ hm₁ (by rw [← hc₁]; exact h_tdir_A0A2_ne_zero)
  have h_angle_add₂ : angle (tdir A₀ A₂) (tdir A₀ A₄) + angle (tdir A₀ A₄) (tdir A₀ A₅) = angle (tdir A₀ A₂) (tdir A₀ A₅) := by
    calc
      angle (tdir A₀ A₂) (tdir A₀ A₄) + angle (tdir A₀ A₄) (tdir A₀ A₅)
          = angle (tdir A₀ A₂) (l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₅) + angle (l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₅) (tdir A₀ A₅) := by rw [hc₂]
      _ = angle (tdir A₀ A₂) (tdir A₀ A₅) :=
        angle_add_of_cone (tdir A₀ A₂) (tdir A₀ A₅) h_tdir_A0A2_ne_zero h_tdir_A0A5_ne_zero l₂ m₂ hl₂ hm₂ (by rw [← hc₂]; exact h_tdir_A0A4_ne_zero)
  have h_sum : angle (tdir A₀ A₁) (tdir A₀ A₅) = angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₄) + angle (tdir A₀ A₄) (tdir A₀ A₅) := by
    linarith
  rw [h_sum]
  have h_gam : angle (tdir A₀ A₂) (tdir A₀ A₄) = gam (sdist A₂ A₄) (sdist A₀ A₂) (sdist A₀ A₄) := by
    rw [angle_tdir_eq_gam A₀ A₂ A₄ h₀ h₂ h₄ ⟨he_pos, he_lt⟩ ⟨hf_pos, hf_lt⟩]
  rw [h_gam]
  have h_bangle₁ : bangle d (angle (tdir A₁ A₀) (tdir A₁ A₂)) = angle (tdir A₀ A₁) (tdir A₀ A₂) := by
    rw [T1_isosceles_angle d ⟨hd_pos, hd_lt⟩ A₁ A₀ A₂ h₁ h₀ h₂ h01_comm h₁₂ hu₁]
  rw [h_bangle₁]
  have hu₅' : 0 < angle (tdir A₅ A₀) (tdir A₅ A₄) := by
    rw [← angle_comm (tdir A₅ A₄) (tdir A₅ A₀)]
    exact hu₅
  have htemp := T1_isosceles_angle d ⟨hd_pos, hd_lt⟩ A₅ A₀ A₄ h₅ h₀ h₄ h50_comm h45_comm hu₅'
  have h_bangle₂ : bangle d (angle (tdir A₅ A₄) (tdir A₅ A₀)) = angle (tdir A₀ A₄) (tdir A₀ A₅) := by
    calc
      bangle d (angle (tdir A₅ A₄) (tdir A₅ A₀))
          = bangle d (angle (tdir A₅ A₀) (tdir A₅ A₄)) := by rw [angle_comm (tdir A₅ A₄) (tdir A₅ A₀)]
      _ = angle (tdir A₀ A₅) (tdir A₀ A₄) := by rw [← htemp]
      _ = angle (tdir A₀ A₄) (tdir A₀ A₅) := by rw [angle_comm (tdir A₀ A₅) (tdir A₀ A₄)]
  rw [h_bangle₂]

/-- (T5), the corner two steps along: `u₂ = b(u₁) + γ(f; e, d)` with `e = dist(A₀, A₂)`,
`f = dist(A₀, A₃)`. -/
theorem T5_side_corner (d : ℝ) (hd : 0 < d ∧ d < π / 2) (A₀ A₁ A₂ A₃ : E3) (h₀ : ‖A₀‖ = 1)
    (h₁ : ‖A₁‖ = 1) (h₂ : ‖A₂‖ = 1) (h₃ : ‖A₃‖ = 1) (h₀₁ : sdist A₀ A₁ = d)
    (h₁₂ : sdist A₁ A₂ = d) (h₂₃ : sdist A₂ A₃ = d) (hu₁ : 0 < angle (tdir A₁ A₂) (tdir A₁ A₀))
    (he : 0 < sdist A₀ A₂ ∧ sdist A₀ A₂ < π) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hc : tdir A₂ A₀ = l • tdir A₂ A₁ + m • tdir A₂ A₃) :
    angle (tdir A₂ A₁) (tdir A₂ A₃) = bangle d (angle (tdir A₁ A₂) (tdir A₁ A₀)) +
      gam (sdist A₀ A₃) (sdist A₀ A₂) d := by
  have hpos_tdir1 : tdir A₂ A₁ ≠ 0 := by
    have hnorm : ‖tdir A₂ A₁‖ = sin d := by
      rw [tdir_norm A₂ A₁ h₂ h₁, sdist_comm A₂ A₁, h₁₂]
    have hsin_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 (by linarith [hd.2, pi_pos])
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  have hpos_tdir3 : tdir A₂ A₃ ≠ 0 := by
    have hnorm : ‖tdir A₂ A₃‖ = sin d := by
      rw [tdir_norm A₂ A₃ h₂ h₃, h₂₃]
    have hsin_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hd.1 (by linarith [hd.2, pi_pos])
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  have hpos_sum : l • tdir A₂ A₁ + m • tdir A₂ A₃ ≠ 0 := by
    rw [← hc]
    have hnorm : ‖tdir A₂ A₀‖ = sin (sdist A₂ A₀) := tdir_norm A₂ A₀ h₂ h₀
    have hpos_sdist : 0 < sdist A₂ A₀ := by rw [sdist_comm A₂ A₀]; exact he.1
    have hsin_pos : 0 < sin (sdist A₂ A₀) :=
      sin_pos_of_pos_of_lt_pi hpos_sdist (by rw [sdist_comm A₂ A₀]; exact he.2)
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  have hsum := angle_add_of_cone (tdir A₂ A₁) (tdir A₂ A₃) hpos_tdir1 hpos_tdir3 l m hl hm hpos_sum
  rw [← hc] at hsum
  have hfirst : angle (tdir A₂ A₁) (tdir A₂ A₀) = bangle d (angle (tdir A₁ A₂) (tdir A₁ A₀)) := by
    have hAC : sdist A₁ A₀ = d := by rw [sdist_comm A₁ A₀, h₀₁]
    have h := T1_isosceles_angle d hd A₁ A₂ A₀ h₁ h₂ h₀ h₁₂ hAC hu₁
    -- h : angle (tdir A₁ A₂) (tdir A₁ A₀) = bangle d (angle (tdir A₂ A₁) (tdir A₂ A₀))
    -- We need angle (tdir A₂ A₁) (tdir A₂ A₀) = bangle d (angle (tdir A₁ A₂) (tdir A₁ A₀))
    rw [angle_comm (tdir A₂ A₁) (tdir A₂ A₀), angle_comm (tdir A₁ A₂) (tdir A₁ A₀)] at h
    -- Now h : angle (tdir A₂ A₀) (tdir A₂ A₁) = bangle d (angle (tdir A₁ A₀) (tdir A₁ A₂))
    -- But we need the RHS to be bangle d (angle (tdir A₁ A₂) (tdir A₁ A₀))
    -- angle_comm on the RHS: angle (tdir A₁ A₀) (tdir A₁ A₂) = angle (tdir A₁ A₂) (tdir A₁ A₀)
    rw [angle_comm (tdir A₁ A₀) (tdir A₁ A₂)] at h
    -- Now h : angle (tdir A₂ A₀) (tdir A₂ A₁) = bangle d (angle (tdir A₁ A₂) (tdir A₁ A₀))
    -- We need angle (tdir A₂ A₁) (tdir A₂ A₀), not angle (tdir A₂ A₀) (tdir A₂ A₁)
    -- Use angle_comm again
    rw [angle_comm (tdir A₂ A₁) (tdir A₂ A₀)]
    exact h
  have hsecond : angle (tdir A₂ A₀) (tdir A₂ A₃) = gam (sdist A₀ A₃) (sdist A₀ A₂) d := by
    have hAB : 0 < sdist A₂ A₀ ∧ sdist A₂ A₀ < π := by
      constructor
      · rw [sdist_comm A₂ A₀]; exact he.1
      · rw [sdist_comm A₂ A₀]; exact he.2
    have hAC : 0 < sdist A₂ A₃ ∧ sdist A₂ A₃ < π := by
      constructor
      · rw [h₂₃]; exact hd.1
      · rw [h₂₃]; linarith [hd.2, pi_pos]
    rw [angle_tdir_eq_gam A₂ A₀ A₃ h₂ h₀ h₃ hAB hAC, sdist_comm A₂ A₀, h₂₃]
  rw [hfirst, hsecond] at hsum
  rw [← hsum]

end Tammes15
