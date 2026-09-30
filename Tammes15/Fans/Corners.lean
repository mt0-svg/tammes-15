import Tammes15.Fans.Cone
import Tammes15.Trigrows.Points

/-!
# Fans: corner decompositions of (T5) and (T8)

The diagonals from a corner lie inside it (convexity), stated as the cone
conditions `hcone`, `hc₁`, `hc₂` on the tangent directions; the corner is then the sum of the
angles of the fan.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

/-- (T8): at a corner `A` with neighbours `B`, `C` at distance `d` and a point `X` inside the
corner, `u = γ(dist(B, X); d, r) + γ(dist(X, C); r, d)` with `r = dist(A, X)`. -/
theorem T8_corner (d : ℝ) (hd : 0 < d ∧ d < π) (A B C X : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1)
    (hC : ‖C‖ = 1) (hX : ‖X‖ = 1) (hAB : sdist A B = d) (hAC : sdist A C = d)
    (hAX : 0 < sdist A X ∧ sdist A X < π) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hcone : tdir A X = l • tdir A B + m • tdir A C) :
    angle (tdir A B) (tdir A C) = gam (sdist B X) d (sdist A X) + gam (sdist X C) (sdist A X) d := by
  have hAB_lt : 0 < sdist A B ∧ sdist A B < π := by
    rw [hAB]
    exact hd
  have hAC_lt : 0 < sdist A C ∧ sdist A C < π := by
    rw [hAC]
    exact hd
  have hsin_pos : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hd.1 hd.2
  have hsin_ne_zero : sin d ≠ 0 := by linarith
  have htdir_AB_ne_zero : tdir A B ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A B‖ = 0 := by simp [hzero]
    rw [tdir_norm A B hA hB, hAB] at hnorm
    exact hsin_ne_zero hnorm
  have htdir_AC_ne_zero : tdir A C ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A C‖ = 0 := by simp [hzero]
    rw [tdir_norm A C hA hC, hAC] at hnorm
    exact hsin_ne_zero hnorm
  have hAXpos : 0 < sdist A X := hAX.1
  have hAXlt : sdist A X < π := hAX.2
  have hsin_AX_pos : 0 < sin (sdist A X) := Real.sin_pos_of_pos_of_lt_pi hAXpos hAXlt
  have hsin_AX_ne_zero : sin (sdist A X) ≠ 0 := by linarith
  have htdir_AX_ne_zero : tdir A X ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A X‖ = 0 := by simp [hzero]
    rw [tdir_norm A X hA hX] at hnorm
    linarith
  have hsum_ne_zero : l • tdir A B + m • tdir A C ≠ 0 := by
    rw [← hcone]
    exact htdir_AX_ne_zero
  have h_angle_sum := angle_add_of_cone (tdir A B) (tdir A C) htdir_AB_ne_zero htdir_AC_ne_zero l m hl hm hsum_ne_zero
  rw [← hcone] at h_angle_sum
  have h1 := angle_tdir_eq_gam A B X hA hB hX hAB_lt hAX
  have h2 := angle_tdir_eq_gam A X C hA hX hC hAX hAC_lt
  rw [h1, h2] at h_angle_sum
  rw [hAB, hAC] at h_angle_sum
  exact h_angle_sum.symm

/-- (T5): the fan of a pentagon `A₀ ... A₄` from `A₀`: `u₀ = b₁ + γ(d; e, f) + b₃`. -/
theorem T5_corner (d : ℝ) (hd : 0 < d ∧ d < π / 2) (A₀ A₁ A₂ A₃ A₄ : E3) (h₀ : ‖A₀‖ = 1)
    (h₁ : ‖A₁‖ = 1) (h₂ : ‖A₂‖ = 1) (h₃ : ‖A₃‖ = 1) (h₄ : ‖A₄‖ = 1) (h₀₁ : sdist A₀ A₁ = d)
    (h₁₂ : sdist A₁ A₂ = d) (h₂₃ : sdist A₂ A₃ = d) (h₃₄ : sdist A₃ A₄ = d)
    (h₄₀ : sdist A₄ A₀ = d) (hu₁ : 0 < angle (tdir A₁ A₀) (tdir A₁ A₂))
    (hu₄ : 0 < angle (tdir A₄ A₃) (tdir A₄ A₀)) (he : 0 < sdist A₀ A₂ ∧ sdist A₀ A₂ < π)
    (hf : 0 < sdist A₀ A₃ ∧ sdist A₀ A₃ < π) (l₁ m₁ l₂ m₂ : ℝ) (hl₁ : 0 ≤ l₁) (hm₁ : 0 ≤ m₁)
    (hl₂ : 0 ≤ l₂) (hm₂ : 0 ≤ m₂) (hc₁ : tdir A₀ A₂ = l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₄)
    (hc₂ : tdir A₀ A₃ = l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₄) :
    angle (tdir A₀ A₁) (tdir A₀ A₄) = bangle d (angle (tdir A₁ A₀) (tdir A₁ A₂)) +
      gam d (sdist A₀ A₂) (sdist A₀ A₃) + bangle d (angle (tdir A₄ A₃) (tdir A₄ A₀)) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  rcases he with ⟨he_pos, he_lt⟩
  rcases hf with ⟨hf_pos, hf_lt⟩
  have hd_sin_pos : sin d > 0 := Real.sin_pos_of_pos_of_lt_pi hd_pos (by linarith)
  have h01_comm : sdist A₁ A₀ = d := by
    rw [← sdist_comm A₀ A₁, h₀₁]
  have h40_comm : sdist A₄ A₃ = d := by
    rw [← sdist_comm A₃ A₄, h₃₄]
  have h_tdir_A0A1_ne_zero : tdir A₀ A₁ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₁‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₁‖ = sin (sdist A₀ A₁) := tdir_norm A₀ A₁ h₀ h₁
    rw [hnorm'] at hnorm
    rw [h₀₁] at hnorm
    linarith [hd_sin_pos, hnorm]
  have h_tdir_A0A4_ne_zero : tdir A₀ A₄ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₄‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₄‖ = sin (sdist A₀ A₄) := tdir_norm A₀ A₄ h₀ h₄
    rw [hnorm'] at hnorm
    rw [← sdist_comm A₄ A₀, h₄₀] at hnorm
    linarith [hd_sin_pos, hnorm]
  have h_tdir_A0A2_ne_zero : tdir A₀ A₂ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₂‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₂‖ = sin (sdist A₀ A₂) := tdir_norm A₀ A₂ h₀ h₂
    rw [hnorm'] at hnorm
    have hpos : sin (sdist A₀ A₂) > 0 := Real.sin_pos_of_pos_of_lt_pi he_pos he_lt
    linarith
  have h_tdir_A0A3_ne_zero : tdir A₀ A₃ ≠ 0 := by
    intro hzero
    have hnorm : ‖tdir A₀ A₃‖ = 0 := by simpa [hzero] using norm_zero
    have hnorm' : ‖tdir A₀ A₃‖ = sin (sdist A₀ A₃) := tdir_norm A₀ A₃ h₀ h₃
    rw [hnorm'] at hnorm
    have hpos : sin (sdist A₀ A₃) > 0 := Real.sin_pos_of_pos_of_lt_pi hf_pos hf_lt
    linarith
  have h_angle_add₁ : angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₄) = angle (tdir A₀ A₁) (tdir A₀ A₄) := by
    calc
      angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₄)
          = angle (tdir A₀ A₁) (l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₄) + angle (l₁ • tdir A₀ A₁ + m₁ • tdir A₀ A₄) (tdir A₀ A₄) := by rw [hc₁]
      _ = angle (tdir A₀ A₁) (tdir A₀ A₄) :=
        angle_add_of_cone (tdir A₀ A₁) (tdir A₀ A₄) h_tdir_A0A1_ne_zero h_tdir_A0A4_ne_zero l₁ m₁ hl₁ hm₁ (by rw [← hc₁]; exact h_tdir_A0A2_ne_zero)
  have h_angle_add₂ : angle (tdir A₀ A₂) (tdir A₀ A₃) + angle (tdir A₀ A₃) (tdir A₀ A₄) = angle (tdir A₀ A₂) (tdir A₀ A₄) := by
    calc
      angle (tdir A₀ A₂) (tdir A₀ A₃) + angle (tdir A₀ A₃) (tdir A₀ A₄)
          = angle (tdir A₀ A₂) (l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₄) + angle (l₂ • tdir A₀ A₂ + m₂ • tdir A₀ A₄) (tdir A₀ A₄) := by rw [hc₂]
      _ = angle (tdir A₀ A₂) (tdir A₀ A₄) :=
        angle_add_of_cone (tdir A₀ A₂) (tdir A₀ A₄) h_tdir_A0A2_ne_zero h_tdir_A0A4_ne_zero l₂ m₂ hl₂ hm₂ (by rw [← hc₂]; exact h_tdir_A0A3_ne_zero)
  have h_sum : angle (tdir A₀ A₁) (tdir A₀ A₄) = angle (tdir A₀ A₁) (tdir A₀ A₂) + angle (tdir A₀ A₂) (tdir A₀ A₃) + angle (tdir A₀ A₃) (tdir A₀ A₄) := by
    linarith
  rw [h_sum]
  have h_gam : angle (tdir A₀ A₂) (tdir A₀ A₃) = gam d (sdist A₀ A₂) (sdist A₀ A₃) := by
    rw [angle_tdir_eq_gam A₀ A₂ A₃ h₀ h₂ h₃ ⟨he_pos, he_lt⟩ ⟨hf_pos, hf_lt⟩, h₂₃]
  rw [h_gam]
  have h_bangle₁ : bangle d (angle (tdir A₁ A₀) (tdir A₁ A₂)) = angle (tdir A₀ A₁) (tdir A₀ A₂) := by
    rw [T1_isosceles_angle d ⟨hd_pos, hd_lt⟩ A₁ A₀ A₂ h₁ h₀ h₂ h01_comm h₁₂ hu₁]
  rw [h_bangle₁]
  have hu₄' : 0 < angle (tdir A₄ A₀) (tdir A₄ A₃) := by
    rw [← angle_comm (tdir A₄ A₃) (tdir A₄ A₀)]
    exact hu₄
  have htemp := T1_isosceles_angle d ⟨hd_pos, hd_lt⟩ A₄ A₀ A₃ h₄ h₀ h₃ h₄₀ h40_comm hu₄'
  have h_bangle₂ : bangle d (angle (tdir A₄ A₃) (tdir A₄ A₀)) = angle (tdir A₀ A₃) (tdir A₀ A₄) := by
    calc
      bangle d (angle (tdir A₄ A₃) (tdir A₄ A₀))
          = bangle d (angle (tdir A₄ A₀) (tdir A₄ A₃)) := by rw [angle_comm (tdir A₄ A₃) (tdir A₄ A₀)]
      _ = angle (tdir A₀ A₄) (tdir A₀ A₃) := by rw [← htemp]
      _ = angle (tdir A₀ A₃) (tdir A₀ A₄) := by rw [angle_comm (tdir A₀ A₄) (tdir A₀ A₃)]
  rw [h_bangle₂]

end Tammes15
