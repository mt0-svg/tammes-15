import Mathlib

/-!
# Angle additivity inside a cone

The fan relations (T5), (T6) and the wheel (T8) add angles at a corner: a
direction in the closed cone of two others splits their angle.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

theorem angle_add_of_cone {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hc : l • a + m • b ≠ 0) :
    angle a (l • a + m • b) + angle (l • a + m • b) b = angle a b := by
  set c := l • a + m • b with hc_def
  have hc_ne_zero : c ≠ 0 := hc
  by_cases hl_pos : 0 < l
  · by_cases hm_pos : 0 < m
    · -- l > 0, m > 0
      have hmb_ne_zero : m • b ≠ 0 := smul_ne_zero hm_pos.ne' hb
      have h_eq := angle_eq_angle_add_add_angle_add (l • a) hmb_ne_zero
      rw [← hc_def] at h_eq
      rw [angle_smul_left_of_pos a c hl_pos, angle_smul_left_of_pos b c hm_pos] at h_eq
      rw [angle_smul_left_of_pos a (m • b) hl_pos, angle_smul_right_of_pos a b hm_pos] at h_eq
      rw [← angle_comm c b] at h_eq
      exact h_eq.symm
    · -- l > 0, m = 0
      have hm_zero : m = 0 := by linarith
      rw [hm_zero, zero_smul, add_zero] at hc_def
      rw [hc_def]
      rw [angle_smul_right_of_pos a a hl_pos, angle_self ha, angle_smul_left_of_pos a b hl_pos]
      simp
  · -- l = 0
    have hl_zero : l = 0 := by linarith
    rw [hl_zero, zero_smul, zero_add] at hc_def
    rw [hc_def]
    by_cases hm_pos : 0 < m
    · rw [angle_smul_right_of_pos a b hm_pos, angle_smul_left_of_pos b b hm_pos, angle_self hb]
      simp
    · have hm_zero : m = 0 := by linarith
      rw [hm_zero, zero_smul] at hc_def
      exact absurd hc_def hc_ne_zero

end Tammes15
