import Tammes15.TwoConn.Excess

/-!
# The triangle lemma of the Fejes Tóth bound

Paper, Section 8, Lemmas 8.1 and 8.2. A
spherical triangle `p q r` (positively oriented) with sides at least `a` (`⟪·, ·⟫ ≤ c = cos a`) and
circumradius at most `a` (a unit `n` with `⟪n, p⟫ = ⟪n, q⟫ = ⟪n, r⟫ = k ≥ c`) has angle sum at least
that of the equilateral triangle of side `a`, `π + 2 arg (1 + 3c + i (1 - c) √(1 + 2c))`, for
`1/2 ≤ c < 1` (`fejesToth_triangle`, Lemma 8.2). The proof is algebraic: the corners are arguments
(`sphereVertexAngle_eq_arg`, Lemma 8.1), their sum is `π + 2 arg (1 + x + y + z + iD)`
(`angle_sum_arg`, Lemma 8.1), the circumradius condition is a polynomial inequality
(`circumcentre_identity`), and the comparison of arguments (`arg_le_arg_of_mul_le`)
reduces to the certificate `tri_poly` (proof of Lemma 8.2).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification (sphereVertexAngle)
open Tammes15.Vendor.EM8.SquareAntiprismVerification (crossVec spherical_triangle_excess_positive
  unit_triple_gram_identity)

namespace Tammes15.FejesToth

/-- The triangle lemma in polynomial form (the certificate in the proof of Lemma 8.2). -/
theorem tri_poly (m a b g : ℝ) (hm0 : 0 < m) (hm : m ≤ 1 / 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hK : 0 ≤ (2 - m) * (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2) - 2 * ((1 + a) * (1 + b) * (1 + g))) :
    0 ≤ (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2 - 2 * m * ((1 + a) * (1 + b) * (1 + g)))
        * (4 - 3 * m) ^ 2 - (3 - 2 * m) * (4 - m * ((1 + a) + (1 + b) + (1 + g))) ^ 2 := by
  set p1 := a + b + g with hp1
  set p2 := a * b + b * g + g * a with hp2
  set p3 := a * b * g with hp3
  set K := (2 - m) * (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2) - 2 * ((1 + a) * (1 + b) * (1 + g)) with hKdef
  have h1 : 0 ≤ p1 := by positivity
  have h2 : 0 ≤ p2 := by positivity
  have h3 : 0 ≤ p3 := by positivity
  have hmac : 9 * p3 ≤ p1 * p2 := by
    nlinarith [mul_nonneg ha (sq_nonneg (b - g)), mul_nonneg hb (sq_nonneg (g - a)),
      mul_nonneg hg (sq_nonneg (a - b))]
  -- the goal is `F`; two exact rewritings of `F / 2`
  have eA : (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2 - 2 * m * ((1 + a) * (1 + b) * (1 + g)))
        * (4 - 3 * m) ^ 2 - (3 - 2 * m) * (4 - m * ((1 + a) + (1 + b) + (1 + g))) ^ 2
      = 2 * ((2 - m) ^ 2 * p1 * ((4 - 3 * m) - (2 - m) * p1)
          + (4 - 3 * m) ^ 2 * ((2 - m) * p2 - m * p3)) := by
    simp only [hp1, hp2, hp3]; ring
  have eB : (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2 - 2 * m * ((1 + a) * (1 + b) * (1 + g)))
        * (4 - 3 * m) ^ 2 - (3 - 2 * m) * (4 - m * ((1 + a) + (1 + b) + (1 + g))) ^ 2
      = 2 * ((2 - m) ^ 2 * K + (2 - m) ^ 2 * ((2 - m) * p1 - (4 - 3 * m))
          + (2 - m) * (5 * m ^ 2 - 10 * m + 4) * p2 + (-9 * m ^ 3 + 26 * m ^ 2 - 24 * m + 8) * p3) := by
    simp only [hp1, hp2, hp3, hKdef]; ring
  by_cases hcase : (2 - m) * p1 ≤ 4 - 3 * m
  · rw [eA]
    have hA1 : 0 ≤ (2 - m) ^ 2 * p1 * ((4 - 3 * m) - (2 - m) * p1) := by
      have : 0 ≤ (4 - 3 * m) - (2 - m) * p1 := by linarith
      positivity
    have hmp : m * p1 ≤ 9 * (2 - m) := by nlinarith
    have hA2 : 0 ≤ (2 - m) * p2 - m * p3 := by nlinarith
    have : 0 ≤ (4 - 3 * m) ^ 2 * ((2 - m) * p2 - m * p3) := by positivity
    linarith
  · push Not at hcase
    rw [eB]
    have hc2 : 0 ≤ 5 * m ^ 2 - 10 * m + 4 := by nlinarith
    have hc3 : 0 ≤ -9 * m ^ 3 + 26 * m ^ 2 - 24 * m + 8 := by nlinarith [sq_nonneg m, mul_pos hm0 hm0]
    have t1 : 0 ≤ (2 - m) ^ 2 * K := by positivity
    have t2 : 0 ≤ (2 - m) ^ 2 * ((2 - m) * p1 - (4 - 3 * m)) := by
      have : 0 ≤ (2 - m) * p1 - (4 - 3 * m) := by linarith
      positivity
    have t3 : 0 ≤ (2 - m) * (5 * m ^ 2 - 10 * m + 4) * p2 := by
      have : 0 ≤ 2 - m := by linarith
      positivity
    have t4 : 0 ≤ (-9 * m ^ 3 + 26 * m ^ 2 - 24 * m + 8) * p3 := by positivity
    linarith

/-- The triangle lemma in the inner products `x = ⟪q, r⟫`, `y = ⟪r, p⟫`, `z = ⟪p, q⟫` and
`D = det (p, q, r)`, squared: `tri_poly` after the change of variables of the proof of Lemma 8.2. -/
theorem tri_sq_le (x y z D c : ℝ) (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hx : x ≤ c) (hy : y ≤ c) (hz : z ≤ c)
    (hG : D ^ 2 = 1 - x ^ 2 - y ^ 2 - z ^ 2 + 2 * x * y * z)
    (hcirc : 2 * c ^ 2 * ((1 - x) * (1 - y) * (1 - z)) ≤ (1 - c ^ 2) * D ^ 2) :
    (1 + x + y + z) ^ 2 * ((1 - c) ^ 2 * (1 + 2 * c)) ≤ (1 + 3 * c) ^ 2 * D ^ 2 := by
  set m := 1 - c with hm_def
  have hm0 : 0 < m := by linarith
  have hm : m ≤ 1 / 2 := by linarith
  set a := (c - x) / m with ha_def
  set b := (c - y) / m with hb_def
  set g := (c - z) / m with hg_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    have h : 0 ≤ c - x := by linarith
    exact div_nonneg h hm0.le
  have hb : 0 ≤ b := by
    rw [hb_def]
    have h : 0 ≤ c - y := by linarith
    exact div_nonneg h hm0.le
  have hg : 0 ≤ g := by
    rw [hg_def]
    have h : 0 ≤ c - z := by linarith
    exact div_nonneg h hm0.le
  have hxs : x = 1 - m * (1 + a) := by
    rw [ha_def]
    field_simp [hm0.ne']
    ring
  have hys : y = 1 - m * (1 + b) := by
    rw [hb_def]
    field_simp [hm0.ne']
    ring
  have hzs : z = 1 - m * (1 + g) := by
    rw [hg_def]
    field_simp [hm0.ne']
    ring
  have hcs : c = 1 - m := by
    rw [hm_def]
    ring
  set U := 1 + a with hU_def
  set V := 1 + b with hV_def
  set W := 1 + g with hW_def
  set H := 2 * (U * V + V * W + W * U) - U ^ 2 - V ^ 2 - W ^ 2 with hH_def
  set T := U * V * W with hT_def
  set K := (2 - m) * H - 2 * T with hK_def
  have id1 : 1 - x ^ 2 - y ^ 2 - z ^ 2 + 2 * x * y * z = m ^ 2 * (H - 2 * m * T) := by
    rw [hxs, hys, hzs, hU_def, hV_def, hW_def, hH_def, hT_def]
    ring
  have id2a : (1 - x) * (1 - y) * (1 - z) = m ^ 3 * T := by
    rw [hxs, hys, hzs, hU_def, hV_def, hW_def, hT_def]
    ring
  have id2b : 1 - c ^ 2 = m * (2 - m) := by
    rw [hcs]
    ring
  have id3 : (1 - c ^ 2) * D ^ 2 - 2 * c ^ 2 * ((1 - x) * (1 - y) * (1 - z)) = m ^ 3 * K := by
    rw [id2a, id2b, hG, id1, hK_def, hH_def, hT_def]
    ring
  have hK_nonneg : 0 ≤ K := by
    have h_nonneg : 0 ≤ (1 - c ^ 2) * D ^ 2 - 2 * c ^ 2 * ((1 - x) * (1 - y) * (1 - z)) := by linarith
    rw [id3] at h_nonneg
    have hm3_pos : 0 < m ^ 3 := pow_pos hm0 3
    exact nonneg_of_mul_nonneg_right h_nonneg hm3_pos
  set S := U + V + W with hS_def
  set F := (H - 2 * m * T) * (4 - 3 * m) ^ 2 - (3 - 2 * m) * (4 - m * S) ^ 2 with hF_def
  have h_tri_poly : 0 ≤ (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
      - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2 - 2 * m * ((1 + a) * (1 + b) * (1 + g)))
      * (4 - 3 * m) ^ 2 - (3 - 2 * m) * (4 - m * ((1 + a) + (1 + b) + (1 + g))) ^ 2 := by
    have hK_tri : 0 ≤ (2 - m) * (2 * ((1 + a) * (1 + b) + (1 + b) * (1 + g) + (1 + g) * (1 + a))
        - (1 + a) ^ 2 - (1 + b) ^ 2 - (1 + g) ^ 2) - 2 * ((1 + a) * (1 + b) * (1 + g)) := by
      rw [hK_def, hH_def, hT_def, hU_def, hV_def, hW_def] at hK_nonneg
      exact hK_nonneg
    exact Tammes15.FejesToth.tri_poly m a b g hm0 hm ha hb hg hK_tri
  have hD_sq : D ^ 2 = m ^ 2 * (H - 2 * m * T) := by
    rw [hG, id1]
  have id4 : (1 + 3 * c) ^ 2 * D ^ 2 - (1 + x + y + z) ^ 2 * ((1 - c) ^ 2 * (1 + 2 * c)) = m ^ 2 * F := by
    rw [hcs, hF_def, hD_sq]
    rw [hxs, hys, hzs, hU_def, hV_def, hW_def, hS_def]
    ring
  have hF_nonneg : 0 ≤ F := by
    rw [hF_def, hH_def, hT_def, hS_def, hU_def, hV_def, hW_def]
    exact h_tri_poly
  have hm_sq_nonneg : 0 ≤ m ^ 2 := pow_two_nonneg _
  have hprod_nonneg : 0 ≤ m ^ 2 * F := mul_nonneg hm_sq_nonneg hF_nonneg
  linarith

/-- `s D₀ ≤ s₀ D`, the form of the triangle lemma that `arg_le_arg_of_mul_le` takes. -/
theorem tri_mul_le (x y z D c : ℝ) (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hx : x ≤ c) (hy : y ≤ c) (hz : z ≤ c) (hD : 0 < D)
    (hG : D ^ 2 = 1 - x ^ 2 - y ^ 2 - z ^ 2 + 2 * x * y * z)
    (hcirc : 2 * c ^ 2 * ((1 - x) * (1 - y) * (1 - z)) ≤ (1 - c ^ 2) * D ^ 2) :
    (1 + x + y + z) * ((1 - c) * √(1 + 2 * c)) ≤ (1 + 3 * c) * D := by
  set s := 1 + x + y + z with hs
  set D₀ := (1 - c) * √(1 + 2 * c) with hD₀
  set s₀ := 1 + 3 * c with hs₀
  have h_one_minus_c_pos : 0 < 1 - c := by linarith
  have h_one_plus_2c_pos : 0 < 1 + 2 * c := by linarith
  have h_one_plus_2c_nonneg : 0 ≤ 1 + 2 * c := by linarith
  have hD₀_pos : 0 < D₀ := by
    rw [hD₀]
    have h_sqrt_pos : 0 < √(1 + 2 * c) := Real.sqrt_pos.mpr h_one_plus_2c_pos
    exact mul_pos h_one_minus_c_pos h_sqrt_pos
  have hs₀_pos : 0 < s₀ := by
    rw [hs₀]
    linarith
  by_cases hs_nonpos : s ≤ 0
  · -- s ≤ 0: left side ≤ 0, right side > 0
    have h_left : s * D₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_nonpos (by linarith)
    have h_right : 0 < s₀ * D := mul_pos hs₀_pos hD
    linarith
  · -- s > 0: square both sides and use tri_sq_le
    have hs_pos : 0 < s := by linarith
    have h_left_nonneg : 0 ≤ s * D₀ := by positivity
    have h_right_nonneg : 0 ≤ s₀ * D := by positivity
    have h_sq : (s * D₀) ^ 2 ≤ (s₀ * D) ^ 2 := by
      calc
        (s * D₀) ^ 2 = s ^ 2 * D₀ ^ 2 := by ring
        _ = s ^ 2 * (((1 - c) * √(1 + 2 * c)) ^ 2) := by rw [hD₀]
        _ = s ^ 2 * ((1 - c) ^ 2 * (√(1 + 2 * c)) ^ 2) := by ring
        _ = s ^ 2 * ((1 - c) ^ 2 * (1 + 2 * c)) := by
          rw [Real.sq_sqrt h_one_plus_2c_nonneg]
        _ ≤ s₀ ^ 2 * D ^ 2 := by
          rw [hs, hs₀]
          -- tri_sq_le : (1+x+y+z)^2 * ((1-c)^2*(1+2*c)) ≤ (1+3*c)^2 * D^2
          -- which is exactly s^2 * ((1-c)^2*(1+2*c)) ≤ s₀^2 * D^2
          simpa [hs, hs₀] using Tammes15.FejesToth.tri_sq_le x y z D c hc hc1 hx hy hz hG hcirc
        _ = (s₀ * D) ^ 2 := by ring
    have h_final := (pow_le_pow_iff_left₀ h_left_nonneg h_right_nonneg (by norm_num : 2 ≠ 0)).mp h_sq
    exact h_final

/-- Lemma 8.1: the angle sum of a spherical triangle as an argument. -/
theorem angle_sum_arg (x y z D : ℝ) (hD : 0 < D) (hx : x < 1) (hy : y < 1) (hz : z < 1)
    (hG : D ^ 2 = 1 - x ^ 2 - y ^ 2 - z ^ 2 + 2 * x * y * z)
    (hexc : π < Complex.arg ⟨x - y * z, D⟩ + Complex.arg ⟨y - z * x, D⟩ + Complex.arg ⟨z - x * y, D⟩) :
    Complex.arg ⟨x - y * z, D⟩ + Complex.arg ⟨y - z * x, D⟩ + Complex.arg ⟨z - x * y, D⟩
      = π + 2 * Complex.arg ⟨1 + x + y + z, D⟩ := by
  set w1 : ℂ := ⟨x - y * z, D⟩ with hw1
  set w2 : ℂ := ⟨y - z * x, D⟩ with hw2
  set w3 : ℂ := ⟨z - x * y, D⟩ with hw3
  set S : ℂ := ⟨1 + x + y + z, D⟩ with hSdef
  have ne (u : ℂ) (hu : 0 < u.im) : u ≠ 0 := fun h => by simp [h] at hu
  have h1 : w1 ≠ 0 := ne w1 hD
  have h2 : w2 ≠ 0 := ne w2 hD
  have h3 : w3 ≠ 0 := ne w3 hD
  have hS : S ≠ 0 := ne S hD
  have hk : 0 < (1 - x) * (1 - y) * (1 - z) / 2 := by
    have : 0 < (1 - x) * (1 - y) * (1 - z) := by
      apply mul_pos (mul_pos _ _) <;> linarith
    positivity
  -- the product identity
  have hprod : w1 * w2 * w3 = (((1 - x) * (1 - y) * (1 - z) / 2 : ℝ) : ℂ) * (-(S ^ 2)) := by
    apply Complex.ext
    · simp [w1, w2, w3, S, pow_two, Complex.mul_re, Complex.mul_im]
      linear_combination ((x * y * z + x * y + y * z + z * x - x - y - z - 1) / 2) * hG
    · simp [w1, w2, w3, S, pow_two, Complex.mul_re, Complex.mul_im]
      linear_combination (-D) * hG
  -- arguments in `Real.Angle`
  have hang : ((Complex.arg w1 + Complex.arg w2 + Complex.arg w3 : ℝ) : Real.Angle)
      = ((π + 2 * Complex.arg S : ℝ) : Real.Angle) := by
    have e1 : (Complex.arg (w1 * w2 * w3) : Real.Angle)
        = Complex.arg w1 + Complex.arg w2 + Complex.arg w3 := by
      rw [Complex.arg_mul_coe_angle (mul_ne_zero h1 h2) h3, Complex.arg_mul_coe_angle h1 h2]
    have e2 : Complex.arg (w1 * w2 * w3) = Complex.arg (-(S ^ 2)) := by
      rw [hprod, Complex.arg_real_mul _ hk]
    have e3 : (Complex.arg (-(S ^ 2)) : Real.Angle) = 2 • (Complex.arg S : Real.Angle) + π := by
      rw [Complex.arg_neg_coe_angle (pow_ne_zero 2 hS), Complex.arg_pow_coe_angle]
    rw [Real.Angle.coe_add, Real.Angle.coe_add, Real.Angle.coe_add,
      show (2 * Complex.arg S : ℝ) = ((2 : ℕ) : ℝ) * Complex.arg S by norm_num, ← nsmul_eq_mul,
      Real.Angle.coe_nsmul, ← e1, e2, e3]
    abel
  obtain ⟨k, hkeq⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hA1 := Complex.arg_le_pi w1
  have hA2 := Complex.arg_le_pi w2
  have hA3 := Complex.arg_le_pi w3
  have hθ0' : 0 ≤ Complex.arg S := Complex.arg_nonneg_iff.mpr hD.le
  have hθ0 : 0 < Complex.arg S := by
    rcases hθ0'.lt_or_eq with h | h
    · exact h
    · exfalso
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      simp [S] at this
      linarith
  have hθ1 : Complex.arg S < π := Complex.arg_lt_pi_iff.mpr (Or.inr hD.ne')
  have hk1 : (k : ℝ) < 1 := by
    by_contra h
    push Not at h
    nlinarith [Real.pi_pos]
  have hk2 : -1 < (k : ℝ) := by
    by_contra h
    push Not at h
    nlinarith [Real.pi_pos]
  have hk0 : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hkeq
  simp at hkeq
  linarith

/-- Comparison of two arguments in the upper half plane (proof of Lemma 8.2). -/
theorem arg_le_arg_of_mul_le (s D s₀ D₀ : ℝ) (hD : 0 < D) (hD₀ : 0 < D₀) (hs₀ : 0 < s₀)
    (h : s * D₀ ≤ s₀ * D) : Complex.arg ⟨s₀, D₀⟩ ≤ Complex.arg ⟨s, D⟩ := by
  set z : ℂ := ⟨s, D⟩ with hz
  set z₀ : ℂ := ⟨s₀, D₀⟩ with hz₀
  have hz_im_pos : 0 < z.im := by
    dsimp [z]
    exact hD
  have hz₀_im_pos : 0 < z₀.im := by
    dsimp [z₀]
    exact hD₀
  rw [Complex.arg_of_im_pos hz₀_im_pos, Complex.arg_of_im_pos hz_im_pos]
  refine Real.arccos_le_arccos ?_
  dsimp [z, z₀]
  -- Need: s / ‖⟨s, D⟩‖ ≤ s₀ / ‖⟨s₀, D₀⟩‖
  by_cases hs_nonpos : s ≤ 0
  · -- s ≤ 0: left fraction ≤ 0 < right fraction
    have h_nonpos : s / ‖(⟨s, D⟩ : ℂ)‖ ≤ 0 := by
      refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
      exact hs_nonpos
    have h_pos : 0 < s₀ / ‖(⟨s₀, D₀⟩ : ℂ)‖ := by
      refine div_pos hs₀ ?_
      have h_ne_zero : (⟨s₀, D₀⟩ : ℂ) ≠ 0 := by
        intro hzero
        have : D₀ = 0 := by simpa using congrArg Complex.im hzero
        linarith
      exact (norm_pos_iff.mpr h_ne_zero)
    linarith
  · -- s > 0
    have hs_pos : 0 < s := by linarith
    -- Square both sides: (s / ‖z‖)² ≤ (s₀ / ‖z₀‖)²
    have h_sq : (s / ‖(⟨s, D⟩ : ℂ)‖) ^ 2 ≤ (s₀ / ‖(⟨s₀, D₀⟩ : ℂ)‖) ^ 2 := by
      have h1 : (s / ‖(⟨s, D⟩ : ℂ)‖) ^ 2 = s ^ 2 / (‖(⟨s, D⟩ : ℂ)‖ ^ 2) := by ring
      have h2 : (s₀ / ‖(⟨s₀, D₀⟩ : ℂ)‖) ^ 2 = s₀ ^ 2 / (‖(⟨s₀, D₀⟩ : ℂ)‖ ^ 2) := by ring
      rw [h1, h2]
      have h_norm_sq : ‖(⟨s, D⟩ : ℂ)‖ ^ 2 = s ^ 2 + D ^ 2 := by
        calc
          ‖(⟨s, D⟩ : ℂ)‖ ^ 2 = Complex.normSq (⟨s, D⟩ : ℂ) := by
            rw [Complex.normSq_eq_norm_sq]
          _ = s ^ 2 + D ^ 2 := by
            simp; ring
      have h_norm₀_sq : ‖(⟨s₀, D₀⟩ : ℂ)‖ ^ 2 = s₀ ^ 2 + D₀ ^ 2 := by
        calc
          ‖(⟨s₀, D₀⟩ : ℂ)‖ ^ 2 = Complex.normSq (⟨s₀, D₀⟩ : ℂ) := by
            rw [Complex.normSq_eq_norm_sq]
          _ = s₀ ^ 2 + D₀ ^ 2 := by
            simp; ring
      rw [h_norm_sq, h_norm₀_sq]
      have h_denom_pos : 0 < s ^ 2 + D ^ 2 := by nlinarith
      have h_denom₀_pos : 0 < s₀ ^ 2 + D₀ ^ 2 := by nlinarith
      rw [div_le_div_iff₀ h_denom_pos h_denom₀_pos]
      -- Goal: s² * (s₀² + D₀²) ≤ s₀² * (s² + D²)
      -- Expand both sides, cancel s²*s₀², reduces to s²*D₀² ≤ s₀²*D² = (s*D₀)² ≤ (s₀*D)²
      have h_sq : (s * D₀) ^ 2 ≤ (s₀ * D) ^ 2 := by
        have h_nonneg_prod : 0 ≤ s * D₀ := by nlinarith
        have h_nonneg_prod₀ : 0 ≤ s₀ * D := by nlinarith
        nlinarith
      nlinarith
    -- Now we have (s/‖z‖)² ≤ (s₀/‖z₀‖)² and both sides are nonnegative, so s/‖z‖ ≤ s₀/‖z₀‖
    have h_nonneg : 0 ≤ s / ‖(⟨s, D⟩ : ℂ)‖ := by
      refine div_nonneg (by linarith) (by positivity)
    have h_nonneg₀ : 0 ≤ s₀ / ‖(⟨s₀, D₀⟩ : ℂ)‖ := by
      refine div_nonneg (by linarith) (by positivity)
    nlinarith

/-- Lemma 8.1: the corner of a positively oriented triangle as an argument. -/
theorem sphereVertexAngle_eq_arg (p q r : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hD : 0 < ⟪cross p q, r⟫) :
    sphereVertexAngle p q r
      = Complex.arg ⟨⟪q, r⟫ - ⟪p, q⟫ * ⟪p, r⟫, ⟪cross p q, r⟫⟩ := by
  rw [sphereVertexAngle_eq_ocorner p q r hp hq hr hD, ocorner, inner_tdir p q r hp,
    inner_cross_tdir]
  have h0 : 0 ≤ Complex.arg ⟨⟪q, r⟫ - ⟪p, q⟫ * ⟪p, r⟫, ⟪cross p q, r⟫⟩ :=
    Complex.arg_nonneg_iff.mpr hD.le
  have h1 := Complex.arg_le_pi (⟨⟪q, r⟫ - ⟪p, q⟫ * ⟪p, r⟫, ⟪cross p q, r⟫⟩ : ℂ)
  refine (toIcoMod_eq_self two_pi_pos).mpr ⟨h0, ?_⟩
  linarith [Real.pi_pos]

/-- The Gram identity for unit vectors, `D² = 1 - x² - y² - z² + 2xyz`. -/
theorem gram_cross (p q r : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) :
    ⟪cross p q, r⟫ ^ 2 = 1 - ⟪q, r⟫ ^ 2 - ⟪r, p⟫ ^ 2 - ⟪p, q⟫ ^ 2 + 2 * ⟪q, r⟫ * ⟪r, p⟫ * ⟪p, q⟫ := by
  have h := unit_triple_gram_identity p q r hp hq hr
  rw [crossVec_eq_cross] at h
  rw [h, real_inner_comm p r]
  ring

/-- The inner products of `w = p × q + q × r + r × p` with the vertices are `det (p, q, r)`. -/
theorem inner_cross_sum (p q r : E3) :
    ⟪cross p q + cross q r + cross r p, p⟫ = ⟪cross p q, r⟫ ∧
      ⟪cross p q + cross q r + cross r p, q⟫ = ⟪cross p q, r⟫ ∧
      ⟪cross p q + cross q r + cross r p, r⟫ = ⟪cross p q, r⟫ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three, inner_add_left] <;> ring

/-- `‖p × q + q × r + r × p‖² = G + 2 (1 - x)(1 - y)(1 - z)` at unit norms. -/
theorem inner_cross_sum_self (p q r : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hr : ‖r‖ = 1) :
    ⟪cross p q + cross q r + cross r p, cross p q + cross q r + cross r p⟫ =
      1 - ⟪q, r⟫ ^ 2 - ⟪r, p⟫ ^ 2 - ⟪p, q⟫ ^ 2 + 2 * ⟪q, r⟫ * ⟪r, p⟫ * ⟪p, q⟫
        + 2 * ((1 - ⟪q, r⟫) * (1 - ⟪r, p⟫) * (1 - ⟪p, q⟫)) := by
  have hpp : ⟪p, p⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hqq : ⟪q, q⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hq, one_pow]
  have hrr : ⟪r, r⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hr, one_pow]
  simp only [inner_add_left, inner_add_right, inner_cross_cross, hpp, hqq, hrr]
  rw [real_inner_comm q p, real_inner_comm r q, real_inner_comm p r]
  ring

/-- The circumcentre is `(k / D) (p × q + q × r + r × p)`. -/
theorem circumcentre_smul (p q r n : E3) (k : ℝ) (hkp : ⟪n, p⟫ = k)
    (hkq : ⟪n, q⟫ = k) (hkr : ⟪n, r⟫ = k) (hD : ⟪cross p q, r⟫ ≠ 0) :
    ⟪cross p q, r⟫ • n = k • (cross p q + cross q r + cross r p) := by
  set D := ⟪cross p q, r⟫ with hDdef
  set w := cross p q + cross q r + cross r p with hwdef
  have hsum := FejesToth.inner_cross_sum p q r
  have hp_w : ⟪p, w⟫ = D := by
    simpa [w, D, real_inner_comm] using hsum.1
  have hq_w : ⟪q, w⟫ = D := by
    simpa [w, D, real_inner_comm] using hsum.2.1
  have hr_w : ⟪r, w⟫ = D := by
    simpa [w, D, real_inner_comm] using hsum.2.2
  set y := D • n - k • w with hydef
  have hp_y : ⟪p, y⟫ = 0 := by
    calc
      ⟪p, y⟫ = ⟪p, D • n - k • w⟫ := rfl
      _ = ⟪p, D • n⟫ - ⟪p, k • w⟫ := by rw [inner_sub_right]
      _ = D * ⟪p, n⟫ - k * ⟪p, w⟫ := by simp [real_inner_smul_right]
      _ = D * ⟪n, p⟫ - k * D := by simp [real_inner_comm p n, hp_w]
      _ = D * k - k * D := by rw [hkp]
      _ = 0 := by ring
  have hq_y : ⟪q, y⟫ = 0 := by
    calc
      ⟪q, y⟫ = ⟪q, D • n - k • w⟫ := rfl
      _ = ⟪q, D • n⟫ - ⟪q, k • w⟫ := by rw [inner_sub_right]
      _ = D * ⟪q, n⟫ - k * ⟪q, w⟫ := by simp [real_inner_smul_right]
      _ = D * ⟪n, q⟫ - k * D := by simp [real_inner_comm q n, hq_w]
      _ = D * k - k * D := by rw [hkq]
      _ = 0 := by ring
  have hr_y : ⟪r, y⟫ = 0 := by
    calc
      ⟪r, y⟫ = ⟪r, D • n - k • w⟫ := rfl
      _ = ⟪r, D • n⟫ - ⟪r, k • w⟫ := by rw [inner_sub_right]
      _ = D * ⟪r, n⟫ - k * ⟪r, w⟫ := by simp [real_inner_smul_right]
      _ = D * ⟪n, r⟫ - k * D := by simp [real_inner_comm r n, hr_w]
      _ = D * k - k * D := by rw [hkr]
      _ = 0 := by ring
  have hy_zero : y = 0 :=
    eq_zero_of_inner_eq_zero3 p q r y hD hp_y hq_y hr_y
  have h_eq : D • n = k • w := sub_eq_zero.mp hy_zero
  simpa [D, w] using h_eq

/-- The circumcentre relation `D² (1 - k²) = 2 k² (1 - x)(1 - y)(1 - z)` (proof of Lemma 8.2). -/
theorem circumcentre_identity (p q r n : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hn : ‖n‖ = 1) (k : ℝ) (hkp : ⟪n, p⟫ = k) (hkq : ⟪n, q⟫ = k) (hkr : ⟪n, r⟫ = k)
    (hD : ⟪cross p q, r⟫ ≠ 0) :
    ⟪cross p q, r⟫ ^ 2 * (1 - k ^ 2) = 2 * k ^ 2 * ((1 - ⟪q, r⟫) * (1 - ⟪r, p⟫) * (1 - ⟪p, q⟫)) := by
  set D := ⟪cross p q, r⟫ with hDdef
  set w := cross p q + cross q r + cross r p with hwdef
  set P := (1 - ⟪q, r⟫) * (1 - ⟪r, p⟫) * (1 - ⟪p, q⟫) with hPdef
  have h_smul : D • n = k • w := Tammes15.FejesToth.circumcentre_smul p q r n k hkp hkq hkr hD
  have h_inner_w : ⟪w, w⟫ = (1 - ⟪q, r⟫ ^ 2 - ⟪r, p⟫ ^ 2 - ⟪p, q⟫ ^ 2 + 2 * ⟪q, r⟫ * ⟪r, p⟫ * ⟪p, q⟫) + 2 * P := by
    rw [hwdef]
    exact Tammes15.FejesToth.inner_cross_sum_self p q r hp hq hr
  have h_gram : D ^ 2 = 1 - ⟪q, r⟫ ^ 2 - ⟪r, p⟫ ^ 2 - ⟪p, q⟫ ^ 2 + 2 * ⟪q, r⟫ * ⟪r, p⟫ * ⟪p, q⟫ := by
    rw [hDdef]
    exact Tammes15.FejesToth.gram_cross p q r hp hq hr
  have h_eq : D ^ 2 = k ^ 2 * (D ^ 2 + 2 * P) := by
    calc
      D ^ 2 = D ^ 2 * ⟪n, n⟫ := by
        rw [real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
      _ = (D * D) * ⟪n, n⟫ := by rw [sq]
      _ = D * (D * ⟪n, n⟫) := by ring
      _ = D * ⟪n, D • n⟫ := by rw [real_inner_smul_right]
      _ = ⟪D • n, D • n⟫ := by rw [real_inner_smul_left]
      _ = ⟪k • w, k • w⟫ := by rw [h_smul]
      _ = k * ⟪w, k • w⟫ := by rw [real_inner_smul_left]
      _ = k * (k * ⟪w, w⟫) := by rw [real_inner_smul_right]
      _ = k ^ 2 * ⟪w, w⟫ := by ring
      _ = k ^ 2 * ((1 - ⟪q, r⟫ ^ 2 - ⟪r, p⟫ ^ 2 - ⟪p, q⟫ ^ 2 + 2 * ⟪q, r⟫ * ⟪r, p⟫ * ⟪p, q⟫) + 2 * P) := by rw [h_inner_w]
      _ = k ^ 2 * (D ^ 2 + 2 * P) := by rw [← h_gram]
  nlinarith

/-- Lemma 8.2: the triangle lemma. -/
theorem fejesToth_triangle (p q r n : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hn : ‖n‖ = 1) (c k : ℝ) (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hck : c ≤ k)
    (hkp : ⟪n, p⟫ = k) (hkq : ⟪n, q⟫ = k) (hkr : ⟪n, r⟫ = k)
    (hpq : ⟪p, q⟫ ≤ c) (hqr : ⟪q, r⟫ ≤ c) (hrp : ⟪r, p⟫ ≤ c) (hD : 0 < ⟪cross p q, r⟫) :
    π + 2 * Complex.arg ⟨1 + 3 * c, (1 - c) * √(1 + 2 * c)⟩
      ≤ sphereVertexAngle p q r + sphereVertexAngle q r p + sphereVertexAngle r p q := by
  have hD2 : 0 < ⟪cross q r, p⟫ := by rw [inner_cross_cyc]; exact hD
  have hD3 : 0 < ⟪cross r p, q⟫ := by rw [inner_cross_cyc, inner_cross_cyc]; exact hD
  have hA : sphereVertexAngle p q r = Complex.arg ⟨⟪q, r⟫ - ⟪r, p⟫ * ⟪p, q⟫, ⟪cross p q, r⟫⟩ := by
    rw [sphereVertexAngle_eq_arg p q r hp hq hr hD, real_inner_comm r p, mul_comm]
  have hB : sphereVertexAngle q r p = Complex.arg ⟨⟪r, p⟫ - ⟪p, q⟫ * ⟪q, r⟫, ⟪cross p q, r⟫⟩ := by
    rw [sphereVertexAngle_eq_arg q r p hq hr hp hD2, inner_cross_cyc, real_inner_comm p q,
      mul_comm]
  have hC : sphereVertexAngle r p q = Complex.arg ⟨⟪p, q⟫ - ⟪q, r⟫ * ⟪r, p⟫, ⟪cross p q, r⟫⟩ := by
    rw [sphereVertexAngle_eq_arg r p q hr hp hq hD3, inner_cross_cyc, inner_cross_cyc,
      real_inner_comm q r, mul_comm]
  have hG := gram_cross p q r hp hq hr
  have hexc := spherical_triangle_excess_positive p q r hp hq hr
    (by rw [crossVec_eq_cross]; exact hD.ne')
  rw [hA, hB, hC] at hexc ⊢
  have hsum := angle_sum_arg ⟪q, r⟫ ⟪r, p⟫ ⟪p, q⟫ ⟪cross p q, r⟫ hD (by linarith) (by linarith)
    (by linarith) (by linear_combination hG) hexc
  rw [hsum]
  have hcirc0 := circumcentre_identity p q r n hp hq hr hn k hkp hkq hkr hD.ne'
  have hc0 : 0 < c := by linarith
  have hP : 0 ≤ (1 - ⟪q, r⟫) * (1 - ⟪r, p⟫) * (1 - ⟪p, q⟫) := by
    have h1 : 0 ≤ 1 - ⟪q, r⟫ := by linarith
    have h2 : 0 ≤ 1 - ⟪r, p⟫ := by linarith
    have h3 : 0 ≤ 1 - ⟪p, q⟫ := by linarith
    positivity
  have hck2 : c ^ 2 ≤ k ^ 2 := by nlinarith
  have hcirc : 2 * c ^ 2 * ((1 - ⟪q, r⟫) * (1 - ⟪r, p⟫) * (1 - ⟪p, q⟫)) ≤
      (1 - c ^ 2) * ⟪cross p q, r⟫ ^ 2 := by
    have hD2 : 0 ≤ ⟪cross p q, r⟫ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hck2 hP, mul_le_mul_of_nonneg_left hck2 hD2]
  have hmul := tri_mul_le ⟪q, r⟫ ⟪r, p⟫ ⟪p, q⟫ ⟪cross p q, r⟫ c hc hc1 hqr hrp hpq hD
    (by linear_combination hG) hcirc
  have hD₀ : 0 < (1 - c) * √(1 + 2 * c) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))
  have harg := arg_le_arg_of_mul_le (1 + ⟪q, r⟫ + ⟪r, p⟫ + ⟪p, q⟫) ⟪cross p q, r⟫ (1 + 3 * c)
    ((1 - c) * √(1 + 2 * c)) hD hD₀ (by linarith) hmul
  linarith

end Tammes15.FejesToth
