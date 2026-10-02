import Tammes15.Contractors.Tri

/-!
# Monotonicity of the fan maps (T9) and the corner evaluation of `monoBounds` (Section 5.3)

An output of the pentagon and hexagon contractors is `C(u) = bangle d u + gam c (ebase d u) b`
in a corner `u` (the base angle of the isosceles triangle at the corner, plus an angle of the middle
triangle). It is non-increasing on `[p, q] ⊆ (0, π]` when `cos d sin(u/2) + cot X cos(u/2) ≥ 0`
wherever the middle triangle is not degenerate (`fanC_antitoneOn`); where it is degenerate the
angle is the constant `0` or `π`. `decDir_sound` reads that sign from the interval test of deep.rs
`dec_dir`; `monoBounds_mem` evaluates a function at the corners of a box selected by the
directions; `cornerEnds_spec` gives the corners.
-/

namespace Tammes15.Contractors

open Real
open scoped Classical
open Tammes15 Tammes15.PaperSteps.Search

theorem ebase_hasDerivAt {d u : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hu : 0 < u ∧ u < 2 * π) :
    HasDerivAt (ebase d) (sin d * cos (u / 2) / √(1 - (sin d * sin (u / 2)) ^ 2)) u := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hu with ⟨hupos, hult⟩
  have hd_sin_pos : 0 < sin d :=
    Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith)
  have hd_sin_lt_one : sin d < 1 := by
    have hneg : -(π / 2) ≤ d := by linarith
    have hle : π / 2 ≤ π / 2 := le_refl _
    have hlt : d < π / 2 := hdlt
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hneg hle hlt
    calc
      sin d < sin (π / 2) := h
      _ = 1 := Real.sin_pi_div_two
  have hu2pos : 0 < u / 2 := by linarith
  have hu2ltpi : u / 2 < π := by linarith
  have hu2_sin_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hu2pos hu2ltpi
  have hu2_sin_le_one : sin (u / 2) ≤ 1 :=
    Real.sin_le_one (u / 2)
  set s := sin d * sin (u / 2) with hs_def
  have hs_pos : 0 < s := mul_pos hd_sin_pos hu2_sin_pos
  have hs_lt_one : s < 1 := by
    nlinarith
  have hs_ne_one : s ≠ 1 := by linarith
  have hs_ne_neg_one : s ≠ -1 := by linarith
  have h_deriv_s : HasDerivAt (fun x : ℝ => sin d * sin (x / 2))
      (sin d * (cos (u / 2) * ((1 : ℝ) / 2))) u := by
    have h1 : HasDerivAt (fun x : ℝ => sin (x / 2)) (cos (u / 2) * ((1 : ℝ) / 2)) u := by
      have h_inner : HasDerivAt (fun x : ℝ => x / 2) ((1 : ℝ) / 2) u := by
        simpa using (hasDerivAt_id u).div_const 2
      have h_sin : HasDerivAt sin (cos (u / 2)) (u / 2) := Real.hasDerivAt_sin (u / 2)
      exact HasDerivAt.comp u h_sin h_inner
    have h_const : HasDerivAt (fun _ : ℝ => sin d) 0 u :=
      hasDerivAt_const (c := sin d) (x := u)
    convert h_const.mul h1 using 1
    ring
  have h_deriv_arcsin : HasDerivAt Real.arcsin (1 / √(1 - s ^ 2)) s :=
    Real.hasDerivAt_arcsin hs_ne_neg_one hs_ne_one
  have h_deriv_comp : HasDerivAt (fun x : ℝ => Real.arcsin (sin d * sin (x / 2)))
      ((1 / √(1 - s ^ 2)) * (sin d * (cos (u / 2) * ((1 : ℝ) / 2)))) u :=
    HasDerivAt.comp (x := u) (h := fun x => sin d * sin (x / 2)) (h₂ := Real.arcsin)
      h_deriv_arcsin h_deriv_s
  have h_deriv_ebase : HasDerivAt (ebase d)
      (2 * ((1 / √(1 - s ^ 2)) * (sin d * (cos (u / 2) * ((1 : ℝ) / 2))))) u :=
    h_deriv_comp.const_mul 2
  have h_simplify : 2 * ((1 / √(1 - s ^ 2)) * (sin d * (cos (u / 2) * ((1 : ℝ) / 2)))) =
      sin d * cos (u / 2) / √(1 - (sin d * sin (u / 2)) ^ 2) := by
    rw [hs_def]
    field_simp
  rw [hs_def] at h_deriv_ebase
  rw [h_simplify] at h_deriv_ebase
  exact h_deriv_ebase

theorem bangle_hasDerivAt {d u : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hu : 0 < u ∧ u < 2 * π) :
    HasDerivAt (bangle d) (-cos d / (2 * (1 - (sin d * sin (u / 2)) ^ 2))) u := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hu with ⟨hupos, hult⟩
  set h := u / 2 with hh
  have hhpos : 0 < h := by linarith
  have hhltpi : h < π := by linarith
  have hcosd_pos : cos d > 0 := Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hsinh_pos : sin h > 0 := Real.sin_pos_of_pos_of_lt_pi hhpos hhltpi
  have hsinh_ne_zero : sin h ≠ 0 := by linarith
  have hcosd_ne_zero : cos d ≠ 0 := by linarith
  have hsin_ne_zero' : sin (u / 2) ≠ 0 := by simpa [hh] using hsinh_ne_zero
  have hhalf_deriv : HasDerivAt (fun x : ℝ => x / 2) (1/2 : ℝ) u := by
    simpa [div_eq_inv_mul] using (hasDerivAt_id u).const_mul (1/2 : ℝ)
  have hcos_deriv : HasDerivAt (fun x => cos (x / 2)) (-(sin (u / 2)) * (1/2 : ℝ)) u := by
    have := HasDerivAt.comp u (Real.hasDerivAt_cos (u/2)) hhalf_deriv
    -- this : HasDerivAt (cos ∘ (fun x => x/2)) ((-sin (u/2)) * (1/2)) u
    have h : (cos ∘ (fun x => x / 2)) = (fun x => cos (x / 2)) := by rfl
    simpa [h] using this
  have hsin_deriv : HasDerivAt (fun x => sin (x / 2)) (cos (u / 2) * (1/2 : ℝ)) u := by
    have := HasDerivAt.comp u (Real.hasDerivAt_sin (u/2)) hhalf_deriv
    have h : (sin ∘ (fun x => x / 2)) = (fun x => sin (x / 2)) := by rfl
    simpa [h] using this
  have hnum : HasDerivAt (fun x => cos (x / 2)) (-(sin (u / 2)) * (1/2 : ℝ)) u := hcos_deriv
  have hdenom : HasDerivAt (fun x => cos d * sin (x / 2)) (cos d * cos (u / 2) * (1/2 : ℝ)) u := by
    have := hsin_deriv.const_mul (cos d)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hdenom_ne_zero : (fun x => cos d * sin (x / 2)) u ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using mul_ne_zero hcosd_ne_zero hsin_ne_zero'
  have hinner_deriv : HasDerivAt (fun x => cos (x / 2) / (cos d * sin (x / 2)))
      (((-(sin (u / 2)) * (1/2 : ℝ)) * (cos d * sin (u / 2)) - cos (u / 2) * (cos d * cos (u / 2) * (1/2 : ℝ))) /
        ((cos d * sin (u / 2)) ^ 2)) u :=
    HasDerivAt.div hnum hdenom hdenom_ne_zero
  have hinner_simp : (-(sin (u / 2)) * (1/2 : ℝ)) * (cos d * sin (u / 2)) - cos (u / 2) * (cos d * cos (u / 2) * (1/2 : ℝ))
      = -cos d / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (u/2)]
  have hinner_deriv_simp : HasDerivAt (fun x => cos (x / 2) / (cos d * sin (x / 2)))
      (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2))) u := by
    convert hinner_deriv using 1
    rw [hinner_simp]
    ring
  have harctan_deriv : HasDerivAt Real.arctan (1 / (1 + ((cos (u / 2) / (cos d * sin (u / 2))) ^ 2)))
      ((cos (u / 2) / (cos d * sin (u / 2)))) :=
    Real.hasDerivAt_arctan _
  have hcomp : HasDerivAt (Real.arctan ∘ (fun x => cos (x / 2) / (cos d * sin (x / 2))))
      ((1 / (1 + ((cos (u / 2) / (cos d * sin (u / 2))) ^ 2))) *
        (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2)))) u :=
    HasDerivAt.comp u harctan_deriv hinner_deriv_simp
  -- Now simplify the expression to the target
  have htarget : (1 / (1 + ((cos (u / 2) / (cos d * sin (u / 2))) ^ 2))) *
      (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2))) =
      -cos d / (2 * (1 - (sin d * sin h) ^ 2)) := by
    have h_key : cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2 = 1 - (sin d * sin (u / 2)) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq d, Real.sin_sq_add_cos_sq (u/2)]
    have h_denom_ne_zero' : (cos d * sin (u / 2)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero hcosd_ne_zero hsin_ne_zero')
    have h_sum_eq : 1 + ((cos (u / 2) / (cos d * sin (u / 2))) ^ 2) =
        (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2) / ((cos d * sin (u / 2)) ^ 2) := by
      rw [div_pow]
      calc
        1 + cos (u / 2) ^ 2 / ((cos d * sin (u / 2)) ^ 2) =
          (((cos d * sin (u / 2)) ^ 2) / ((cos d * sin (u / 2)) ^ 2)) + (cos (u / 2) ^ 2 / ((cos d * sin (u / 2)) ^ 2)) := by
          rw [div_self h_denom_ne_zero']
        _ = (((cos d * sin (u / 2)) ^ 2) + cos (u / 2) ^ 2) / ((cos d * sin (u / 2)) ^ 2) := by rw [add_div]
        _ = (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2) / ((cos d * sin (u / 2)) ^ 2) := by
          rw [show ((cos d * sin (u / 2)) ^ 2) = cos d ^ 2 * sin (u / 2) ^ 2 by ring]
    calc
      (1 / (1 + ((cos (u / 2) / (cos d * sin (u / 2))) ^ 2))) *
          (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2))) =
        (1 / ((cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2) / ((cos d * sin (u / 2)) ^ 2))) *
          (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2))) := by rw [h_sum_eq]
      _ = (((cos d * sin (u / 2)) ^ 2) / (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2)) *
          (-cos d / (2 * ((cos d * sin (u / 2)) ^ 2))) := by
        rw [one_div_div]
      _ = -cos d / (2 * (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2)) := by
        rw [div_mul_div_comm]
        rw [show ((cos d * sin (u / 2)) ^ 2) * (-cos d) = (-cos d) * ((cos d * sin (u / 2)) ^ 2) by ring]
        rw [show (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2) * (2 * ((cos d * sin (u / 2)) ^ 2)) =
          (2 * (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2)) * ((cos d * sin (u / 2)) ^ 2) by ring]
        exact mul_div_mul_right (-cos d) h_denom_ne_zero' (b := 2 * (cos d ^ 2 * sin (u / 2) ^ 2 + cos (u / 2) ^ 2))
      _ = -cos d / (2 * (1 - (sin d * sin (u / 2)) ^ 2)) := by rw [h_key]
      _ = -cos d / (2 * (1 - (sin d * sin h) ^ 2)) := by simp [hh]
  -- Now note that bangle d = Real.arctan ∘ (fun x => cos(x/2) / (cos d * sin(x/2)))
  have hbangle_eq : bangle d = Real.arctan ∘ (fun x => cos (x / 2) / (cos d * sin (x / 2))) := by
    ext x
    simp [bangle]
  rw [hbangle_eq]
  rw [← htarget]
  exact hcomp

theorem fanC_hasDerivAt {d u b c : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hu : 0 < u ∧ u < π) (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π)
    (h : -1 < eta c (ebase d u) b ∧ eta c (ebase d u) b < 1) :
    HasDerivAt (fun u => bangle d u + gam c (ebase d u) b)
      (-(cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) /
        (2 * sin (u / 2) * (1 - (sin d * sin (u / 2)) ^ 2))) u := by
  have hd0 := hd.1
  have hd1 := hd.2
  have hu0 := hu.1
  have hu1 := hu.2
  have hb0 := hb.1
  have hb1 := hb.2
  have hc0 := hc.1
  have hc1 := hc.2
  have h_eta_low := h.1
  have h_eta_high := h.2
  set s := sin d * sin (u / 2) with hs_def
  set K := √(1 - s ^ 2) with hK_def
  set e := ebase d u with he_def
  have hd_sin_pos : 0 < sin d := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith)
  have hu_sin_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hs_pos : 0 < s := by
    rw [hs_def]
    exact mul_pos hd_sin_pos hu_sin_pos
  have hs_lt_one : s < 1 := by
    rw [hs_def]
    have h1 : sin d < 1 := by
      have : sin d < sin (π / 2) :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hd1
      simpa [sin_pi_div_two] using this
    have h2 : sin (u / 2) ≤ 1 := sin_le_one _
    have h_mul : sin d * sin (u / 2) < 1 * 1 :=
      mul_lt_mul h1 h2 (by positivity) (by positivity)
    linarith
  have hs_nonneg : 0 ≤ s := by linarith
  have hs_le_one : s ≤ 1 := by linarith
  have hs_ge_neg_one : -1 ≤ s := by linarith
  have h_ebase_pos : 0 < e := by
    rw [he_def, ebase]
    have h_arcsin_pos : 0 < arcsin s :=
      (Real.arcsin_pos.mpr hs_pos)
    nlinarith
  have h_ebase_lt_pi : e < π := by
    rw [he_def, ebase]
    have h_arcsin_lt : arcsin s < π / 2 :=
      (Real.arcsin_lt_pi_div_two).mpr hs_lt_one
    nlinarith [pi_pos]
  have h_sin_e_pos : 0 < sin e :=
    Real.sin_pos_of_pos_of_lt_pi h_ebase_pos h_ebase_lt_pi
  have h_sin_e_ne_zero : sin e ≠ 0 := by linarith
  have h_sin_u2_ne_zero : sin (u / 2) ≠ 0 := by linarith
  have h_K_pos : 0 < K := by
    rw [hK_def]
    refine Real.sqrt_pos.mpr ?_
    have : s ^ 2 < 1 := by nlinarith
    nlinarith
  have h_K_ne_zero : K ≠ 0 := by linarith
  have h_K_sq : K ^ 2 = 1 - s ^ 2 := by
    rw [hK_def]
    have h_nonneg : 0 ≤ 1 - s ^ 2 := by
      have : s ^ 2 ≤ 1 := by nlinarith
      linarith
    rw [Real.sq_sqrt h_nonneg]
  have h_sin_e_eq : sin e = 2 * s * K := by
    rw [he_def, ebase]
    calc
      sin (2 * arcsin s) = 2 * sin (arcsin s) * cos (arcsin s) := by
        rw [Real.sin_two_mul]
      _ = 2 * s * cos (arcsin s) := by rw [Real.sin_arcsin hs_ge_neg_one hs_le_one]
      _ = 2 * s * √(1 - s ^ 2) := by rw [Real.cos_arcsin s]
      _ = 2 * s * K := by rw [hK_def]
  have hu_lt_2pi : u < 2 * π := by linarith [pi_pos]
  have h_bangle : HasDerivAt (bangle d)
      (-cos d / (2 * (1 - s ^ 2))) u := by
    have := bangle_hasDerivAt hd ⟨hu0, hu_lt_2pi⟩
    simpa [hs_def] using this
  have h_ebase : HasDerivAt (ebase d)
      (sin d * cos (u / 2) / K) u := by
    have := ebase_hasDerivAt hd ⟨hu0, hu_lt_2pi⟩
    simpa [hs_def, hK_def] using this
  have h_gam : HasDerivAt (fun a => gam c a b)
      (-(cot (gam b e c)) / sin e) e := by
    have := gam_hasDerivAt_side e b c ⟨h_ebase_pos, h_ebase_lt_pi⟩ hb hc
      ⟨by simpa [he_def] using h_eta_low,
       by simpa [he_def] using h_eta_high⟩
    simpa [he_def] using this
  have h_chain : HasDerivAt ((fun a => gam c a b) ∘ ebase d)
      ((-(cot (gam b e c)) / sin e) * (sin d * cos (u / 2) / K)) u :=
    HasDerivAt.comp u h_gam h_ebase
  have h_add : HasDerivAt (fun u => bangle d u + gam c (ebase d u) b)
      ((-cos d / (2 * (1 - s ^ 2))) +
       ((-(cot (gam b e c)) / sin e) * (sin d * cos (u / 2) / K))) u := by
    have : (fun u => bangle d u + gam c (ebase d u) b) =
        (bangle d) + ((fun a => gam c a b) ∘ ebase d) := by
      ext x; simp [Function.comp]
    rw [this]
    exact HasDerivAt.add h_bangle h_chain
  convert h_add using 1
  have h_denom : 1 - s ^ 2 = K ^ 2 := by rw [h_K_sq]
  rw [h_denom]
  field_simp [h_sin_e_ne_zero, h_sin_u2_ne_zero, h_K_ne_zero]
  ring_nf
  rw [h_sin_e_eq]
  field_simp [h_sin_u2_ne_zero, h_K_ne_zero]
  ring

theorem eta_mem_Ioo {b c e : ℝ} (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π)
    (he : 0 < e ∧ e < π) (h1 : |b - c| < e) (h2 : e < min (b + c) (2 * π - b - c)) :
    -1 < eta c e b ∧ eta c e b < 1 := by
  rcases hb with ⟨hb_pos, hb_lt_pi⟩
  rcases hc with ⟨hc_pos, hc_lt_pi⟩
  rcases he with ⟨he_pos, he_lt_pi⟩
  have hsin_pos : sin e * sin b > 0 := by
    have hsin_e_pos : sin e > 0 := sin_pos_of_pos_of_lt_pi he_pos he_lt_pi
    have hsin_b_pos : sin b > 0 := sin_pos_of_pos_of_lt_pi hb_pos hb_lt_pi
    exact mul_pos hsin_e_pos hsin_b_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have h_abs_nonneg : 0 ≤ |e - b| := abs_nonneg _
  have h_abs_lt_pi : |e - b| < π := by
    have h_low : -π < e - b := by
      have hpi_pos : 0 < π := Real.pi_pos
      linarith
    have h_high : e - b < π := by linarith
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h_abs_le_pi : |e - b| ≤ π := le_of_lt h_abs_lt_pi
  have h_abs_lt_c : |e - b| < c := by
    rcases (abs_sub_lt_iff (a := b) (b := c) (c := e)).mp h1 with ⟨h_left, h_right⟩
    have h_e_lt_b_add_c : e < b + c := lt_of_lt_of_le h2 (min_le_left _ _)
    apply (abs_sub_lt_iff (a := e) (b := b) (c := c)).mpr
    constructor
    · linarith
    · linarith
  have h_cos_lt_one : eta c e b < 1 := by
    rw [eta]
    apply (div_lt_iff₀ hsin_pos).mpr
    have h_cos_sub : cos e * cos b + sin e * sin b = cos (e - b) := by
      rw [Real.cos_sub e b]
    have h_cos_lt : cos c < cos (|e - b|) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi h_abs_nonneg (le_of_lt hc_lt_pi) h_abs_lt_c
    have h_cos_abs : cos (|e - b|) = cos (e - b) := Real.cos_abs (e - b)
    rw [h_cos_abs] at h_cos_lt
    rw [← h_cos_sub] at h_cos_lt
    linarith
  have h_cos_gt_neg_one : -1 < eta c e b := by
    rw [eta]
    apply (lt_div_iff₀ hsin_pos).mpr
    have h_cos_add : cos e * cos b - sin e * sin b = cos (e + b) := by
      rw [Real.cos_add e b]
    have h_c_lt_e_add_b : c < e + b := by
      rcases (abs_sub_lt_iff (a := b) (b := c) (c := e)).mp h1 with ⟨h_left, h_right⟩
      linarith
    have h_c_lt_two_pi_sub : c < 2 * π - e - b := by
      have h_e_lt_two_pi_sub : e < 2 * π - b - c := by
        -- from h2: e < min (b + c) (2 * π - b - c)
        exact lt_of_lt_of_le h2 (min_le_right _ _)
      linarith
    by_cases h_e_add_b_le_pi : e + b ≤ π
    · have h_cos_lt : cos (e + b) < cos c :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hc_nonneg h_e_add_b_le_pi h_c_lt_e_add_b
      have h_goal : cos e * cos b - sin e * sin b < cos c := by
        rw [h_cos_add]
        exact h_cos_lt
      linarith
    · have h_e_add_b_gt_pi : π < e + b := by linarith
      have h_two_pi_sub_e_add_b_pos : 0 < 2 * π - e - b := by linarith
      have h_two_pi_sub_e_add_b_lt_pi : 2 * π - e - b < π := by linarith
      have h_cos_eq : cos (e + b) = cos (2 * π - e - b) := by
        have : cos (e + b) = cos (2 * π - (e + b)) := by
          rw [Real.cos_sub (2 * π) (e + b), Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
        simpa [sub_sub] using this
      have h_cos_lt : cos (2 * π - e - b) < cos c :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hc_nonneg (le_of_lt h_two_pi_sub_e_add_b_lt_pi) h_c_lt_two_pi_sub
      have h_goal : cos e * cos b - sin e * sin b < cos c := by
        rw [h_cos_add, h_cos_eq]
        exact h_cos_lt
      linarith
  exact And.intro h_cos_gt_neg_one h_cos_lt_one

theorem gam_of_le_abs {b c e : ℝ} (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (he : 0 < e ∧ e < π) (h : e ≤ |b - c|) :
    gam c e b = if c ≤ b then 0 else π := by
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases he with ⟨he0, he1⟩
  have hsin_pos : sin e * sin b > 0 := by
    exact mul_pos (sin_pos_of_pos_of_lt_pi he0 he1) (sin_pos_of_pos_of_lt_pi hb0 hb1)
  by_cases hcb : c ≤ b
  · -- case c ≤ b: then e ≤ b - c
    have h_abs : e ≤ b - c := by
      have : |b - c| = b - c := abs_of_nonneg (sub_nonneg.mpr hcb)
      rw [this] at h
      exact h
    have h_cos_le : cos (b - e) ≤ cos c :=
      Real.cos_le_cos_of_nonneg_of_le_pi hc0.le (by linarith) (by linarith)
    have h_cos_sub_eq : cos (b - e) = cos e * cos b + sin e * sin b := by
      rw [Real.cos_sub, mul_comm (cos b), mul_comm (sin b)]
    rw [h_cos_sub_eq] at h_cos_le
    have h_eta_ge_one : 1 ≤ eta c e b := by
      dsimp [eta]
      rw [one_le_div hsin_pos]
      linarith
    dsimp [gam]
    rw [Real.arccos_of_one_le h_eta_ge_one]
    rw [if_pos hcb]
  · -- case b < c
    have hbc : b < c := by linarith
    have h_abs' : e ≤ c - b := by
      have : |b - c| = -(b - c) := abs_of_neg (sub_neg.mpr hbc)
      rw [this] at h
      linarith
    have h_cos_le : cos c ≤ cos (e + b) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hc1.le (by linarith)
    have h_cos_add_eq : cos (e + b) = cos e * cos b - sin e * sin b := by
      rw [Real.cos_add]
    rw [h_cos_add_eq] at h_cos_le
    have h_eta_le_neg_one : eta c e b ≤ -1 := by
      dsimp [eta]
      calc
        (cos c - cos e * cos b) / (sin e * sin b) ≤ (-(sin e * sin b)) / (sin e * sin b) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ = -1 := by
          rw [neg_div, div_self (hsin_pos.ne.symm)]
    dsimp [gam]
    rw [Real.arccos_of_le_neg_one h_eta_le_neg_one]
    rw [if_neg (by linarith : ¬ c ≤ b)]

theorem gam_of_min_le {b c e : ℝ} (hb : 0 < b ∧ b < π)
    (hc : 0 < c ∧ c < π) (he : 0 < e ∧ e < π) (h : min (b + c) (2 * π - b - c) ≤ e) :
    gam c e b = if b + c ≤ π then 0 else π := by
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases he with ⟨he0, he1⟩
  have hsin_pos : 0 < sin e * sin b := by
    have hsin_e : 0 < sin e := Real.sin_pos_of_pos_of_lt_pi he0 he1
    have hsin_b : 0 < sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hb1
    exact mul_pos hsin_e hsin_b
  unfold gam eta
  by_cases hle : b + c ≤ π
  · -- case b + c ≤ π
    have hmin : min (b + c) (2 * π - b - c) = b + c := min_eq_left (by linarith)
    rw [hmin] at h
    have hc_le_e_sub_b : c ≤ e - b := by linarith
    have hcos_le : cos (e - b) ≤ cos c :=
      Real.cos_le_cos_of_nonneg_of_le_pi hc0.le (by linarith) hc_le_e_sub_b
    have hcos_sub : cos (e - b) = cos e * cos b + sin e * sin b := by
      rw [Real.cos_sub e b]
    rw [hcos_sub] at hcos_le
    have hnum : 1 ≤ (cos c - cos e * cos b) / (sin e * sin b) := by
      refine (one_le_div hsin_pos).mpr ?_
      linarith
    rw [Real.arccos_of_one_le hnum]
    rw [if_pos hle]
  · -- case π < b + c
    have hmin : min (b + c) (2 * π - b - c) = 2 * π - b - c := by
      apply min_eq_right
      linarith
    rw [hmin] at h
    have hwpos : 0 < 2 * π - (e + b) := by linarith
    have hw_le_c : 2 * π - (e + b) ≤ c := by linarith
    have hw_le_pi : 2 * π - (e + b) ≤ π := by linarith
    have hcos_le : cos c ≤ cos (2 * π - (e + b)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hc1.le hw_le_c
    have hcos_two_pi_sub : cos (2 * π - (e + b)) = cos (e + b) := by
      rw [Real.cos_two_pi_sub]
    rw [hcos_two_pi_sub] at hcos_le
    have hcos_add : cos (e + b) = cos e * cos b - sin e * sin b := by
      rw [Real.cos_add e b]
    rw [hcos_add] at hcos_le
    have hnum : (cos c - cos e * cos b) / (sin e * sin b) ≤ -1 := by
      have h' : (cos c - cos e * cos b) ≤ -(sin e * sin b) := by linarith
      calc
        (cos c - cos e * cos b) / (sin e * sin b) ≤ (-(sin e * sin b)) / (sin e * sin b) :=
          div_le_div_of_nonneg_right h' hsin_pos.le
        _ = -1 := by
          field_simp [hsin_pos.ne.symm]
          rw [div_self hsin_pos.ne.symm]
    rw [Real.arccos_of_le_neg_one hnum]
    rw [if_neg (by linarith)]

theorem antitoneOn_glue3 {f φ : ℝ → ℝ} {p q A B : ℝ}
    (hφ : MonotoneOn φ (Set.Icc p q)) (hφc : ContinuousOn φ (Set.Icc p q)) (hAB : A ≤ B)
    (h0 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ φ u ≤ A})
    (h1 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B})
    (h2 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ B ≤ φ u}) :
    AntitoneOn f (Set.Icc p q) := by
  intro x hx y hy hxy
  rcases hx with ⟨hpx, hxq⟩
  rcases hy with ⟨hpy, hyq⟩
  have hφxy : φ x ≤ φ y := hφ ⟨hpx, hxq⟩ ⟨hpy, hyq⟩ hxy
  have hφc_xy : ContinuousOn φ (Set.Icc x y) :=
    hφc.mono (Set.Icc_subset_Icc hpx hyq)
  have h_ivt : Set.Icc (φ x) (φ y) ⊆ φ '' Set.Icc x y :=
    intermediate_value_Icc hxy hφc_xy
  by_cases hφyA : φ y ≤ A
  · -- case 1: φ y ≤ A
    have hy_set : y ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨⟨hpy, hyq⟩, hφyA⟩
    have hx_set : x ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨⟨hpx, hxq⟩, le_trans hφxy hφyA⟩
    exact h0 hx_set hy_set hxy
  · have hAy : A < φ y := lt_of_not_ge hφyA
    by_cases hφxA : φ x ≤ A
    · -- φ x ≤ A < φ y
      by_cases hφyB : φ y ≤ B
      · -- case 2: φ x ≤ A < φ y ≤ B
        have hA_mem : A ∈ Set.Icc (φ x) (φ y) := ⟨hφxA, le_of_lt hAy⟩
        rcases h_ivt hA_mem with ⟨m, hm, hm_eq⟩
        rcases hm with ⟨hmx, hmy⟩
        have hm_Icc_pq : m ∈ Set.Icc p q := ⟨le_trans hpx hmx, le_trans hmy hyq⟩
        have hm_set1 : m ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} := by
          refine ⟨hm_Icc_pq, ?_, ?_⟩
          · simpa [hm_eq] using le_refl A
          · simpa [hm_eq] using hAB
        have hy_set1 : y ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} :=
          ⟨⟨hpy, hyq⟩, le_of_lt hAy, hφyB⟩
        have hm_set0 : m ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨hm_Icc_pq, by rw [hm_eq]⟩
        have hx_set0 : x ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨⟨hpx, hxq⟩, hφxA⟩
        have h1_res : f y ≤ f m := h1 hm_set1 hy_set1 hmy
        have h0_res : f m ≤ f x := h0 hx_set0 hm_set0 hmx
        exact le_trans h1_res h0_res
      · -- case 3: φ x ≤ A, B < φ y
        have hA_mem : A ∈ Set.Icc (φ x) (φ y) := ⟨hφxA, le_of_lt hAy⟩
        rcases h_ivt hA_mem with ⟨m₁, hm₁, hm₁_eq⟩
        rcases hm₁ with ⟨hm₁x, hm₁y⟩
        have hm₁_Icc_pq : m₁ ∈ Set.Icc p q := ⟨le_trans hpx hm₁x, le_trans hm₁y hyq⟩
        have h_ivt_m₁y : Set.Icc (φ m₁) (φ y) ⊆ φ '' Set.Icc m₁ y :=
          intermediate_value_Icc hm₁y (hφc.mono (Set.Icc_subset_Icc (le_trans hpx hm₁x) hyq))
        have hB_mem : B ∈ Set.Icc (φ m₁) (φ y) := by
          rw [hm₁_eq]
          exact ⟨hAB, le_of_lt (lt_of_not_ge hφyB)⟩
        rcases h_ivt_m₁y hB_mem with ⟨m₂, hm₂, hm₂_eq⟩
        rcases hm₂ with ⟨hm₂m₁, hm₂y⟩
        have hm₂_Icc_pq : m₂ ∈ Set.Icc p q :=
          ⟨le_trans hpx (le_trans hm₁x hm₂m₁), le_trans hm₂y hyq⟩
        have hy_set2 : y ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := ⟨⟨hpy, hyq⟩, le_of_lt (lt_of_not_ge hφyB)⟩
        have hm₂_set2 : m₂ ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := ⟨hm₂_Icc_pq, by rw [hm₂_eq]⟩
        have hm₁_set1 : m₁ ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} := by
          refine ⟨hm₁_Icc_pq, ?_, ?_⟩
          · simpa [hm₁_eq] using le_refl A
          · simpa [hm₁_eq] using hAB
        have hm₂_set1 : m₂ ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} := by
          refine ⟨hm₂_Icc_pq, ?_, ?_⟩
          · simpa [hm₂_eq] using hAB
          · simpa [hm₂_eq] using le_refl B
        have hx_set0 : x ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨⟨hpx, hxq⟩, hφxA⟩
        have hm₁_set0 : m₁ ∈ {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := ⟨hm₁_Icc_pq, by rw [hm₁_eq]⟩
        have h2_res : f y ≤ f m₂ := h2 hm₂_set2 hy_set2 hm₂y
        have h1_res : f m₂ ≤ f m₁ := h1 hm₁_set1 hm₂_set1 hm₂m₁
        have h0_res : f m₁ ≤ f x := h0 hx_set0 hm₁_set0 hm₁x
        exact le_trans (le_trans h2_res h1_res) h0_res
    · -- A < φ x
      have hxA : A < φ x := lt_of_not_ge hφxA
      by_cases hφxB : φ x ≤ B
      · -- A < φ x ≤ B
        by_cases hφyB : φ y ≤ B
        · -- case 4: A < φ x, φ y ≤ B
          have hAy : A ≤ φ y := le_trans (le_of_lt hxA) hφxy
          have hx_set1 : x ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} :=
            ⟨⟨hpx, hxq⟩, le_of_lt hxA, hφxB⟩
          have hy_set1 : y ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} :=
            ⟨⟨hpy, hyq⟩, hAy, hφyB⟩
          exact h1 hx_set1 hy_set1 hxy
        · -- case 5: A < φ x ≤ B < φ y
          have hBy : B < φ y := lt_of_not_ge hφyB
          have hB_mem : B ∈ Set.Icc (φ x) (φ y) := ⟨hφxB, le_of_lt hBy⟩
          rcases h_ivt hB_mem with ⟨m, hm, hm_eq⟩
          rcases hm with ⟨hmx, hmy⟩
          have hm_Icc_pq : m ∈ Set.Icc p q := ⟨le_trans hpx hmx, le_trans hmy hyq⟩
          have hm_set2 : m ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := ⟨hm_Icc_pq, by rw [hm_eq]⟩
          have hy_set2 : y ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := ⟨⟨hpy, hyq⟩, le_of_lt hBy⟩
          have hm_set1 : m ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} := by
            refine ⟨hm_Icc_pq, ?_, ?_⟩
            · simpa [hm_eq] using le_trans (le_of_lt hxA) hφxB
            · simpa [hm_eq] using le_refl B
          have hx_set1 : x ∈ {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} :=
            ⟨⟨hpx, hxq⟩, le_of_lt hxA, hφxB⟩
          have h2_res : f y ≤ f m := h2 hm_set2 hy_set2 hmy
          have h1_res : f m ≤ f x := h1 hx_set1 hm_set1 hmx
          exact le_trans h2_res h1_res
      · -- case 6: B < φ x
        have hxB : B < φ x := lt_of_not_ge hφxB
        have hy_set2 : y ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} :=
          ⟨⟨hpy, hyq⟩, le_trans (le_of_lt hxB) hφxy⟩
        have hx_set2 : x ∈ {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := ⟨⟨hpx, hxq⟩, le_of_lt hxB⟩
        exact h2 hx_set2 hy_set2 hxy

theorem fanC_continuousOn {d b c : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π) :
    ContinuousOn (fun u => bangle d u + gam c (ebase d u) b) (Set.Ioc 0 π) := by
  rcases hd with ⟨hdpos, hdlt⟩
  rcases hb with ⟨hbpos, hblt⟩
  have hcosd_pos : cos d > 0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  have hcosd_ne_zero : cos d ≠ 0 := by linarith
  have hsinb_pos : sin b > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨hbpos, hblt⟩
  have hsinb_ne_zero : sin b ≠ 0 := by linarith
  have hsin_d_pos : sin d > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨hdpos, by linarith⟩
  have hsin_d_lt_one : sin d < 1 := by
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hdlt
    simpa [Real.sin_pi_div_two] using this
  intro u hu
  rcases hu with ⟨hu_pos, hu_le⟩
  have hdiv_cont : ContinuousAt (fun x : ℝ => x / 2) u := by
    exact continuous_id.continuousAt.div continuousAt_const (by norm_num)
  have hsin_half_pos : sin (u / 2) > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hdenom1_ne_zero : cos d * sin (u / 2) ≠ 0 :=
    mul_ne_zero hcosd_ne_zero (by linarith)
  have hbangle_cont : ContinuousAt (fun u => bangle d u) u := by
    dsimp [bangle]
    refine Real.continuous_arctan.continuousAt.comp ?_
    refine ContinuousAt.div ?_ ?_ hdenom1_ne_zero
    · exact Real.continuous_cos.continuousAt.comp hdiv_cont
    · exact (continuousAt_const.mul (Real.continuous_sin.continuousAt.comp hdiv_cont))
  have hebase_cont : ContinuousAt (ebase d) u := by
    unfold ebase
    refine (continuousAt_const.mul ?_)
    refine Real.continuous_arcsin.continuousAt.comp ?_
    refine (continuousAt_const.mul ?_)
    exact Real.continuous_sin.continuousAt.comp hdiv_cont
  have hprod_pos : sin d * sin (u / 2) > 0 :=
    mul_pos hsin_d_pos hsin_half_pos
  have hprod_lt_one : sin d * sin (u / 2) < 1 := by
    have h_sin_half_le_one : sin (u / 2) ≤ 1 := Real.sin_le_one _
    nlinarith
  have hebase_pos : ebase d u > 0 := by
    unfold ebase
    have h_arcsin_pos : arcsin (sin d * sin (u / 2)) > 0 :=
      (Real.arcsin_pos.mpr hprod_pos)
    nlinarith
  have hebase_lt_pi : ebase d u < π := by
    unfold ebase
    have h_arcsin_lt : arcsin (sin d * sin (u / 2)) < π / 2 :=
      (Real.arcsin_lt_pi_div_two.mpr hprod_lt_one)
    nlinarith
  have hsin_ebase_pos : sin (ebase d u) > 0 :=
    Real.sin_pos_of_mem_Ioo ⟨hebase_pos, hebase_lt_pi⟩
  have hsin_ebase_ne_zero : sin (ebase d u) ≠ 0 := by linarith
  have hdenom2_ne_zero : sin (ebase d u) * sin b ≠ 0 :=
    mul_ne_zero hsin_ebase_ne_zero hsinb_ne_zero
  have hgam_cont : ContinuousAt (fun u => gam c (ebase d u) b) u := by
    dsimp [gam, eta]
    refine Real.continuous_arccos.continuousAt.comp ?_
    refine ContinuousAt.div ?_ ?_ hdenom2_ne_zero
    · refine ContinuousAt.sub ?_ ?_
      · exact continuousAt_const
      · exact (Real.continuous_cos.continuousAt.comp hebase_cont).mul continuousAt_const
    · exact (Real.continuous_sin.continuousAt.comp hebase_cont).mul continuousAt_const
  exact (hbangle_cont.continuousWithinAt.add hgam_cont.continuousWithinAt)

theorem fanC_antitoneOn {d b c p q : ℝ} (hd : 0 < d ∧ d < π / 2)
    (hb : 0 < b ∧ b < π) (hc : 0 < c ∧ c < π) (hp : 0 < p) (hq : q ≤ π)
    (hF : ∀ u ∈ Set.Icc p q, -1 < eta c (ebase d u) b → eta c (ebase d u) b < 1 →
      0 ≤ cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) :
    AntitoneOn (fun u => bangle d u + gam c (ebase d u) b) (Set.Icc p q) := by
  rcases hd with ⟨hd0, hd1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  set φ := ebase d with hφ_def
  set A := |b - c| with hA_def
  set B := min (b + c) (2 * π - b - c) with hB_def
  set f := (fun u => bangle d u + gam c (ebase d u) b) with hf_def
  have hbundle : 0 < b ∧ b < π := ⟨hb0, hb1⟩
  have hcundle : 0 < c ∧ c < π := ⟨hc0, hc1⟩
  have hdundle : 0 < d ∧ d < π / 2 := ⟨hd0, hd1⟩
  have hA_le_B : A ≤ B := by
    rw [hA_def, hB_def]
    have h1 : |b - c| ≤ b + c := by
      rcases le_total b c with (hle | hle)
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        linarith
    have h2 : |b - c| ≤ 2 * π - b - c := by
      have hbc_le_π : |b - c| ≤ π := by
        rw [abs_le]
        constructor <;> linarith
      have h_sum_le : |b - c| + (b + c) ≤ 2 * π := by
        -- |b-c| + (b+c) = 2 * max(b,c) ≤ 2π
        rcases le_total b c with (hle | hle)
        · have : |b - c| = c - b := by
            rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
          rw [this]
          linarith
        · have : |b - c| = b - c := abs_of_nonneg (sub_nonneg.mpr hle)
          rw [this]
          linarith
      linarith
    exact le_min h1 h2
  have hφ_range : ∀ u, u ∈ Set.Icc p q → φ u ∈ Set.Ioo 0 π := by
    intro u hu
    rcases hu with ⟨hpu, huq⟩
    have hu_pos : 0 < u := by linarith
    have hu_le_π : u ≤ π := by linarith
    have hφ_pos : 0 < φ u := by
      dsimp [φ, ebase]
      have hsin_d_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hd0 (by linarith)
      have hsin_u_pos : 0 < sin (u / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by
        nlinarith)
      have h_sin_mul_pos : 0 < sin d * sin (u / 2) := mul_pos hsin_d_pos hsin_u_pos
      have h_sin_mul_lt_one : sin d * sin (u / 2) < 1 := by
        have hsin_d_lt_one : sin d < 1 := by
          have hpos : -(π / 2) ≤ d := by linarith
          have : sin d < sin (π/2) :=
            Real.sin_lt_sin_of_lt_of_le_pi_div_two hpos (by linarith) (by linarith)
          simpa using this
        have hsin_u_le_one : sin (u / 2) ≤ 1 := sin_le_one _
        nlinarith
      have hpos' : 0 ≤ sin d * sin (u / 2) := le_of_lt h_sin_mul_pos
      have harcsin_pos : 0 < arcsin (sin d * sin (u / 2)) := by
        rw [Real.arcsin_pos]
        exact h_sin_mul_pos
      nlinarith
    have hφ_lt_π : φ u < π := by
      dsimp [φ, ebase]
      have h_mul_le_sin_d : sin d * sin (u / 2) ≤ sin d := by
        have hsin_u_le_one : sin (u / 2) ≤ 1 := sin_le_one _
        have hsin_d_nonneg : 0 ≤ sin d := by linarith [sin_pos_of_pos_of_lt_pi hd0 (by linarith)]
        nlinarith
      have h_arcsin_le : arcsin (sin d * sin (u / 2)) ≤ arcsin (sin d) :=
        Real.arcsin_le_arcsin h_mul_le_sin_d
      have h_arcsin_sin_d_eq_d : arcsin (sin d) = d := by
        apply Real.arcsin_sin
        · linarith
        · linarith
      rw [h_arcsin_sin_d_eq_d] at h_arcsin_le
      have hsin_d_lt_one : sin d < 1 := by
        have hpos : -(π / 2) ≤ d := by linarith
        have : sin d < sin (π/2) :=
          Real.sin_lt_sin_of_lt_of_le_pi_div_two hpos (by linarith) (by linarith)
        simpa using this
      have h_2d_lt_π : 2 * d < π := by linarith
      nlinarith
    exact ⟨hφ_pos, hφ_lt_π⟩
  have h_sub_Icc_Ioc : Set.Icc p q ⊆ Set.Ioc 0 π := by
    intro u hu
    rcases hu with ⟨hpu, huq⟩
    have hu_pos : 0 < u := by linarith
    have hu_le_π : u ≤ π := by linarith
    exact ⟨hu_pos, hu_le_π⟩
  have hφ_mono : MonotoneOn φ (Set.Icc p q) := by
    have h_strictMono : StrictMonoOn φ (Set.Ioc 0 π) :=
      ebase_strictMonoOn d hdundle
    exact h_strictMono.monotoneOn.mono h_sub_Icc_Ioc
  have hφ_cont : ContinuousOn φ (Set.Icc p q) := by
    dsimp [φ]
    have h_cont : ContinuousOn (ebase d) (Set.Icc p q) := by
      -- ebase d u = 2 * arcsin (sin d * sin (u / 2))
      have h_cont_ebase : Continuous (ebase d) := by
        unfold ebase
        refine Continuous.mul (continuous_const) ?_
        refine Real.continuous_arcsin.comp ?_
        refine Continuous.mul (continuous_const) ?_
        refine continuous_sin.comp ?_
        refine Continuous.div continuous_id (continuous_const) (by norm_num)
      exact h_cont_ebase.continuousOn
    exact h_cont
  have h0 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ φ u ≤ A} := by
    intro u hu v hv huv
    rcases hu with ⟨hu_Icc, hu_le⟩
    rcases hv with ⟨hv_Icc, hv_le⟩
    have hu_φ_mem := hφ_range u hu_Icc
    have hv_φ_mem := hφ_range v hv_Icc
    have hu_φ_pos : 0 < φ u := hu_φ_mem.1
    have hu_φ_lt_π : φ u < π := hu_φ_mem.2
    have hv_φ_pos : 0 < φ v := hv_φ_mem.1
    have hv_φ_lt_π : φ v < π := hv_φ_mem.2
    have hgam_u : gam c (φ u) b = (if c ≤ b then 0 else π) := by
      dsimp [φ] at hu_le
      exact gam_of_le_abs hbundle hcundle ⟨hu_φ_pos, hu_φ_lt_π⟩ hu_le
    have hgam_v : gam c (φ v) b = (if c ≤ b then 0 else π) := by
      dsimp [φ] at hv_le
      exact gam_of_le_abs hbundle hcundle ⟨hv_φ_pos, hv_φ_lt_π⟩ hv_le
    dsimp [f]
    rw [hgam_u, hgam_v]
    have h_bangle_anti : AntitoneOn (bangle d) (Set.Ioc 0 π) :=
      (bangle_strictAntiOn d hdundle).antitoneOn
    have hu_Ioc : u ∈ Set.Ioc 0 π := h_sub_Icc_Ioc hu_Icc
    have hv_Ioc : v ∈ Set.Ioc 0 π := h_sub_Icc_Ioc hv_Icc
    have h := h_bangle_anti hu_Ioc hv_Ioc huv
    linarith
  have h2 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ B ≤ φ u} := by
    intro u hu v hv huv
    rcases hu with ⟨hu_Icc, hu_ge⟩
    rcases hv with ⟨hv_Icc, hv_ge⟩
    have hu_φ_mem := hφ_range u hu_Icc
    have hv_φ_mem := hφ_range v hv_Icc
    have hu_φ_pos : 0 < φ u := hu_φ_mem.1
    have hu_φ_lt_π : φ u < π := hu_φ_mem.2
    have hv_φ_pos : 0 < φ v := hv_φ_mem.1
    have hv_φ_lt_π : φ v < π := hv_φ_mem.2
    have hgam_u : gam c (φ u) b = (if b + c ≤ π then 0 else π) := by
      dsimp [φ] at hu_ge
      exact gam_of_min_le hbundle hcundle ⟨hu_φ_pos, hu_φ_lt_π⟩ hu_ge
    have hgam_v : gam c (φ v) b = (if b + c ≤ π then 0 else π) := by
      dsimp [φ] at hv_ge
      exact gam_of_min_le hbundle hcundle ⟨hv_φ_pos, hv_φ_lt_π⟩ hv_ge
    dsimp [f]
    rw [hgam_u, hgam_v]
    have h_bangle_anti : AntitoneOn (bangle d) (Set.Ioc 0 π) :=
      (bangle_strictAntiOn d hdundle).antitoneOn
    have hu_Ioc : u ∈ Set.Ioc 0 π := h_sub_Icc_Ioc hu_Icc
    have hv_Ioc : v ∈ Set.Ioc 0 π := h_sub_Icc_Ioc hv_Icc
    have h := h_bangle_anti hu_Ioc hv_Ioc huv
    linarith
  have h1 : AntitoneOn f {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} := by
    set M := {u | u ∈ Set.Icc p q ∧ A ≤ φ u ∧ φ u ≤ B} with hM_def
    have hM_ord_connected : M.OrdConnected := by
      refine Set.OrdConnected.mk ?_
      intro x hx y hy z hz
      rcases hx with ⟨⟨hxp, hxq⟩, hxA, hxB⟩
      rcases hy with ⟨⟨hyp, hyq⟩, hyA, hyB⟩
      rcases hz with ⟨hxz, hzy⟩
      have hzp : p ≤ z := by linarith
      have hzq : z ≤ q := by linarith
      have hz_mem : z ∈ Set.Icc p q := ⟨hzp, hzq⟩
      have hx_mem : x ∈ Set.Icc p q := ⟨hxp, hxq⟩
      have hy_mem : y ∈ Set.Icc p q := ⟨hyp, hyq⟩
      have hφx_le_φz : φ x ≤ φ z := hφ_mono hx_mem hz_mem hxz
      have hφz_le_φy : φ z ≤ φ y := hφ_mono hz_mem hy_mem hzy
      have hφz_ge_A : A ≤ φ z := by linarith
      have hφz_le_B : φ z ≤ B := by linarith
      exact ⟨⟨hzp, hzq⟩, hφz_ge_A, hφz_le_B⟩
    have hM_convex : Convex ℝ M := hM_ord_connected.convex
    have hM_cont : ContinuousOn (fun u => bangle d u + gam c (ebase d u) b) M := by
      have h_sub : M ⊆ Set.Ioc 0 π := by
        intro u hu
        rcases hu with ⟨hu_Icc, _, _⟩
        rcases hu_Icc with ⟨hpu, huq⟩
        exact ⟨by linarith, by linarith⟩
      have h_cont_on_Ioc : ContinuousOn (fun u => bangle d u + gam c (ebase d u) b) (Set.Ioc 0 π) :=
        fanC_continuousOn hdundle hbundle hcundle
      exact h_cont_on_Ioc.mono h_sub
    have hM_interior_subset : interior M ⊆ Set.Ioo p q := by
      intro u hu
      have h_sub_int : interior M ⊆ interior (Set.Icc p q) :=
        interior_mono (by
          intro v hv
          rcases hv with ⟨hv_Icc, _, _⟩
          exact hv_Icc)
      rw [interior_Icc] at h_sub_int
      exact h_sub_int hu
    have hM_interior_φ_range : ∀ u ∈ interior M, A < φ u ∧ φ u < B := by
      intro u hu
      have hu_mem_M : u ∈ M := interior_subset hu
      rcases hu_mem_M with ⟨⟨hpu, huq⟩, hA_le_φu, hφu_le_B⟩
      have hu_pos : 0 < u := by linarith
      have hu_lt_q : u < q := by
        have hu_Ioo := hM_interior_subset hu
        rcases hu_Ioo with ⟨_, hu_lt_q⟩
        exact hu_lt_q
      have hu_lt_π : u < π := by linarith
      have hu_mem_Ioc : u ∈ Set.Ioc 0 π := ⟨hu_pos, le_of_lt hu_lt_π⟩
      have hφ_strictMono : StrictMonoOn φ (Set.Ioc 0 π) :=
        ebase_strictMonoOn d hdundle
      -- Since u ∈ interior M, there exists v < u with v ∈ interior M ⊆ M
      have h_exists_left : ∃ v, v < u ∧ v ∈ interior M := by
        have h_open : IsOpen (interior M) := isOpen_interior
        rcases Metric.mem_nhds_iff.mp (h_open.mem_nhds hu) with ⟨ε, hε_pos, h_ball⟩
        refine ⟨u - ε/2, by linarith, ?_⟩
        apply h_ball
        rw [Metric.mem_ball, Real.dist_eq]
        have : |(u - ε/2) - u| = ε/2 := by
          calc
            |(u - ε/2) - u| = |-(ε/2)| := by ring
            _ = |ε/2| := by rw [abs_neg]
            _ = ε/2 := abs_of_pos (by linarith)
        rw [this]
        linarith
      rcases h_exists_left with ⟨v, hv_lt_u, hv_mem⟩
      have hv_mem_M : v ∈ M := interior_subset hv_mem
      rcases hv_mem_M with ⟨⟨hvp, hvq⟩, hA_le_φv, hφv_le_B⟩
      have hv_pos : 0 < v := by linarith
      have hv_lt_q : v < q := by
        have hv_Ioo := hM_interior_subset hv_mem
        rcases hv_Ioo with ⟨_, hv_lt_q⟩
        exact hv_lt_q
      have hv_lt_π : v < π := by linarith
      have hv_mem_Ioc : v ∈ Set.Ioc 0 π := ⟨hv_pos, le_of_lt hv_lt_π⟩
      have hφv_lt_φu : φ v < φ u := hφ_strictMono hv_mem_Ioc hu_mem_Ioc hv_lt_u
      have hA_lt_φu : A < φ u := by linarith
      -- Similarly, there exists w > u with w ∈ interior M
      have h_exists_right : ∃ w, u < w ∧ w ∈ interior M := by
        have h_open : IsOpen (interior M) := isOpen_interior
        rcases Metric.mem_nhds_iff.mp (h_open.mem_nhds hu) with ⟨ε, hε_pos, h_ball⟩
        refine ⟨u + ε/2, by linarith, ?_⟩
        apply h_ball
        rw [Metric.mem_ball, Real.dist_eq]
        have : |(u + ε/2) - u| = ε/2 := by
          calc
            |(u + ε/2) - u| = |ε/2| := by ring
            _ = ε/2 := abs_of_pos (by linarith)
        rw [this]
        linarith
      rcases h_exists_right with ⟨w, hu_lt_w, hw_mem⟩
      have hw_mem_M : w ∈ M := interior_subset hw_mem
      rcases hw_mem_M with ⟨⟨hwp, hwq⟩, hA_le_φw, hφw_le_B⟩
      have hw_pos : 0 < w := by linarith
      have hw_lt_q : w < q := by
        have hw_Ioo := hM_interior_subset hw_mem
        rcases hw_Ioo with ⟨_, hw_lt_q⟩
        exact hw_lt_q
      have hw_lt_π : w < π := by linarith
      have hw_mem_Ioc : w ∈ Set.Ioc 0 π := ⟨hw_pos, le_of_lt hw_lt_π⟩
      have hφu_lt_φw : φ u < φ w := hφ_strictMono hu_mem_Ioc hw_mem_Ioc hu_lt_w
      have hφu_lt_B : φ u < B := by linarith
      exact ⟨hA_lt_φu, hφu_lt_B⟩
    have hM_diff : DifferentiableOn ℝ (fun u => bangle d u + gam c (ebase d u) b) (interior M) := by
      intro u hu
      have hu_Ioo : u ∈ Set.Ioo p q := hM_interior_subset hu
      rcases hu_Ioo with ⟨hpu_lt, hu_lt_q⟩
      have hu_pos : 0 < u := by linarith
      have hu_lt_π : u < π := by linarith
      rcases hM_interior_φ_range u hu with ⟨hA_lt_φu, hφu_lt_B⟩
      have hu_ebase_pos : 0 < ebase d u := by
        have hA_nonneg : 0 ≤ A := by
          rw [hA_def]
          exact abs_nonneg _
        linarith
      have hu_ebase_lt_π : ebase d u < π := by
        have hB_le_π : B ≤ π := by
          rw [hB_def]
          by_cases h : b + c ≤ π
          · calc
              min (b + c) (2 * π - b - c) ≤ b + c := min_le_left _ _
              _ ≤ π := h
          · have : 2 * π - b - c ≤ π := by linarith
            calc
              min (b + c) (2 * π - b - c) ≤ 2 * π - b - c := min_le_right _ _
              _ ≤ π := this
        linarith
      have h_eta_range : -1 < eta c (ebase d u) b ∧ eta c (ebase d u) b < 1 := by
        have h1 : |b - c| < ebase d u := by
          dsimp [A, φ] at hA_lt_φu
          exact hA_lt_φu
        have h2 : ebase d u < min (b + c) (2 * π - b - c) := by
          dsimp [B, φ] at hφu_lt_B
          exact hφu_lt_B
        exact eta_mem_Ioo hbundle hcundle ⟨hu_ebase_pos, hu_ebase_lt_π⟩ h1 h2
      have h_hasDeriv : HasDerivAt (fun u => bangle d u + gam c (ebase d u) b)
        (-(cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) /
          (2 * sin (u / 2) * (1 - (sin d * sin (u / 2)) ^ 2))) u :=
        fanC_hasDerivAt hdundle ⟨hu_pos, hu_lt_π⟩ hbundle hcundle h_eta_range
      exact h_hasDeriv.differentiableAt.differentiableWithinAt
    have hM_deriv_nonpos : ∀ x ∈ interior M, deriv (fun u => bangle d u + gam c (ebase d u) b) x ≤ 0 := by
      intro u hu
      have hu_Ioo : u ∈ Set.Ioo p q := hM_interior_subset hu
      rcases hu_Ioo with ⟨hpu_lt, hu_lt_q⟩
      have hu_pos : 0 < u := by linarith
      have hu_lt_π : u < π := by linarith
      rcases hM_interior_φ_range u hu with ⟨hA_lt_φu, hφu_lt_B⟩
      have hu_ebase_pos : 0 < ebase d u := by
        have hA_nonneg : 0 ≤ A := by
          rw [hA_def]
          exact abs_nonneg _
        linarith
      have hu_ebase_lt_π : ebase d u < π := by
        have hB_le_π : B ≤ π := by
          rw [hB_def]
          by_cases h : b + c ≤ π
          · calc
              min (b + c) (2 * π - b - c) ≤ b + c := min_le_left _ _
              _ ≤ π := h
          · have : 2 * π - b - c ≤ π := by linarith
            calc
              min (b + c) (2 * π - b - c) ≤ 2 * π - b - c := min_le_right _ _
              _ ≤ π := this
        linarith
      have h_eta_range : -1 < eta c (ebase d u) b ∧ eta c (ebase d u) b < 1 := by
        have h1 : |b - c| < ebase d u := by
          dsimp [A, φ] at hA_lt_φu
          exact hA_lt_φu
        have h2 : ebase d u < min (b + c) (2 * π - b - c) := by
          dsimp [B, φ] at hφu_lt_B
          exact hφu_lt_B
        exact eta_mem_Ioo hbundle hcundle ⟨hu_ebase_pos, hu_ebase_lt_π⟩ h1 h2
      have h_hasDeriv : HasDerivAt (fun u => bangle d u + gam c (ebase d u) b)
        (-(cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) /
          (2 * sin (u / 2) * (1 - (sin d * sin (u / 2)) ^ 2))) u :=
        fanC_hasDerivAt hdundle ⟨hu_pos, hu_lt_π⟩ hbundle hcundle h_eta_range
      have h_deriv_eq : deriv (fun u => bangle d u + gam c (ebase d u) b) u =
        (-(cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) /
          (2 * sin (u / 2) * (1 - (sin d * sin (u / 2)) ^ 2))) :=
        h_hasDeriv.deriv
      rw [h_deriv_eq]
      have h_denom_pos : 0 < 2 * sin (u / 2) * (1 - (sin d * sin (u / 2)) ^ 2) := by
        have h_sin_pos : 0 < sin (u / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith)
        have h_sq_lt_one : (sin d * sin (u / 2)) ^ 2 < 1 := by
          have h_sin_d_lt_one : sin d < 1 := by
            have hpos : -(π / 2) ≤ d := by linarith
            have : sin d < sin (π/2) :=
              Real.sin_lt_sin_of_lt_of_le_pi_div_two hpos (by linarith) (by linarith)
            simpa using this
          have h_sin_u_le_one : sin (u / 2) ≤ 1 := sin_le_one _
          have h_mul_lt_one : sin d * sin (u / 2) < 1 := by
            nlinarith
          have h_mul_pos : 0 < sin d * sin (u / 2) := by
            have hsin_d_pos : 0 < sin d := sin_pos_of_pos_of_lt_pi hd0 (by linarith)
            exact mul_pos hsin_d_pos h_sin_pos
          nlinarith
        nlinarith
      have h_num_nonpos : -(cos d * sin (u / 2) + cot (gam b (ebase d u) c) * cos (u / 2)) ≤ 0 := by
        have hF' := hF u (by exact ⟨by linarith, by linarith⟩)
        rcases h_eta_range with ⟨h_eta_gt, h_eta_lt⟩
        have h_nonneg := hF' h_eta_gt h_eta_lt
        linarith
      exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by linarith)
    exact antitoneOn_of_deriv_nonpos hM_convex hM_cont hM_diff hM_deriv_nonpos
  rw [hf_def]
  exact antitoneOn_glue3 hφ_mono hφ_cont hA_le_B h0 h1 h2

theorem fanOpp_monotoneOn {d a b : ℝ} (hd : 0 < d ∧ d < π / 2)
    (ha : 0 < a ∧ a < π) (hb : 0 < b ∧ b < π) :
    MonotoneOn (fun u => gam (ebase d u) a b) (Set.Ioc 0 π) := by
  rcases hd with ⟨hd0, hd1⟩
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  have hsin_d_pos : 0 < sin d :=
    Real.sin_pos_of_mem_Ioo ⟨hd0, hd1.trans (by linarith [pi_pos])⟩
  have hsin_d_lt_one : sin d < 1 := by
    have : sin d < sin (π / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hd1
    simpa [sin_pi_div_two] using this
  intro u hu v hv huv
  have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).1
  have hu_le_pi : u ≤ π := (Set.mem_Ioc.mp hu).2
  have hv_pos : 0 < v := (Set.mem_Ioc.mp hv).1
  have hv_le_pi : v ≤ π := (Set.mem_Ioc.mp hv).2
  have hu_div2_pos : 0 < u / 2 := by linarith
  have hu_div2_le_pi_div_two : u / 2 ≤ π / 2 := by linarith
  have hv_div2_pos : 0 < v / 2 := by linarith
  have hv_div2_le_pi_div_two : v / 2 ≤ π / 2 := by linarith
  have hsin_u_div2_pos : 0 < sin (u / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨hu_div2_pos, by linarith⟩
  have hsin_v_div2_pos : 0 < sin (v / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨hv_div2_pos, by linarith⟩
  have hprod_u_pos : 0 < sin d * sin (u / 2) := mul_pos hsin_d_pos hsin_u_div2_pos
  have hprod_v_pos : 0 < sin d * sin (v / 2) := mul_pos hsin_d_pos hsin_v_div2_pos
  have hprod_u_lt_one : sin d * sin (u / 2) < 1 := by
    have : sin (u / 2) ≤ 1 := Real.sin_le_one _
    nlinarith
  have hprod_v_lt_one : sin d * sin (v / 2) < 1 := by
    have : sin (v / 2) ≤ 1 := Real.sin_le_one _
    nlinarith
  have hebase_u_lower : 0 ≤ ebase d u := by
    dsimp [ebase]
    have h : 0 < arcsin (sin d * sin (u / 2)) :=
      (Real.arcsin_pos.mpr hprod_u_pos)
    nlinarith
  have hebase_u_upper : ebase d u ≤ π := by
    dsimp [ebase]
    have h : arcsin (sin d * sin (u / 2)) < π / 2 :=
      (Real.arcsin_lt_pi_div_two.mpr hprod_u_lt_one)
    nlinarith
  have hebase_v_lower : 0 ≤ ebase d v := by
    dsimp [ebase]
    have h : 0 < arcsin (sin d * sin (v / 2)) :=
      (Real.arcsin_pos.mpr hprod_v_pos)
    nlinarith
  have hebase_v_upper : ebase d v ≤ π := by
    dsimp [ebase]
    have h : arcsin (sin d * sin (v / 2)) < π / 2 :=
      (Real.arcsin_lt_pi_div_two.mpr hprod_v_lt_one)
    nlinarith
  have hebase_u_mem : ebase d u ∈ Set.Icc 0 π :=
    Set.mem_Icc.mpr ⟨hebase_u_lower, hebase_u_upper⟩
  have hebase_v_mem : ebase d v ∈ Set.Icc 0 π :=
    Set.mem_Icc.mpr ⟨hebase_v_lower, hebase_v_upper⟩
  have hmono_ebase : MonotoneOn (ebase d) (Set.Ioc 0 π) :=
    (ebase_strictMonoOn d ⟨hd0, hd1⟩).monotoneOn
  have hebase_le : ebase d u ≤ ebase d v :=
    hmono_ebase hu hv huv
  have hanti_eta : StrictAntiOn (fun g => eta g a b) (Set.Icc 0 π) :=
    eta_strictAntiOn_g a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
  have hanti_eta_anti : AntitoneOn (fun g => eta g a b) (Set.Icc 0 π) :=
    hanti_eta.antitoneOn
  have heta_le : eta (ebase d v) a b ≤ eta (ebase d u) a b :=
    hanti_eta_anti hebase_u_mem hebase_v_mem hebase_le
  dsimp [gam]
  exact Real.arccos_le_arccos heta_le

theorem decDir_sound {R : Rnd} (hR : R.Sound) {lo hi d : ℝ}
    {BX X D : Iv} (Y : ℝ → ℝ) (hlo : 0 < lo) (hd : D.Mem d) (hd0 : 0 < d ∧ d < π / 2)
    (hbx : ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → BX.Mem (bangle d u + Y u))
    (hx : ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π → X.Mem (Y u))
    (hdir : decDir R (Iv.ofReal lo hi) BX X D = -1) :
    ∀ u ∈ Set.Icc lo (min hi π), 0 < Y u → Y u < π →
      0 ≤ cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
  intro u hu hYpos hYlt
  have hu_ge_lo : lo ≤ u := hu.1
  have hu_le_min : u ≤ min hi π := hu.2
  have hu_le_hi : u ≤ hi := le_trans hu_le_min (min_le_left hi π)
  have hu_le_pi : u ≤ π := le_trans hu_le_min (min_le_right hi π)
  have hu_pos : 0 < u := lt_of_lt_of_le hlo hu_ge_lo
  have hdpos : 0 < d := hd0.1
  have hdlt : d < π / 2 := hd0.2
  have hcos_d_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hdlt⟩
  unfold decDir at hdir
  split_ifs at hdir with hcase1
  · -- hcase1 : Fl.le (Iv.ofReal lo hi).hi (.ofReal R.piLo) ∧ Fl.le BX.hi (.ofReal R.piLo)
    rcases hcase1 with ⟨hhi_le_piLo, hBXhi_le_piLo⟩
    have hhi_le_RpiLo : hi ≤ R.piLo := by
      simpa [Iv.ofReal, Fl.ofReal_le_ofReal] using hhi_le_piLo
    have hRpiLo_le_pi : R.piLo ≤ π := hR.piLo
    have hu_le_RpiLo : u ≤ R.piLo := le_trans hu_le_hi hhi_le_RpiLo
    have hsum_le_pi : bangle d u + Y u ≤ π := by
      have hBXmem : BX.Mem (bangle d u + Y u) := hbx u hu hYpos hYlt
      rcases hBXmem with ⟨hBXlo, hBXhi⟩
      have hle : Fl.le (.ofReal (bangle d u + Y u)) (.ofReal R.piLo) :=
        Fl.le_trans hBXhi hBXhi_le_piLo
      have hBXhi' : bangle d u + Y u ≤ R.piLo := by
        rwa [Fl.ofReal_le_ofReal] at hle
      exact le_trans hBXhi' hRpiLo_le_pi
    by_cases hu_eq_pi : u = π
    · subst hu_eq_pi
      have h_target_eq : cos d * sin (π / 2) + cot (Y π) * cos (π / 2) = cos d := by
        simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.cot_eq_cos_div_sin]
      rw [h_target_eq]
      exact hcos_d_pos.le
    · have hu_lt_pi : u < π := lt_of_le_of_ne hu_le_pi hu_eq_pi
      have hbangle_pos : 0 < bangle d u := by
        have hcos_u2_pos : 0 < cos (u / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
        have hsin_u2_pos : 0 < sin (u / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have harg_pos : 0 < cos (u / 2) / (cos d * sin (u / 2)) :=
          div_pos hcos_u2_pos (mul_pos hcos_d_pos hsin_u2_pos)
        rw [bangle]
        exact Real.arctan_pos.mpr harg_pos
      have hsum_nonneg : 0 ≤ bangle d u + Y u := by linarith
      have hsin_sum_nonneg : 0 ≤ sin (bangle d u + Y u) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hsum_nonneg hsum_le_pi
      have hcos_u2_pos : 0 < cos (u / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hsin_bangle_pos : 0 < sin (bangle d u) := by
        have hbangle_lt_pi_div_two : bangle d u < π / 2 := Real.arctan_lt_pi_div_two _
        have hbangle_lt_pi : bangle d u < π := by linarith
        exact Real.sin_pos_of_pos_of_lt_pi hbangle_pos hbangle_lt_pi
      have hsin_Y_pos : 0 < sin (Y u) := Real.sin_pos_of_pos_of_lt_pi hYpos hYlt
      have h_fan_eq : cos d * sin (u / 2) + cot (Y u) * cos (u / 2) =
          cos (u / 2) * sin (bangle d u + Y u) / (sin (bangle d u) * sin (Y u)) :=
        fan_sign_identity d u (Y u) hd0 ⟨hu_pos, hu_lt_pi⟩ ⟨hYpos, hYlt⟩
      rw [h_fan_eq]
      refine div_nonneg ?_ ?_
      · exact mul_nonneg hcos_u2_pos.le hsin_sum_nonneg
      · exact mul_nonneg hsin_bangle_pos.le hsin_Y_pos.le
  · -- hcase1 : ¬ (Fl.le (Iv.ofReal lo hi).hi (.ofReal R.piLo) ∧ Fl.le BX.hi (.ofReal R.piLo))
    simp at hdir
    rcases hdir with ⟨hsable, hlt⟩
    -- hlt : Fl.lt (.ofReal 0) s.lo
    -- s.Usable : Fl.le s.lo s.hi
    -- We'll show s.Mem of the target value, and s.lo > 0, so the value ≥ 0
    let s := R.add (R.mul (R.cos D) (R.sin (R.scale (Iv.ofReal lo hi) 0.5)))
                 (R.mul (R.div (R.cos X) (R.sin X)) (R.cos (R.scale (Iv.ofReal lo hi) 0.5)))
    have hmem_u_half : (Iv.ofReal lo hi).Mem u := by
      rw [Iv.mem_ofReal]
      exact ⟨hu_ge_lo, hu_le_hi⟩
    have hmem_h : (R.scale (Iv.ofReal lo hi) 0.5).Mem (u * 0.5) := by
      dsimp [Rnd.scale]
      exact hR.mul (Iv.ofReal lo hi) (Iv.pt (.ofReal 0.5)) u 0.5 hmem_u_half (Iv.mem_pt (x := 0.5))
    have hmem_sin_h : (R.sin (R.scale (Iv.ofReal lo hi) 0.5)).Mem (sin (u * 0.5)) :=
      hR.sin (R.scale (Iv.ofReal lo hi) 0.5) (u * 0.5) hmem_h
    have hmem_cos_h : (R.cos (R.scale (Iv.ofReal lo hi) 0.5)).Mem (cos (u * 0.5)) :=
      hR.cos (R.scale (Iv.ofReal lo hi) 0.5) (u * 0.5) hmem_h
    have hcos_D_mem : (R.cos D).Mem (cos d) := hR.cos D d hd
    have hmem_mul1 : (R.mul (R.cos D) (R.sin (R.scale (Iv.ofReal lo hi) 0.5))).Mem
        (cos d * sin (u * 0.5)) :=
      hR.mul (R.cos D) (R.sin (R.scale (Iv.ofReal lo hi) 0.5)) (cos d) (sin (u * 0.5))
        hcos_D_mem hmem_sin_h
    have hXmem : X.Mem (Y u) := hx u hu hYpos hYlt
    have hcos_X_mem : (R.cos X).Mem (cos (Y u)) := hR.cos X (Y u) hXmem
    have hsin_X_mem : (R.sin X).Mem (sin (Y u)) := hR.sin X (Y u) hXmem
    have hsin_Y_ne_zero : sin (Y u) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hYpos hYlt)
    have hmem_div : (R.div (R.cos X) (R.sin X)).Mem (cos (Y u) / sin (Y u)) :=
      hR.div (R.cos X) (R.sin X) (cos (Y u)) (sin (Y u)) hcos_X_mem hsin_X_mem hsin_Y_ne_zero
    have hmem_mul2 : (R.mul (R.div (R.cos X) (R.sin X)) (R.cos (R.scale (Iv.ofReal lo hi) 0.5))).Mem
        ((cos (Y u) / sin (Y u)) * cos (u * 0.5)) :=
      hR.mul (R.div (R.cos X) (R.sin X)) (R.cos (R.scale (Iv.ofReal lo hi) 0.5))
        (cos (Y u) / sin (Y u)) (cos (u * 0.5))
        hmem_div hmem_cos_h
    have hmem_s : s.Mem (cos d * sin (u * 0.5) + (cos (Y u) / sin (Y u)) * cos (u * 0.5)) :=
      hR.add (R.mul (R.cos D) (R.sin (R.scale (Iv.ofReal lo hi) 0.5)))
        (R.mul (R.div (R.cos X) (R.sin X)) (R.cos (R.scale (Iv.ofReal lo hi) 0.5)))
        (cos d * sin (u * 0.5)) ((cos (Y u) / sin (Y u)) * cos (u * 0.5))
        hmem_mul1 hmem_mul2
    rcases hmem_s with ⟨hslo, hshi⟩
    -- hslo : Fl.le s.lo (.ofReal (cos d * sin (u * 0.5) + (cos (Y u) / sin (Y u)) * cos (u * 0.5)))
    -- hlt : Fl.lt (.ofReal 0) s.lo
    -- From Fl.lt we get Fl.le, then use eq_ofReal_toReal to relate s.lo to s.lo.toReal
    have hzero_le_slo : Fl.le (.ofReal (0 : ℝ)) s.lo := Fl.le_of_lt hlt
    have hzero_le_slo_toReal : 0 ≤ s.lo.toReal :=
      (Fl.le_ofReal_toReal hzero_le_slo hslo).1
    have h_eq_slo : s.lo = Fl.ofReal (s.lo.toReal) :=
      Fl.eq_ofReal_toReal hzero_le_slo hslo
    -- Now from hlt and h_eq_slo, we get Fl.lt (.ofReal 0) (Fl.ofReal (s.lo.toReal))
    -- which by Fl.ofReal_lt_ofReal gives 0 < s.lo.toReal
    have hzero_lt_slo_toReal : 0 < s.lo.toReal := by
      rw [h_eq_slo] at hlt
      -- hlt : Fl.lt (.ofReal 0) (Fl.ofReal (s.lo.toReal))
      rwa [Fl.ofReal_lt_ofReal] at hlt
    have h_slo_toReal_le_v : s.lo.toReal ≤ cos d * sin (u * 0.5) + (cos (Y u) / sin (Y u)) * cos (u * 0.5) :=
      (Fl.le_ofReal_toReal hzero_le_slo hslo).2
    have h_target_nonneg : 0 ≤ cos d * sin (u * 0.5) + (cos (Y u) / sin (Y u)) * cos (u * 0.5) := by
      linarith
    have h_eq : cos d * sin (u * 0.5) + (cos (Y u) / sin (Y u)) * cos (u * 0.5) =
        cos d * sin (u / 2) + cot (Y u) * cos (u / 2) := by
      rw [Real.cot_eq_cos_div_sin]
      have h_half : u * 0.5 = u / 2 := by ring
      rw [h_half]
    rw [← h_eq]
    exact h_target_nonneg

theorem cornerEnds_spec {R : Rnd} (hR : R.Sound) {lo hi t : ℝ}
    (ht : lo ≤ t ∧ t ≤ min hi π) :
    (∃ w, lo ≤ w ∧ w ≤ t ∧ (cornerEnds R (Iv.ofReal lo hi)).1.Mem w) ∧
      ∃ w, t ≤ w ∧ w ≤ min hi π ∧ (cornerEnds R (Iv.ofReal lo hi)).2.Mem w := by
  rcases ht with ⟨ht_left, ht_right⟩
  have ht_le_hi : t ≤ hi := le_trans ht_right (min_le_left _ _)
  have ht_le_pi : t ≤ π := le_trans ht_right (min_le_right _ _)
  have hlo_le_hi : lo ≤ hi := le_trans ht_left ht_le_hi
  have hlo_le_pi : lo ≤ π := le_trans ht_left ht_le_pi
  have hmin_le_hi : min hi π ≤ hi := min_le_left _ _
  have hmin_le_pi : min hi π ≤ π := min_le_right _ _
  delta Iv.ofReal
  unfold cornerEnds
  dsimp
  constructor
  · by_cases h1 : Fl.le (R.addUp (Fl.ofReal lo) (Fl.ofReal hi)) (Fl.ofReal (2 * R.piLo))
    · rw [if_pos h1]
      exact ⟨lo, le_rfl, ht_left, Iv.mem_pt⟩
    · rw [if_neg h1]
      have hmem : (Iv.ofReal lo hi).Mem t := by
        rw [Iv.mem_ofReal]
        exact ⟨ht_left, ht_le_hi⟩
      exact ⟨t, ht_left, le_rfl, hmem⟩
  · by_cases h2 : Fl.le (Fl.ofReal hi) (Fl.ofReal R.piLo)
    · rw [if_pos h2]
      have hhi_le_RpiLo : hi ≤ R.piLo := by
        simpa [Fl.ofReal_le_ofReal] using h2
      have hhi_le_pi : hi ≤ π := le_trans hhi_le_RpiLo hR.piLo
      have hhi_le_min : hi ≤ min hi π := le_min (le_refl hi) hhi_le_pi
      exact ⟨hi, ht_le_hi, hhi_le_min, Iv.mem_pt⟩
    · rw [if_neg h2]
      have hRpiLo_lt_hi : R.piLo < hi := by
        have : ¬ hi ≤ R.piLo := by
          simpa [Fl.ofReal_le_ofReal] using h2
        exact lt_of_not_ge this
      have hmax_le_min : Fl.le (Fl.max (Fl.ofReal lo) (Fl.ofReal R.piLo)) (Fl.ofReal (min hi π)) := by
        apply Fl.max_le
        · simpa [Fl.ofReal_le_ofReal] using le_trans ht_left ht_right
        · have hRpiLo_le_hi : R.piLo ≤ hi := le_of_lt hRpiLo_lt_hi
          have hRpiLo_le_min : R.piLo ≤ min hi π := le_min hRpiLo_le_hi hR.piLo
          simpa [Fl.ofReal_le_ofReal] using hRpiLo_le_min
      have hmin_le_hi' : Fl.le (Fl.ofReal (min hi π)) (Fl.ofReal hi) := by
        simpa [Fl.ofReal_le_ofReal] using hmin_le_hi
      have hmem : ((⟨Fl.max (Fl.ofReal lo) (Fl.ofReal R.piLo), Fl.ofReal hi⟩ : Iv)).Mem (min hi π) :=
        ⟨hmax_le_min, hmin_le_hi'⟩
      exact ⟨min hi π, ht_right, le_rfl, hmem⟩

theorem cornerEnds_forms (R : Rnd) (lo hi : ℝ) :
    ((cornerEnds R (Iv.ofReal lo hi)).1 = Iv.ofReal lo lo ∨
        (cornerEnds R (Iv.ofReal lo hi)).1 = Iv.ofReal lo hi) ∧
      ((cornerEnds R (Iv.ofReal lo hi)).2 = Iv.ofReal hi hi ∨
        (cornerEnds R (Iv.ofReal lo hi)).2 = Iv.ofReal (max lo R.piLo) hi) := by
  unfold cornerEnds
  simp [Iv.ofReal, Iv.pt, Fl.max, Fl.ofReal]
  constructor
  · split_ifs with h <;> simp [h]
  · split_ifs with h
    · simp [h]
    · simp [h]
      right
      norm_cast

theorem monoBounds_mem {K : ℕ} (inp : Fin K → Iv) (ends : Fin K → Iv × Iv)
    (dirs : Fin 3 → Fin K → ℤ) (eval : (Fin K → Iv) → Fin 3 → Iv) (k : Fin 3)
    (C : (Fin K → ℝ) → ℝ) (lo top u₀ : Fin K → ℝ) (hu₀ : ∀ j, lo j ≤ u₀ j ∧ u₀ j ≤ top j)
    (heval : ∀ (X : Fin K → Iv) (x : Fin K → ℝ),
      (∀ j, X j = inp j ∨ X j = (ends j).1 ∨ X j = (ends j).2) → (∀ j, (X j).Mem (x j)) →
        (∀ j, lo j ≤ x j ∧ x j ≤ top j) → (eval X k).Mem (C x))
    (hinp : ∀ j t, lo j ≤ t → t ≤ top j → (inp j).Mem t)
    (hend1 : ∀ j t, lo j ≤ t → t ≤ top j → ∃ w, lo j ≤ w ∧ w ≤ t ∧ (ends j).1.Mem w)
    (hend2 : ∀ j t, lo j ≤ t → t ≤ top j → ∃ w, t ≤ w ∧ w ≤ top j ∧ (ends j).2.Mem w)
    (hmono : ∀ j, dirs k j = 1 → ∀ x : Fin K → ℝ, (∀ i, lo i ≤ x i ∧ x i ≤ top i) →
      MonotoneOn (fun t => C (Function.update x j t)) (Set.Icc (lo j) (top j)))
    (hanti : ∀ j, dirs k j = -1 → ∀ x : Fin K → ℝ, (∀ i, lo i ≤ x i ∧ x i ≤ top i) →
      AntitoneOn (fun t => C (Function.update x j t)) (Set.Icc (lo j) (top j))) :
    (monoBounds inp ends dirs eval k).Mem (C u₀) := by
  let sel := fun (low : Bool) (j : Fin K) =>
    if dirs k j = 1 then (if low then (ends j).1 else (ends j).2)
    else if dirs k j = -1 then (if low then (ends j).2 else (ends j).1)
    else inp j
  let P : Finset (Fin K) → Prop := fun s =>
    ∃ w : Fin K → ℝ, (∀ j, lo j ≤ w j ∧ w j ≤ top j) ∧ (∀ j ∈ s, (sel true j).Mem (w j)) ∧ C w ≤ C u₀
  have h_base : P ∅ := by
    refine ⟨u₀, hu₀, ?_, le_rfl⟩
    intro j hj
    simp at hj
  have h_step : ∀ (j : Fin K) (s : Finset (Fin K)), j ∉ s → P s → P (insert j s) := by
    intro j s hj ih
    rcases ih with ⟨w, hw_range, hw_mem, hw_le⟩
    by_cases hdir1 : dirs k j = 1
    · rcases hend1 j (w j) (hw_range j).1 (hw_range j).2 with ⟨v, hv_lo, hv_le, hv_mem⟩
      have hv_le_top : v ≤ top j := hv_le.trans (hw_range j).2
      have hsel : (sel true j) = (ends j).1 := by
        dsimp [sel]; rw [hdir1]; simp
      have hv_mem' : (sel true j).Mem v := by rw [hsel]; exact hv_mem
      have hmono_j := hmono j hdir1 w hw_range
      have hv_in_Icc : v ∈ Set.Icc (lo j) (top j) := ⟨hv_lo, hv_le_top⟩
      have hw_in_Icc : w j ∈ Set.Icc (lo j) (top j) := ⟨(hw_range j).1, (hw_range j).2⟩
      have h_le : C (Function.update w j v) ≤ C w := by
        have := hmono_j hv_in_Icc hw_in_Icc hv_le
        simpa [Function.update_self] using this
      have h_range : ∀ i, lo i ≤ (Function.update w j v) i ∧ (Function.update w j v) i ≤ top i := by
        intro i
        by_cases hi : i = j
        · subst hi; simp [hv_lo, hv_le_top]
        · simp [Function.update_of_ne hi, hw_range i]
      have h_mem : ∀ i ∈ insert j s, (sel true i).Mem ((Function.update w j v) i) := by
        intro i hi
        rcases Finset.mem_insert.mp hi with (rfl | hi_s)
        · simpa using hv_mem'
        · have hne : i ≠ j := by intro heq; subst heq; exact hj hi_s
          have hmem_i := hw_mem i hi_s
          simpa [Function.update_of_ne hne] using hmem_i
      exact ⟨Function.update w j v, h_range, h_mem, le_trans h_le hw_le⟩
    · by_cases hdir_neg1 : dirs k j = -1
      · rcases hend2 j (w j) (hw_range j).1 (hw_range j).2 with ⟨v, hv_lo, hv_le, hv_mem⟩
        have hv_ge_lo : lo j ≤ v := (hw_range j).1.trans hv_lo
        have hsel : (sel true j) = (ends j).2 := by
          dsimp [sel]; rw [hdir_neg1]; simp
        have hv_mem' : (sel true j).Mem v := by rw [hsel]; exact hv_mem
        have hanti_j := hanti j hdir_neg1 w hw_range
        have hv_in_Icc : v ∈ Set.Icc (lo j) (top j) := ⟨hv_ge_lo, hv_le⟩
        have hw_in_Icc : w j ∈ Set.Icc (lo j) (top j) := ⟨(hw_range j).1, (hw_range j).2⟩
        have h_le : C (Function.update w j v) ≤ C w := by
          have := hanti_j hw_in_Icc hv_in_Icc hv_lo
          simpa [Function.update_self] using this
        have h_range : ∀ i, lo i ≤ (Function.update w j v) i ∧ (Function.update w j v) i ≤ top i := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [hv_ge_lo, hv_le]
          · simp [Function.update_of_ne hi, hw_range i]
        have h_mem : ∀ i ∈ insert j s, (sel true i).Mem ((Function.update w j v) i) := by
          intro i hi
          rcases Finset.mem_insert.mp hi with (rfl | hi_s)
          · simpa using hv_mem'
          · have hne : i ≠ j := by intro heq; subst heq; exact hj hi_s
            have hmem_i := hw_mem i hi_s
            simpa [Function.update_of_ne hne] using hmem_i
        exact ⟨Function.update w j v, h_range, h_mem, le_trans h_le hw_le⟩
      · have hsel : (sel true j) = inp j := by
          dsimp [sel]; simp [hdir1, hdir_neg1]
        have hinp_mem : (inp j).Mem (w j) := hinp j (w j) (hw_range j).1 (hw_range j).2
        have hinp_mem' : (sel true j).Mem (w j) := by rw [hsel]; exact hinp_mem
        have h_mem : ∀ i ∈ insert j s, (sel true i).Mem (w i) := by
          intro i hi
          rcases Finset.mem_insert.mp hi with (rfl | hi_s)
          · exact hinp_mem'
          · exact hw_mem i hi_s
        exact ⟨w, hw_range, h_mem, hw_le⟩
  have h_univ : P Finset.univ := Finset.induction_on Finset.univ h_base h_step
  rcases h_univ with ⟨w_low, hw_low_range, hw_low_mem, hw_low_le⟩
  have h_sel_true_cases : ∀ j, (sel true j) = inp j ∨ (sel true j) = (ends j).1 ∨ (sel true j) = (ends j).2 := by
    intro j
    dsimp [sel]
    by_cases h1 : dirs k j = 1
    · rw [h1]; simp
    · by_cases h_neg1 : dirs k j = -1
      · rw [h_neg1]; simp
      · simp [h1, h_neg1]
  have h_low_eval := heval (sel true) w_low (h_sel_true_cases) ?_ hw_low_range
  · have h_lo : Fl.le ((eval (sel true) k).lo) (Fl.ofReal (C u₀)) := by
      have h_lo' := h_low_eval.1
      have h_ofReal : Fl.le (Fl.ofReal (C w_low)) (Fl.ofReal (C u₀)) :=
        Fl.ofReal_le_ofReal.mpr hw_low_le
      exact Fl.le_trans h_lo' h_ofReal
    let Q : Finset (Fin K) → Prop := fun s =>
      ∃ w : Fin K → ℝ, (∀ j, lo j ≤ w j ∧ w j ≤ top j) ∧ (∀ j ∈ s, (sel false j).Mem (w j)) ∧ C u₀ ≤ C w
    have h_base_Q : Q ∅ := by
      refine ⟨u₀, hu₀, ?_, le_rfl⟩
      intro j hj; simp at hj
    have h_step_Q : ∀ (j : Fin K) (s : Finset (Fin K)), j ∉ s → Q s → Q (insert j s) := by
      intro j s hj ih
      rcases ih with ⟨w, hw_range, hw_mem, hw_le⟩
      by_cases hdir1 : dirs k j = 1
      · rcases hend2 j (w j) (hw_range j).1 (hw_range j).2 with ⟨v, hv_lo, hv_le, hv_mem⟩
        -- hv_lo: w j ≤ v, hv_le: v ≤ top j
        have hlo_v : lo j ≤ v := (hw_range j).1.trans hv_lo
        have hsel : (sel false j) = (ends j).2 := by
          dsimp [sel]; rw [hdir1]; simp
        have hv_mem' : (sel false j).Mem v := by rw [hsel]; exact hv_mem
        have hmono_j := hmono j hdir1 w hw_range
        have hv_in_Icc : v ∈ Set.Icc (lo j) (top j) := ⟨hlo_v, hv_le⟩
        have hw_in_Icc : w j ∈ Set.Icc (lo j) (top j) := ⟨(hw_range j).1, (hw_range j).2⟩
        have h_le : C w ≤ C (Function.update w j v) := by
          have := hmono_j hw_in_Icc hv_in_Icc hv_lo
          simpa [Function.update_self] using this
        have h_range : ∀ i, lo i ≤ (Function.update w j v) i ∧ (Function.update w j v) i ≤ top i := by
          intro i
          by_cases hi : i = j
          · subst hi; simp [hlo_v, hv_le]
          · simp [Function.update_of_ne hi, hw_range i]
        have h_mem : ∀ i ∈ insert j s, (sel false i).Mem ((Function.update w j v) i) := by
          intro i hi
          rcases Finset.mem_insert.mp hi with (rfl | hi_s)
          · simpa using hv_mem'
          · have hne : i ≠ j := by intro heq; subst heq; exact hj hi_s
            have hmem_i := hw_mem i hi_s
            simpa [Function.update_of_ne hne] using hmem_i
        exact ⟨Function.update w j v, h_range, h_mem, le_trans hw_le h_le⟩
      · by_cases hdir_neg1 : dirs k j = -1
        · rcases hend1 j (w j) (hw_range j).1 (hw_range j).2 with ⟨v, hv_lo, hv_le, hv_mem⟩
          -- hv_lo: lo j ≤ v, hv_le: v ≤ w j
          have hle_top : v ≤ top j := hv_le.trans (hw_range j).2
          have hsel : (sel false j) = (ends j).1 := by
            dsimp [sel]; rw [hdir_neg1]; simp
          have hv_mem' : (sel false j).Mem v := by rw [hsel]; exact hv_mem
          have hanti_j := hanti j hdir_neg1 w hw_range
          have hv_in_Icc : v ∈ Set.Icc (lo j) (top j) := ⟨hv_lo, hle_top⟩
          have hw_in_Icc : w j ∈ Set.Icc (lo j) (top j) := ⟨(hw_range j).1, (hw_range j).2⟩
          have h_le : C w ≤ C (Function.update w j v) := by
            have := hanti_j hv_in_Icc hw_in_Icc hv_le
            simpa [Function.update_self] using this
          have h_range : ∀ i, lo i ≤ (Function.update w j v) i ∧ (Function.update w j v) i ≤ top i := by
            intro i
            by_cases hi : i = j
            · subst hi; simp [hv_lo, hle_top]
            · simp [Function.update_of_ne hi, hw_range i]
          have h_mem : ∀ i ∈ insert j s, (sel false i).Mem ((Function.update w j v) i) := by
            intro i hi
            rcases Finset.mem_insert.mp hi with (rfl | hi_s)
            · simpa using hv_mem'
            · have hne : i ≠ j := by intro heq; subst heq; exact hj hi_s
              have hmem_i := hw_mem i hi_s
              simpa [Function.update_of_ne hne] using hmem_i
          exact ⟨Function.update w j v, h_range, h_mem, le_trans hw_le h_le⟩
        · have hsel : (sel false j) = inp j := by
            dsimp [sel]; simp [hdir1, hdir_neg1]
          have hinp_mem : (inp j).Mem (w j) := hinp j (w j) (hw_range j).1 (hw_range j).2
          have hinp_mem' : (sel false j).Mem (w j) := by rw [hsel]; exact hinp_mem
          have h_mem : ∀ i ∈ insert j s, (sel false i).Mem (w i) := by
            intro i hi
            rcases Finset.mem_insert.mp hi with (rfl | hi_s)
            · exact hinp_mem'
            · exact hw_mem i hi_s
          exact ⟨w, hw_range, h_mem, hw_le⟩
    have h_univ_Q : Q Finset.univ := Finset.induction_on Finset.univ h_base_Q h_step_Q
    rcases h_univ_Q with ⟨w_up, hw_up_range, hw_up_mem, hw_up_le⟩
    have h_sel_false_cases : ∀ j, (sel false j) = inp j ∨ (sel false j) = (ends j).1 ∨ (sel false j) = (ends j).2 := by
      intro j
      dsimp [sel]
      by_cases h1 : dirs k j = 1
      · rw [h1]; simp
      · by_cases h_neg1 : dirs k j = -1
        · rw [h_neg1]; simp
        · simp [h1, h_neg1]
    have h_up_eval := heval (sel false) w_up (h_sel_false_cases) ?_ hw_up_range
    · have h_up : Fl.le (Fl.ofReal (C u₀)) ((eval (sel false) k).hi) := by
        have h_up' := h_up_eval.2
        have h_ofReal : Fl.le (Fl.ofReal (C u₀)) (Fl.ofReal (C w_up)) :=
          Fl.ofReal_le_ofReal.mpr hw_up_le
        exact Fl.le_trans h_ofReal h_up'
      have h_monoBounds_eq : monoBounds inp ends dirs eval k = ⟨(eval (sel true) k).lo, (eval (sel false) k).hi⟩ := rfl
      rw [h_monoBounds_eq]
      exact And.intro h_lo h_up
    · intro j
      apply hw_up_mem j
      exact Finset.mem_univ j
  · intro j
    apply hw_low_mem j
    exact Finset.mem_univ j

end Tammes15.Contractors
