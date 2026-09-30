import Mathlib

/-!
# Certified values of `cos`, `sin` and `arccos` at explicit points

Taylor polynomials of `cos` and `sin` at `0` with the Lagrange remainder (every derivative of `cos`
and `sin` is bounded by `1` in absolute value, so the remainder after the terms of degree below `m`
is at most `|x| ^ m / m!` at every real `x`), their one-sided forms at nonnegative points, the
transfer to points `q * π` through rational bounds of `π` (`Real.pi_gt_d20`, `Real.pi_lt_d20` and
the coarser ones of Mathlib) and the monotonicity of `cos` and `sin`, and the comparison of `arccos`
with a point through `cos`. These give the numerical margins of Proposition onehex in its inscribed
polygon form and the bound `dlo < ψ*` (paper, Proposition onehex and the choice of `dlo`).

A value such as `c ≤ cos (q * π)` for explicit rationals `q`, `c` is proved by `le_cos_mul_pi` with
`p = 3.14159265358979323847` (`Real.pi_lt_d20`) and a rational inequality closed by `norm_num`.
-/

open Real Finset
open scoped ContDiff

namespace Tammes15.Numerics

/-- The Taylor polynomial of `cos` at `0` made of its terms of degree below `2 n`. -/
noncomputable def cosT (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- The Taylor polynomial of `sin` at `0` made of its terms of degree below `2 n`. -/
noncomputable def sinT (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

/-! ## Taylor remainders -/

/-- The Lagrange remainder for a smooth function all of whose derivatives are bounded by `1`. -/
theorem abs_sub_taylor_le_of_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ (i : ℕ) (y : ℝ), |iteratedDeriv i f y| ≤ 1) (x : ℝ) (m : ℕ) :
    |f x - ∑ i ∈ range m, iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ)| ≤
      |x| ^ m / (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with (rfl | hm)
  · -- m = 0: the sum is empty, RHS = 1, and hb 0 x gives |f x| ≤ 1
    have h := hb 0 x
    simpa [iteratedDeriv_zero] using h
  · rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
    by_cases hx0 : x = 0
    · -- x = 0: every term with i ≥ 1 vanishes, the i=0 term is f 0
      subst x
      have hsum : (∑ i ∈ range (k + 1), iteratedDeriv i f 0 * (0 : ℝ) ^ i / (i.factorial : ℝ)) = f 0 := by
        calc
          (∑ i ∈ range (k + 1), iteratedDeriv i f 0 * (0 : ℝ) ^ i / (i.factorial : ℝ))
              = iteratedDeriv 0 f 0 * (0 : ℝ) ^ 0 / ((0 : ℕ).factorial : ℝ) := by
            refine Finset.sum_eq_single 0 (fun i hi hine => ?_) (fun h => ?_)
            · rw [zero_pow hine, mul_zero, zero_div]
            · exfalso; exact h (Finset.mem_range.2 (Nat.zero_lt_succ _))
          _ = f 0 := by simp [iteratedDeriv_zero]
      rw [hsum]
      simp [zero_pow (Nat.succ_ne_zero k)]
    · -- x ≠ 0: use Taylor's theorem with Lagrange remainder
      have hx_ne : (0 : ℝ) ≠ x := by intro h; exact hx0 h.symm
      have h_contDiffOn : ContDiffOn ℝ (↑k + 1) f (Set.uIcc (0 : ℝ) x) :=
        hf.contDiffOn.of_le (by simp)
      rcases taylor_mean_remainder_lagrange_iteratedDeriv hx_ne h_contDiffOn with ⟨y, hy, h_eq⟩
      -- h_eq: f x - taylorWithinEval f k (Set.uIcc 0 x) 0 x = iteratedDeriv (k+1) f y * (x - 0)^(k+1) / (k+1)!
      have h_taylor_eq : taylorWithinEval f k (Set.uIcc (0 : ℝ) x) 0 x =
          ∑ i ∈ range (k + 1), iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ) := by
        rw [taylor_within_apply]
        simp_rw [sub_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        have h_contDiffAt : ContDiffAt ℝ j f 0 :=
          (hf.contDiffAt (x := 0)).of_le (by simp)
        have h_mem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x := Set.left_mem_uIcc
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx_ne) h_contDiffAt h_mem]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      rw [h_taylor_eq] at h_eq
      -- h_eq: f x - (sum) = iteratedDeriv (k+1) f y * (x - 0)^(k+1) / (k+1)!
      -- simplify (x - 0) to x
      have h_eq' : f x - ∑ i ∈ range (k + 1), iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ) =
          iteratedDeriv (k + 1) f y * x ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        simpa [sub_zero] using h_eq
      have h_abs_eq : |f x - ∑ i ∈ range (k + 1), iteratedDeriv i f 0 * x ^ i / (i.factorial : ℝ)| =
          |iteratedDeriv (k + 1) f y * x ^ (k + 1) / ((k + 1).factorial : ℝ)| := by rw [h_eq']
      rw [h_abs_eq]
      have h_num : |iteratedDeriv (k + 1) f y| * |x| ^ (k + 1) ≤ 1 * |x| ^ (k + 1) :=
        mul_le_mul_of_nonneg_right (hb (k + 1) y) (by positivity)
      have h_den : 0 ≤ ((k + 1).factorial : ℝ) := by positivity
      have h_fact_pos : 0 < ((k + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      calc
        |iteratedDeriv (k + 1) f y * x ^ (k + 1) / ((k + 1).factorial : ℝ)|
            = |iteratedDeriv (k + 1) f y| * |x ^ (k + 1)| / |((k + 1).factorial : ℝ)| := by
          rw [abs_div, abs_mul]
        _ = |iteratedDeriv (k + 1) f y| * |x| ^ (k + 1) / ((k + 1).factorial : ℝ) := by
          simp [abs_pow, abs_of_pos h_fact_pos]
        _ ≤ 1 * |x| ^ (k + 1) / ((k + 1).factorial : ℝ) :=
          div_le_div_of_nonneg_right h_num h_den
        _ = |x| ^ (k + 1) / ((k + 1).factorial : ℝ) := by simp

theorem cosT_eq_taylor (n : ℕ) (x : ℝ) :
    cosT n x = ∑ i ∈ range (2 * n), iteratedDeriv i cos 0 * x ^ i / (i.factorial : ℝ) := by
  induction' n with n ih
  · simp [cosT]
  · rw [cosT, Finset.sum_range_succ]
    have hRHS : (∑ i ∈ range (2 * (n + 1)), iteratedDeriv i cos 0 * x ^ i / (i.factorial : ℝ)) =
        (∑ i ∈ range (2 * n), iteratedDeriv i cos 0 * x ^ i / (i.factorial : ℝ)) +
        iteratedDeriv (2 * n) cos 0 * x ^ (2 * n) / ((2 * n).factorial : ℝ) +
        iteratedDeriv (2 * n + 1) cos 0 * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
      rw [show (2 : ℕ) * (n + 1) = 2 * n + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hRHS, ← ih, ← cosT]
    have h_even : iteratedDeriv (2 * n) cos 0 = (-1 : ℝ) ^ n := by
      rw [Real.iteratedDeriv_even_cos n]
      simp [Real.cos_zero]
    have h_odd : iteratedDeriv (2 * n + 1) cos 0 = 0 := by
      rw [Real.iteratedDeriv_odd_cos n]
      simp [Real.sin_zero]
    rw [h_even, h_odd]
    ring

theorem sinT_eq_taylor (n : ℕ) (x : ℝ) :
    sinT n x = ∑ i ∈ range (2 * n + 1), iteratedDeriv i sin 0 * x ^ i / (i.factorial : ℝ) := by
  induction n with
  | zero =>
      simp [sinT, Real.sin_zero]
  | succ n ih =>
      have hsum : (∑ i ∈ range (2 * (n + 1) + 1), iteratedDeriv i sin 0 * x ^ i / (i.factorial : ℝ)) =
          (∑ i ∈ range (2 * n + 1), iteratedDeriv i sin 0 * x ^ i / (i.factorial : ℝ)) +
          iteratedDeriv (2 * n + 1) sin 0 * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
        have hindex : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
        rw [hindex, Finset.sum_range_succ, Finset.sum_range_succ]
        have h_even : iteratedDeriv ((2 * n + 1) + 1) sin 0 = 0 := by
          have : (2 * n + 1) + 1 = 2 * (n + 1) := by ring
          rw [this, Real.iteratedDeriv_even_sin (n + 1)]
          simp [Real.sin_zero]
        rw [h_even]
        simp
      rw [hsum, ← ih]
      have h_odd : iteratedDeriv (2 * n + 1) sin 0 = (-1 : ℝ) ^ n := by
        rw [Real.iteratedDeriv_odd_sin n]
        simp [Real.cos_zero]
      rw [h_odd]
      rw [show sinT (n + 1) x = sinT n x + (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) by
        rw [sinT, sinT, Finset.sum_range_succ]]

theorem abs_cos_sub_cosT_le (n : ℕ) (x : ℝ) :
    |cos x - cosT n x| ≤ |x| ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  rw [cosT_eq_taylor n x]
  exact abs_sub_taylor_le_of_bound cos Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one x (2 * n)

theorem abs_sin_sub_sinT_le (n : ℕ) (x : ℝ) :
    |sin x - sinT n x| ≤ |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  rw [sinT_eq_taylor n x]
  exact abs_sub_taylor_le_of_bound sin Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one x (2 * n + 1)

/-! ## One-sided bounds at a nonnegative point -/

theorem cos_le_of_cosT (n : ℕ) {x c : ℝ} (hx : 0 ≤ x)
    (h : cosT n x + x ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ c) : cos x ≤ c := by
  have h_abs := abs_cos_sub_cosT_le n x
  have h_abs' : |cos x - cosT n x| ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    simpa [abs_of_nonneg hx] using h_abs
  have h_le := (abs_le.mp h_abs').right
  linarith

theorem le_cos_of_cosT (n : ℕ) {x c : ℝ} (hx : 0 ≤ x)
    (h : c ≤ cosT n x - x ^ (2 * n) / ((2 * n).factorial : ℝ)) : c ≤ cos x := by
  have h_abs := abs_cos_sub_cosT_le n x
  have hx_abs : |x| = x := abs_of_nonneg hx
  rw [hx_abs] at h_abs
  have h_le := (abs_le.mp h_abs).left
  linarith

theorem sin_le_of_sinT (n : ℕ) {x c : ℝ} (hx : 0 ≤ x)
    (h : sinT n x + x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ c) : sin x ≤ c := by
  have h_abs := abs_sin_sub_sinT_le n x
  have hx_abs : |x| = x := abs_of_nonneg hx
  rw [hx_abs] at h_abs
  have h_bound : sin x - sinT n x ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    have := abs_le.mp h_abs
    exact this.2
  linarith

theorem le_sin_of_sinT (n : ℕ) {x c : ℝ} (hx : 0 ≤ x)
    (h : c ≤ sinT n x - x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) : c ≤ sin x := by
  have h_abs := abs_sin_sub_sinT_le n x
  have habsx : |x| = x := abs_of_nonneg hx
  have h_abs' : |sin x - sinT n x| ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    simpa [habsx] using h_abs
  have h_bound := abs_le.mp h_abs'
  rcases h_bound with ⟨h_left, h_right⟩
  have h_key : sinT n x - x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ sin x := by
    linarith
  linarith

/-! ## Points `q * π`, through a rational bound `p` of `π` -/

theorem cos_mul_pi_le (n : ℕ) {p q c : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ π) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : cosT n (q * p) + (q * p) ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ c) :
    cos (q * π) ≤ c := by
  have h_nonneg_qp : 0 ≤ q * p := mul_nonneg hq0 hp0
  have hπ_nonneg : 0 ≤ π := by linarith [Real.pi_pos]
  have h_qp_le_qπ : q * p ≤ q * π := mul_le_mul_of_nonneg_left hp hq0
  have h_qπ_le_π : q * π ≤ π := by
    calc
      q * π ≤ 1 * π := mul_le_mul_of_nonneg_right hq1 hπ_nonneg
      _ = π := by ring
  have h_cos_le : cos (q * π) ≤ cos (q * p) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h_nonneg_qp h_qπ_le_π h_qp_le_qπ
  have h_cosT_le : cos (q * p) ≤ c := cos_le_of_cosT n h_nonneg_qp h
  exact le_trans h_cos_le h_cosT_le

theorem le_cos_mul_pi (n : ℕ) {p q c : ℝ} (hp : π ≤ p) (hq0 : 0 ≤ q) (hqp : q * p ≤ 3)
    (h : c ≤ cosT n (q * p) - (q * p) ^ (2 * n) / ((2 * n).factorial : ℝ)) :
    c ≤ cos (q * π) := by
  have hp_pos : 0 < p := by linarith [Real.pi_pos, hp]
  have hx : 0 ≤ q * p := mul_nonneg hq0 hp_pos.le
  have h_c_le_cos_qp : c ≤ cos (q * p) :=
    le_cos_of_cosT n (x := q * p) (c := c) hx h
  have hqπ_nonneg : 0 ≤ q * π := mul_nonneg hq0 Real.pi_pos.le
  have hqp_le_pi : q * p ≤ π := by
    have h3ltpi : (3 : ℝ) < π := Real.pi_gt_three
    linarith
  have hqπ_le_qp : q * π ≤ q * p := mul_le_mul_of_nonneg_left hp hq0
  have hcos_qp_le_cos_qπ : cos (q * p) ≤ cos (q * π) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hqπ_nonneg hqp_le_pi hqπ_le_qp
  exact le_trans h_c_le_cos_qp hcos_qp_le_cos_qπ

theorem sin_mul_pi_le (n : ℕ) {p q c : ℝ} (hp : π ≤ p) (hq0 : 0 ≤ q) (hqp : q * p ≤ 3 / 2)
    (h : sinT n (q * p) + (q * p) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ c) :
    sin (q * π) ≤ c := by
  have hqπ_nonneg : 0 ≤ q * π := mul_nonneg hq0 (by linarith [Real.pi_pos])
  have hqp_nonneg : 0 ≤ q * p := mul_nonneg hq0 (by linarith [Real.pi_pos, hp])
  have hqπ_le_qp : q * π ≤ q * p := mul_le_mul_of_nonneg_left hp hq0
  have hqp_le_pi_div_two : q * p ≤ π / 2 := by
    have h3_lt_pi : (3 : ℝ) < π := Real.pi_gt_three
    linarith
  have hqπ_le_pi_div_two : q * π ≤ π / 2 := by linarith
  have hneg_pi_div_two_le_qπ : -(π / 2) ≤ q * π := by
    have hneg : -(π / 2) ≤ 0 := by linarith [Real.pi_pos]
    linarith
  have h_sin_le : sin (q * π) ≤ sin (q * p) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hneg_pi_div_two_le_qπ hqp_le_pi_div_two hqπ_le_qp
  have h_sinT_le : sin (q * p) ≤ c := sin_le_of_sinT n hqp_nonneg h
  linarith

theorem le_sin_mul_pi (n : ℕ) {p q c : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ π) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2)
    (h : c ≤ sinT n (q * p) - (q * p) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) :
    c ≤ sin (q * π) := by
  have hqp_nonneg : 0 ≤ q * p := mul_nonneg hq0 hp0
  have hqp_le_qπ : q * p ≤ q * π := mul_le_mul_of_nonneg_left hp hq0
  have hqπ_le_pi_div_two : q * π ≤ π / 2 := by
    calc
      q * π ≤ (1/2 : ℝ) * π := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = π / 2 := by ring
  have h_sin_le : sin (q * p) ≤ sin (q * π) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hqπ_le_pi_div_two hqp_le_qπ
  have hc_le_sin_qp : c ≤ sin (q * p) := le_sin_of_sinT n hqp_nonneg h
  linarith

/-! ## `arccos` against a point, through `cos` -/

theorem arccos_lt_of_cos_lt {y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ π) (hy : y ≤ 1) (h : cos c < y) :
    arccos y < c := by
  have hneg : -1 ≤ cos c := Real.neg_one_le_cos c
  have h_arccos_lt : arccos y < arccos (cos c) := Real.arccos_lt_arccos hneg h hy
  have h_arccos_eq : arccos (cos c) = c := Real.arccos_cos hc0 hc
  linarith

theorem arccos_le_of_cos_le {y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ π) (h : cos c ≤ y) :
    arccos y ≤ c := by
  calc
    arccos y ≤ arccos (cos c) := Real.arccos_le_arccos h
    _ = c := Real.arccos_cos hc0 hc

theorem lt_arccos_of_lt_cos {y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ π) (hy : -1 ≤ y) (h : y < cos c) :
    c < arccos y := by
  have hcos_le_one : cos c ≤ 1 := Real.cos_le_one c
  have harccos_eq : arccos (cos c) = c := Real.arccos_cos hc0 hc
  have h_lt : arccos (cos c) < arccos y := Real.arccos_lt_arccos hy h hcos_le_one
  linarith

theorem le_arccos_of_le_cos {y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ π) (h : y ≤ cos c) :
    c ≤ arccos y := by
  have h_eq : arccos (cos c) = c := Real.arccos_cos hc0 hc
  have h_le : arccos (cos c) ≤ arccos y := Real.arccos_le_arccos h
  calc
    c = arccos (cos c) := by rw [h_eq]
    _ ≤ arccos y := h_le

end Tammes15.Numerics
