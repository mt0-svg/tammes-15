import Mathlib

namespace Tammes15.D3Kernel.Kinds

noncomputable def lf_qc (q : ℕ) (c s : ℝ) : ℝ :=
  if q % 4 = 0 then c else if q % 4 = 1 then -s else if q % 4 = 2 then -c else s

noncomputable def lf_qs (q : ℕ) (c s : ℝ) : ℝ :=
  if q % 4 = 0 then s else if q % 4 = 1 then c else if q % 4 = 2 then -s else -c

noncomputable def lf_eta (g e f : ℝ) : ℝ := (Real.cos g - Real.cos e * Real.cos f) / (Real.sin e * Real.sin f)

theorem lf_cos_two_arctan (t : ℝ) : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  field_simp
  ring

theorem lf_sin_two_arctan (t : ℝ) : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
  rw [Real.sin_two_mul, Real.sin_arctan t, Real.cos_arctan t]
  have hpos : 1 + t ^ 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  field_simp [hsqrt, hpos]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)]

theorem lf_cos_quarter (q : ℕ) (x : ℝ) :
    Real.cos (q * (Real.pi / 2) + x) = lf_qc q (Real.cos x) (Real.sin x) := by
  have hq := (Nat.div_add_mod q 4).symm
  have hq' : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) + ((q % 4 : ℕ) : ℝ) := by exact_mod_cast hq
  have hcos_periodic (n : ℕ) (y : ℝ) : Real.cos (y + (n : ℝ) * (2 * Real.pi)) = Real.cos y := by
    simpa [add_comm] using Real.cos_add_nat_mul_two_pi y n
  have hsplit : (q : ℝ) * (Real.pi / 2) + x = ((q % 4 : ℕ) : ℝ) * (Real.pi / 2) + x + ((q / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hq']
    ring
  have hcos_eq : Real.cos ((q : ℝ) * (Real.pi / 2) + x) = Real.cos (((q % 4 : ℕ) : ℝ) * (Real.pi / 2) + x) := by
    rw [hsplit, hcos_periodic (q / 4) (((q % 4 : ℕ) : ℝ) * (Real.pi / 2) + x)]

  have hmod_lt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  have h_cases : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by
    omega
  rcases h_cases with (h | h | h | h)
  ·
    have h' : ((q % 4 : ℕ) : ℝ) = (0 : ℝ) := by exact_mod_cast h
    rw [hcos_eq, h']
    simp [h, lf_qc]
  ·
    have h' : ((q % 4 : ℕ) : ℝ) = (1 : ℝ) := by exact_mod_cast h
    rw [hcos_eq, h']
    rw [show (1 : ℝ) * (Real.pi / 2) + x = x + Real.pi / 2 by ring]
    rw [Real.cos_add_pi_div_two]
    simp [h, lf_qc]
  ·
    have h' : ((q % 4 : ℕ) : ℝ) = (2 : ℝ) := by exact_mod_cast h
    rw [hcos_eq, h']
    rw [show (2 : ℝ) * (Real.pi / 2) + x = x + Real.pi by ring]
    rw [Real.cos_add_pi]
    simp [h, lf_qc]
  ·
    have h' : ((q % 4 : ℕ) : ℝ) = (3 : ℝ) := by exact_mod_cast h
    rw [hcos_eq, h']
    rw [show (3 : ℝ) * (Real.pi / 2) + x = x + 3 * Real.pi / 2 by ring]
    have harg : x + 3 * Real.pi / 2 = (x + Real.pi / 2) + Real.pi := by ring
    rw [harg]
    rw [Real.cos_add_pi]
    rw [Real.cos_add_pi_div_two]
    simp [h, lf_qc]

theorem lf_sin_quarter (q : ℕ) (x : ℝ) :
    Real.sin (q * (Real.pi / 2) + x) = lf_qs q (Real.cos x) (Real.sin x) := by
  have hmod_lt : q % 4 < 4 := Nat.mod_lt q (by norm_num : 0 < 4)
  have h_cases : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
  rcases h_cases with (h0 | h1 | h2 | h3)
  ·
    simp [lf_qs, h0]
    have hq : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) := by
      have := (Nat.div_add_mod q 4).symm
      rw [h0] at this
      exact_mod_cast this
    rw [hq]
    calc
      Real.sin (((4 : ℝ) * ((q / 4 : ℕ) : ℝ)) * (Real.pi / 2) + x)
          = Real.sin (((q / 4 : ℕ) : ℝ) * (2 * Real.pi) + x) := by ring
      _ = Real.sin (x + ((q / 4 : ℕ) : ℝ) * (2 * Real.pi)) := by ring
      _ = Real.sin x := by rw [Real.sin_add_nat_mul_two_pi]
  ·
    simp [lf_qs, h1]
    have hq : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) + 1 := by
      have := (Nat.div_add_mod q 4).symm
      rw [h1] at this
      exact_mod_cast this
    rw [hq]
    calc
      Real.sin (((4 : ℝ) * ((q / 4 : ℕ) : ℝ) + 1) * (Real.pi / 2) + x)
          = Real.sin (((q / 4 : ℕ) : ℝ) * (2 * Real.pi) + Real.pi / 2 + x) := by ring
      _ = Real.sin (Real.pi / 2 + x + ((q / 4 : ℕ) : ℝ) * (2 * Real.pi)) := by ring
      _ = Real.sin (Real.pi / 2 + x) := by rw [Real.sin_add_nat_mul_two_pi]
      _ = Real.sin (x + Real.pi / 2) := by ring
      _ = Real.cos x := by rw [Real.sin_add_pi_div_two]
  ·
    simp [lf_qs, h2]
    have hq : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) + 2 := by
      have := (Nat.div_add_mod q 4).symm
      rw [h2] at this
      exact_mod_cast this
    rw [hq]
    calc
      Real.sin (((4 : ℝ) * ((q / 4 : ℕ) : ℝ) + 2) * (Real.pi / 2) + x)
          = Real.sin (((q / 4 : ℕ) : ℝ) * (2 * Real.pi) + Real.pi + x) := by ring
      _ = Real.sin (Real.pi + x + ((q / 4 : ℕ) : ℝ) * (2 * Real.pi)) := by ring
      _ = Real.sin (Real.pi + x) := by rw [Real.sin_add_nat_mul_two_pi]
      _ = Real.sin (x + Real.pi) := by ring
      _ = -Real.sin x := by rw [Real.sin_add_pi]
  ·
    simp [lf_qs, h3]
    have hq : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) + 3 := by
      have := (Nat.div_add_mod q 4).symm
      rw [h3] at this
      exact_mod_cast this
    rw [hq]
    calc
      Real.sin (((4 : ℝ) * ((q / 4 : ℕ) : ℝ) + 3) * (Real.pi / 2) + x)
          = Real.sin (((q / 4 : ℕ) : ℝ) * (2 * Real.pi) + (3 * Real.pi / 2) + x) := by ring
      _ = Real.sin ((3 * Real.pi / 2) + x + ((q / 4 : ℕ) : ℝ) * (2 * Real.pi)) := by ring
      _ = Real.sin ((3 * Real.pi / 2) + x) := by rw [Real.sin_add_nat_mul_two_pi]
      _ = Real.sin (x + (3 * Real.pi / 2)) := by ring
      _ = Real.sin (x + (Real.pi + Real.pi / 2)) := by ring
      _ = Real.sin ((x + Real.pi / 2) + Real.pi) := by ring
      _ = -Real.sin (x + Real.pi / 2) := by rw [Real.sin_add_pi]
      _ = -Real.cos x := by rw [Real.sin_add_pi_div_two]

theorem lf_le_two_arctan {L s c t : ℝ} (hL0 : 0 ≤ L) (hL : L < Real.pi) (ht : 0 ≤ t)
    (hs : Real.sin (L / 2) ≤ s) (hc : c ≤ Real.cos (L / 2)) (hc0 : 0 < c) (h : s ≤ t * c) :
    L ≤ 2 * Real.arctan t := by
  set x := L / 2 with hx
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    nlinarith
  have hx_lt_pi_div_two : x < Real.pi / 2 := by
    rw [hx]
    nlinarith
  have hx_lower : -(Real.pi / 2) < x := by
    nlinarith
  have hcos_pos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨hx_lower, hx_lt_pi_div_two⟩
  have h_sin_le_t_cos : Real.sin x ≤ t * Real.cos x := by
    have h_sin_le_s : Real.sin x ≤ s := hs
    have h_s_le_tc : s ≤ t * c := h
    have h_tc_le_t_cos : t * c ≤ t * Real.cos x := by
      nlinarith
    nlinarith
  have h_sin_div_cos_le_t : Real.sin x / Real.cos x ≤ t := by
    rwa [div_le_iff₀ hcos_pos]
  have h_tan_le_t : Real.tan x ≤ t := by
    rw [Real.tan_eq_sin_div_cos x]
    exact h_sin_div_cos_le_t
  have h_arctan_tan_eq_x : Real.arctan (Real.tan x) = x :=
    Real.arctan_tan hx_lower hx_lt_pi_div_two
  have h_arctan_tan_le_arctan_t : Real.arctan (Real.tan x) ≤ Real.arctan t :=
    (Real.arctan_le_arctan_iff.mpr h_tan_le_t)
  have hx_le_arctan_t : x ≤ Real.arctan t := by
    rw [← h_arctan_tan_eq_x]
    exact h_arctan_tan_le_arctan_t
  have hL_eq : L = 2 * x := by
    rw [hx]
    ring
  rw [hL_eq]
  nlinarith

theorem lf_two_arctan_le {U s c t : ℝ} (hU0 : 0 ≤ U) (hU : U < Real.pi) (ht : 0 ≤ t)
    (hs : s ≤ Real.sin (U / 2)) (hc : Real.cos (U / 2) ≤ c) (h : t * c ≤ s) :
    2 * Real.arctan t ≤ U := by
  set x := U / 2 with hx
  have hx_nonneg : 0 ≤ x := by
    linarith
  have hx_lt_pi_div_two : x < Real.pi / 2 := by
    linarith
  have hx_mem_Ioo : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos_pos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo hx_mem_Ioo
  have h_ineq : t * Real.cos x ≤ Real.sin x := by
    calc
      t * Real.cos x ≤ t * c := by
        nlinarith
      _ ≤ s := h
      _ ≤ Real.sin x := hs
  have h_t_le_tan : t ≤ Real.tan x := by
    have : t * Real.cos x ≤ Real.sin x := h_ineq
    rw [Real.tan_eq_sin_div_cos]
    exact (le_div_iff₀ hcos_pos).mpr this
  have hx_lower : -(Real.pi / 2) < x := by
    linarith
  have h_arctan : Real.arctan t ≤ x := by
    calc
      Real.arctan t ≤ Real.arctan (Real.tan x) :=
        (Real.arctan_le_arctan_iff).mpr h_t_le_tan
      _ = x := Real.arctan_tan hx_lower hx_lt_pi_div_two
  linarith

theorem lf_scaled_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) (a b : ℝ) :
    (a • A.map (Int.cast : ℤ → ℝ)) * (b • B.map (Int.cast : ℤ → ℝ)) =
      (a * b) • (A * B).map (Int.cast : ℤ → ℝ) := by
  calc
    (a • A.map (Int.cast : ℤ → ℝ)) * (b • B.map (Int.cast : ℤ → ℝ))
        = a • ((A.map (Int.cast : ℤ → ℝ)) * (b • B.map (Int.cast : ℤ → ℝ))) := by
      rw [Matrix.smul_mul]
    _ = a • (b • ((A.map (Int.cast : ℤ → ℝ)) * (B.map (Int.cast : ℤ → ℝ)))) := by
      rw [Matrix.mul_smul]
    _ = (a * b) • ((A.map (Int.cast : ℤ → ℝ)) * (B.map (Int.cast : ℤ → ℝ))) := by
      rw [smul_smul]
    _ = (a * b) • ((A * B).map (Int.cast : ℤ → ℝ)) := by
      rw [← Matrix.map_mul_intCast]

theorem lf_norm_lt_of_sq {x : EuclideanSpace ℝ (Fin 3)} {s : ℝ} (hs : 0 < s)
    (h : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 < s ^ 2) : ‖x‖ < s := by
  have hs_nonneg : 0 ≤ s := by linarith
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  have h_sq : ‖x‖ ^ 2 < s ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
      _ = ∑ i : Fin 3, (x.ofLp i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
      _ = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by rw [Fin.sum_univ_three]
      _ < s ^ 2 := h
  have h_abs : |‖x‖| < |s| := (sq_lt_sq.mp h_sq)
  rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hs_nonneg] at h_abs
  exact h_abs

theorem lf_norm_le_of_sq {x : EuclideanSpace ℝ (Fin 3)} {s : ℝ} (hs : 0 ≤ s)
    (h : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 ≤ s ^ 2) : ‖x‖ ≤ s := by
  have h_norm_sq : ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by
    calc
      ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
      _ = ∑ i : Fin 3, (x.ofLp i) ^ 2 := by simp [sq_abs]
      _ = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by simp [Fin.sum_univ_three]
  have h_norm_sq_le : ‖x‖ ^ 2 ≤ s ^ 2 := by linarith
  have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  exact ((sq_le_sq₀ h_norm_nonneg hs).mp h_norm_sq_le)

theorem lf_eta_anti_g {g1 g2 e f : ℝ} (hse : 0 < Real.sin e) (hsf : 0 < Real.sin f) (h1 : 0 ≤ g1)
    (h12 : g1 ≤ g2) (h2 : g2 ≤ Real.pi) : lf_eta g2 e f ≤ lf_eta g1 e f := by
  have hcos : Real.cos g2 ≤ Real.cos g1 :=
    Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h12
  have hsub : Real.cos g2 - Real.cos e * Real.cos f ≤ Real.cos g1 - Real.cos e * Real.cos f := by
    linarith
  have hpos : 0 ≤ Real.sin e * Real.sin f := by
    positivity
  dsimp [lf_eta]
  exact div_le_div_of_nonneg_right hsub hpos

open Real Set in
theorem lf_eta_mono_e {g f a b : ℝ} (ha : 0 < a) (hb : b < Real.pi) (hsf : 0 < Real.sin f)
    (hsign : ∀ e ∈ Set.Icc a b, 0 ≤ Real.cos f - Real.cos e * Real.cos g) :
    MonotoneOn (fun e => lf_eta g e f) (Set.Icc a b) := by
  have hsin_pos : ∀ e ∈ Set.Icc a b, 0 < Real.sin e := by
    intro e he
    rcases he with ⟨hae, heb⟩
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le ha hae) (lt_of_le_of_lt heb hb)
  have h_den_pos : ∀ e ∈ Set.Icc a b, 0 < Real.sin e * Real.sin f := by
    intro e he
    exact mul_pos (hsin_pos e he) hsf
  have h_den_ne_zero : ∀ e ∈ Set.Icc a b, Real.sin e * Real.sin f ≠ 0 := by
    intro e he
    exact ne_of_gt (h_den_pos e he)
  have h_cont : ContinuousOn (fun e => lf_eta g e f) (Set.Icc a b) := by
    unfold lf_eta
    refine ContinuousOn.div ?_ ?_ ?_
    ·
      refine ContinuousOn.sub ?_ ?_
      · exact continuousOn_const
      · refine ContinuousOn.mul ?_ ?_
        · exact continuous_cos.continuousOn
        · exact continuousOn_const
    ·
      refine ContinuousOn.mul ?_ ?_
      · exact continuous_sin.continuousOn
      · exact continuousOn_const
    · intro e he
      exact h_den_ne_zero e he
  have h_diff : DifferentiableOn ℝ (fun e => lf_eta g e f) (interior (Set.Icc a b)) := by
    unfold lf_eta
    refine DifferentiableOn.div ?_ ?_ ?_
    ·
      refine DifferentiableOn.sub ?_ ?_
      · exact differentiableOn_const _
      · refine DifferentiableOn.mul ?_ ?_
        · exact differentiable_cos.differentiableOn
        · exact differentiableOn_const _
    ·
      refine DifferentiableOn.mul ?_ ?_
      · exact differentiable_sin.differentiableOn
      · exact differentiableOn_const _
    · intro e he
      exact h_den_ne_zero e (interior_subset he)
  have h_deriv_nonneg : ∀ e ∈ interior (Set.Icc a b), 0 ≤ deriv (fun e => lf_eta g e f) e := by
    intro e he
    have he_icc : e ∈ Set.Icc a b := interior_subset he
    have hsin_e_pos : 0 < Real.sin e := hsin_pos e he_icc
    have hcos_f_sub : 0 ≤ Real.cos f - Real.cos e * Real.cos g := hsign e he_icc

    have h_hasDeriv : HasDerivAt (fun x => (Real.cos g - Real.cos x * Real.cos f) / (Real.sin x * Real.sin f))
      (Real.sin f * (Real.cos f - Real.cos e * Real.cos g) / (Real.sin e * Real.sin f) ^ 2) e := by

      have h_num : HasDerivAt (fun x => Real.cos g - Real.cos x * Real.cos f) (Real.sin e * Real.cos f) e := by
        have h1 : HasDerivAt (fun x : ℝ => Real.cos g) 0 e := hasDerivAt_const _ _
        have h2 : HasDerivAt (fun x : ℝ => Real.cos x * Real.cos f) (-Real.sin e * Real.cos f) e := by
          have hcos : HasDerivAt Real.cos (-Real.sin e) e := hasDerivAt_cos e
          have hconst : HasDerivAt (fun x : ℝ => Real.cos f) 0 e := hasDerivAt_const _ _
          simpa [Pi.mul_def, mul_comm] using HasDerivAt.mul hcos hconst
        have hsub : HasDerivAt (fun x => Real.cos g - Real.cos x * Real.cos f) (0 - (-Real.sin e * Real.cos f)) e :=
          HasDerivAt.sub h1 h2
        simpa using hsub

      have h_den : HasDerivAt (fun x => Real.sin x * Real.sin f) (Real.cos e * Real.sin f) e := by
        have hsin : HasDerivAt Real.sin (Real.cos e) e := hasDerivAt_sin e
        have hconst : HasDerivAt (fun x : ℝ => Real.sin f) 0 e := hasDerivAt_const _ _
        simpa [Pi.mul_def, mul_comm] using HasDerivAt.mul hsin hconst
      have h_den_ne_zero : Real.sin e * Real.sin f ≠ 0 := h_den_ne_zero e he_icc

      have h_div := HasDerivAt.div h_num h_den h_den_ne_zero

      have h_num_eq : (Real.sin e * Real.cos f) * (Real.sin e * Real.sin f) - (Real.cos g - Real.cos e * Real.cos f) * (Real.cos e * Real.sin f) =
          Real.sin f * (Real.cos f - Real.cos e * Real.cos g) := by
        calc
          (Real.sin e * Real.cos f) * (Real.sin e * Real.sin f) - (Real.cos g - Real.cos e * Real.cos f) * (Real.cos e * Real.sin f)
              = Real.sin f * ((Real.sin e)^2 * Real.cos f - Real.cos e * Real.cos g + (Real.cos e)^2 * Real.cos f) := by ring
          _ = Real.sin f * (((Real.sin e)^2 + (Real.cos e)^2) * Real.cos f - Real.cos e * Real.cos g) := by ring
          _ = Real.sin f * (1 * Real.cos f - Real.cos e * Real.cos g) := by rw [Real.sin_sq_add_cos_sq e]
          _ = Real.sin f * (Real.cos f - Real.cos e * Real.cos g) := by ring

      convert h_div using 1
      rw [h_num_eq]
    have h_deriv_eq : deriv (fun e => lf_eta g e f) e = Real.sin f * (Real.cos f - Real.cos e * Real.cos g) / (Real.sin e * Real.sin f) ^ 2 :=
      h_hasDeriv.deriv
    unfold lf_eta at *
    rw [h_deriv_eq]

    refine div_nonneg ?_ ?_
    ·
      nlinarith
    ·
      nlinarith
  exact monotoneOn_of_deriv_nonneg (convex_Icc a b) h_cont h_diff h_deriv_nonneg

open Real Set in
theorem lf_eta_anti_e {g f a b : ℝ} (ha : 0 < a) (hb : b < Real.pi) (hsf : 0 < Real.sin f)
    (hsign : ∀ e ∈ Set.Icc a b, Real.cos f - Real.cos e * Real.cos g ≤ 0) :
    AntitoneOn (fun e => lf_eta g e f) (Set.Icc a b) := by
  have hsin_pos : ∀ e ∈ Set.Icc a b, 0 < Real.sin e := by
    intro e he
    rcases he with ⟨hae, heb⟩
    exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le ha hae) (lt_of_le_of_lt heb hb)
  have h_den_pos : ∀ e ∈ Set.Icc a b, 0 < Real.sin e * Real.sin f := by
    intro e he
    exact mul_pos (hsin_pos e he) hsf
  have h_den_ne_zero : ∀ e ∈ Set.Icc a b, Real.sin e * Real.sin f ≠ 0 := by
    intro e he
    exact ne_of_gt (h_den_pos e he)
  have h_cont : ContinuousOn (fun e => lf_eta g e f) (Set.Icc a b) := by
    unfold lf_eta
    refine ContinuousOn.div ?_ ?_ ?_
    ·
      refine ContinuousOn.sub ?_ ?_
      · exact continuousOn_const
      · refine ContinuousOn.mul ?_ ?_
        · exact continuous_cos.continuousOn
        · exact continuousOn_const
    ·
      refine ContinuousOn.mul ?_ ?_
      · exact continuous_sin.continuousOn
      · exact continuousOn_const
    · intro e he
      exact h_den_ne_zero e he
  have h_diff : DifferentiableOn ℝ (fun e => lf_eta g e f) (interior (Set.Icc a b)) := by
    unfold lf_eta
    refine DifferentiableOn.div ?_ ?_ ?_
    ·
      refine DifferentiableOn.sub ?_ ?_
      · exact differentiableOn_const _
      · refine DifferentiableOn.mul ?_ ?_
        · exact differentiable_cos.differentiableOn
        · exact differentiableOn_const _
    ·
      refine DifferentiableOn.mul ?_ ?_
      · exact differentiable_sin.differentiableOn
      · exact differentiableOn_const _
    · intro e he
      exact h_den_ne_zero e (interior_subset he)
  have h_deriv_nonpos : ∀ e ∈ interior (Set.Icc a b), deriv (fun e => lf_eta g e f) e ≤ 0 := by
    intro e he
    have he_icc : e ∈ Set.Icc a b := interior_subset he
    have hsin_e_pos : 0 < Real.sin e := hsin_pos e he_icc
    have hcos_f_sub : Real.cos f - Real.cos e * Real.cos g ≤ 0 := hsign e he_icc

    have h_hasDeriv : HasDerivAt (fun x => (Real.cos g - Real.cos x * Real.cos f) / (Real.sin x * Real.sin f))
      (Real.sin f * (Real.cos f - Real.cos e * Real.cos g) / (Real.sin e * Real.sin f) ^ 2) e := by

      have h_num : HasDerivAt (fun x => Real.cos g - Real.cos x * Real.cos f) (Real.sin e * Real.cos f) e := by
        have h1 : HasDerivAt (fun x : ℝ => Real.cos g) 0 e := hasDerivAt_const _ _
        have h2 : HasDerivAt (fun x : ℝ => Real.cos x * Real.cos f) (-Real.sin e * Real.cos f) e := by
          have hcos : HasDerivAt Real.cos (-Real.sin e) e := hasDerivAt_cos e
          have hconst : HasDerivAt (fun x : ℝ => Real.cos f) 0 e := hasDerivAt_const _ _
          simpa [Pi.mul_def, mul_comm] using HasDerivAt.mul hcos hconst
        have hsub : HasDerivAt (fun x => Real.cos g - Real.cos x * Real.cos f) (0 - (-Real.sin e * Real.cos f)) e :=
          HasDerivAt.sub h1 h2
        simpa using hsub

      have h_den : HasDerivAt (fun x => Real.sin x * Real.sin f) (Real.cos e * Real.sin f) e := by
        have hsin : HasDerivAt Real.sin (Real.cos e) e := hasDerivAt_sin e
        have hconst : HasDerivAt (fun x : ℝ => Real.sin f) 0 e := hasDerivAt_const _ _
        simpa [Pi.mul_def, mul_comm] using HasDerivAt.mul hsin hconst
      have h_den_ne_zero : Real.sin e * Real.sin f ≠ 0 := h_den_ne_zero e he_icc

      have h_div := HasDerivAt.div h_num h_den h_den_ne_zero

      have h_num_eq : (Real.sin e * Real.cos f) * (Real.sin e * Real.sin f) - (Real.cos g - Real.cos e * Real.cos f) * (Real.cos e * Real.sin f) =
          Real.sin f * (Real.cos f - Real.cos e * Real.cos g) := by
        calc
          (Real.sin e * Real.cos f) * (Real.sin e * Real.sin f) - (Real.cos g - Real.cos e * Real.cos f) * (Real.cos e * Real.sin f)
              = Real.sin f * ((Real.sin e)^2 * Real.cos f - Real.cos e * Real.cos g + (Real.cos e)^2 * Real.cos f) := by ring
          _ = Real.sin f * (((Real.sin e)^2 + (Real.cos e)^2) * Real.cos f - Real.cos e * Real.cos g) := by ring
          _ = Real.sin f * (1 * Real.cos f - Real.cos e * Real.cos g) := by rw [Real.sin_sq_add_cos_sq e]
          _ = Real.sin f * (Real.cos f - Real.cos e * Real.cos g) := by ring

      convert h_div using 1
      rw [h_num_eq]
    have h_deriv_eq : deriv (fun e => lf_eta g e f) e = Real.sin f * (Real.cos f - Real.cos e * Real.cos g) / (Real.sin e * Real.sin f) ^ 2 :=
      h_hasDeriv.deriv
    unfold lf_eta at *
    rw [h_deriv_eq]

    refine div_nonpos_of_nonpos_of_nonneg ?_ ?_
    ·
      nlinarith
    ·
      nlinarith
  exact antitoneOn_of_deriv_nonpos (convex_Icc a b) h_cont h_diff h_deriv_nonpos

theorem lf_div_bounds {n d n1 n2 d1 d2 : ℝ} (hd1 : 0 < d1) (hd : d1 ≤ d) (hd2 : d ≤ d2) (hn1 : n1 ≤ n)
    (hn2 : n ≤ n2) : min (n1 / d1) (n1 / d2) ≤ n / d ∧ n / d ≤ max (n2 / d1) (n2 / d2) := by
  have hdpos : 0 < d := lt_of_lt_of_le hd1 hd
  have hd1_nonneg : 0 ≤ d1 := le_of_lt hd1
  have hd_nonneg : 0 ≤ d := le_of_lt hdpos
  have hd2pos : 0 < d2 := lt_of_lt_of_le hdpos hd2
  have hd2_nonneg : 0 ≤ d2 := le_of_lt hd2pos
  have hleft : min (n1 / d1) (n1 / d2) ≤ n / d := by
    rw [min_le_iff]
    by_cases hn1_nonneg : 0 ≤ n1
    ·
      right
      have hn_nonneg : 0 ≤ n := le_trans hn1_nonneg hn1
      calc
        n1 / d2 ≤ n / d2 := div_le_div_of_nonneg_right hn1 hd2_nonneg
        _ ≤ n / d := div_le_div_of_nonneg_left hn_nonneg hdpos hd2
    ·
      by_cases hn_nonpos : n ≤ 0
      ·
        left
        have hneg : n1 / d1 ≤ n / d1 := div_le_div_of_nonneg_right hn1 hd1_nonneg
        have hdiv : n / d1 ≤ n / d := by
          have h := mul_le_mul_of_nonpos_right hd hn_nonpos

          field_simp [hd1.ne.symm, hdpos.ne.symm]
          nlinarith
        exact le_trans hneg hdiv
      ·
        have hn_pos : 0 < n := lt_of_not_ge hn_nonpos
        left
        have hn1_neg : n1 < 0 := lt_of_not_ge hn1_nonneg
        have h_neg : n1 / d1 < 0 := div_neg_of_neg_of_pos hn1_neg hd1
        have h_pos : 0 < n / d := div_pos hn_pos hdpos
        linarith
  have hright : n / d ≤ max (n2 / d1) (n2 / d2) := by
    rw [le_max_iff]
    by_cases hn2_nonneg : 0 ≤ n2
    ·
      by_cases hn_nonneg : 0 ≤ n
      ·
        left
        calc
          n / d ≤ n2 / d := div_le_div_of_nonneg_right hn2 hd_nonneg
          _ ≤ n2 / d1 := div_le_div_of_nonneg_left hn2_nonneg hd1 hd
      ·
        have hn_neg : n < 0 := lt_of_not_ge hn_nonneg
        left
        have h_neg : n / d < 0 := div_neg_of_neg_of_pos hn_neg hdpos
        have h_nonneg : 0 ≤ n2 / d1 := div_nonneg hn2_nonneg hd1_nonneg
        linarith
    ·
      have hn2_neg : n2 < 0 := lt_of_not_ge hn2_nonneg
      have hn_neg : n < 0 := lt_of_le_of_lt hn2 hn2_neg
      right

      calc
        n / d ≤ n2 / d := div_le_div_of_nonneg_right hn2 hd_nonneg
        _ ≤ n2 / d2 := by
          have h := mul_le_mul_of_nonpos_right hd2 hn2_neg.le

          field_simp [hdpos.ne.symm, hd2pos.ne.symm]
          nlinarith
  exact And.intro hleft hright

theorem lf_mul_bounds {x y x1 x2 y1 y2 : ℝ} (hx1 : x1 ≤ x) (hx2 : x ≤ x2) (hy1 : y1 ≤ y) (hy2 : y ≤ y2) :
    min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2)) ≤ x * y ∧
      x * y ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := by
  have hx_mid : min (x1 * y) (x2 * y) ≤ x * y ∧ x * y ≤ max (x1 * y) (x2 * y) := by
    by_cases hy_nonneg : 0 ≤ y
    · constructor
      · calc
          min (x1 * y) (x2 * y) ≤ x1 * y := min_le_left _ _
          _ ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy_nonneg
      · calc
          x * y ≤ x2 * y := mul_le_mul_of_nonneg_right hx2 hy_nonneg
          _ ≤ max (x1 * y) (x2 * y) := le_max_right _ _
    · have hy_nonpos : y ≤ 0 := by linarith
      constructor
      · calc
          min (x1 * y) (x2 * y) ≤ x2 * y := min_le_right _ _
          _ ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy_nonpos
      · calc
          x * y ≤ x1 * y := mul_le_mul_of_nonpos_right hx1 hy_nonpos
          _ ≤ max (x1 * y) (x2 * y) := le_max_left _ _
  have hy_mid1 : min (x1 * y1) (x1 * y2) ≤ x1 * y ∧ x1 * y ≤ max (x1 * y1) (x1 * y2) := by
    by_cases hx1_nonneg : 0 ≤ x1
    · constructor
      · calc
          min (x1 * y1) (x1 * y2) ≤ x1 * y1 := min_le_left _ _
          _ ≤ x1 * y := mul_le_mul_of_nonneg_left hy1 hx1_nonneg
      · calc
          x1 * y ≤ x1 * y2 := mul_le_mul_of_nonneg_left hy2 hx1_nonneg
          _ ≤ max (x1 * y1) (x1 * y2) := le_max_right _ _
    · have hx1_nonpos : x1 ≤ 0 := by linarith
      constructor
      · calc
          min (x1 * y1) (x1 * y2) ≤ x1 * y2 := min_le_right _ _
          _ ≤ x1 * y := mul_le_mul_of_nonpos_left hy2 hx1_nonpos
      · calc
          x1 * y ≤ x1 * y1 := mul_le_mul_of_nonpos_left hy1 hx1_nonpos
          _ ≤ max (x1 * y1) (x1 * y2) := le_max_left _ _
  have hy_mid2 : min (x2 * y1) (x2 * y2) ≤ x2 * y ∧ x2 * y ≤ max (x2 * y1) (x2 * y2) := by
    by_cases hx2_nonneg : 0 ≤ x2
    · constructor
      · calc
          min (x2 * y1) (x2 * y2) ≤ x2 * y1 := min_le_left _ _
          _ ≤ x2 * y := mul_le_mul_of_nonneg_left hy1 hx2_nonneg
      · calc
          x2 * y ≤ x2 * y2 := mul_le_mul_of_nonneg_left hy2 hx2_nonneg
          _ ≤ max (x2 * y1) (x2 * y2) := le_max_right _ _
    · have hx2_nonpos : x2 ≤ 0 := by linarith
      constructor
      · calc
          min (x2 * y1) (x2 * y2) ≤ x2 * y2 := min_le_right _ _
          _ ≤ x2 * y := mul_le_mul_of_nonpos_left hy2 hx2_nonpos
      · calc
          x2 * y ≤ x2 * y1 := mul_le_mul_of_nonpos_left hy1 hx2_nonpos
          _ ≤ max (x2 * y1) (x2 * y2) := le_max_left _ _
  rcases hx_mid with ⟨hx_lower, hx_upper⟩
  rcases hy_mid1 with ⟨hy1_lower, hy1_upper⟩
  rcases hy_mid2 with ⟨hy2_lower, hy2_upper⟩
  constructor
  ·
    have hmin : min (x1 * y) (x2 * y) ≥ min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2)) := by
      exact min_le_min hy1_lower hy2_lower
    linarith
  ·
    have hmax : x * y ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := by

      have hmax_inner : max (x1 * y) (x2 * y) ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) :=
        max_le_max hy1_upper hy2_upper
      linarith
    exact hmax

theorem lf_sin_ge_min {a b x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ Real.pi) :
    min (Real.sin a) (Real.sin b) ≤ Real.sin x := by
  by_cases hx : x ≤ Real.pi / 2
  ·
    have h_sin_a_le_sin_x : Real.sin a ≤ Real.sin x :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hax
    have h_min_le_sin_a : min (Real.sin a) (Real.sin b) ≤ Real.sin a := by
      exact min_le_left _ _
    linarith
  ·
    have h_sin_b_le_sin_x : Real.sin b ≤ Real.sin x := by
      calc
        Real.sin b = Real.sin (Real.pi - b) := by rw [Real.sin_pi_sub]
        _ ≤ Real.sin (Real.pi - x) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
        _ = Real.sin x := by rw [Real.sin_pi_sub]
    have h_min_le_sin_b : min (Real.sin a) (Real.sin b) ≤ Real.sin b := by
      exact min_le_right _ _
    linarith
end Tammes15.D3Kernel.Kinds
