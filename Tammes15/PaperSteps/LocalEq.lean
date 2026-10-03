import Tammes15.Local41.Chain
import Tammes15.Attained.Data
import Tammes15.Kappa.Assembly
import Tammes15.PaperSteps.FrameD

/-!
# Theorem C for the eight frame configurations, with its equality case

The paper states: let `p` be one of the eight frame configurations, labelled, and let `x` be
fifteen points of the sphere with `|x_i - R p_i| ≤ r = 1.04·10⁻³` for all `i` and some orthogonal
map `R`; then `min_{i<j} dist(x_i, x_j) ≤ ψ*`, with equality only if `x_i = R' p_i` for all `i` and
some orthogonal map `R'`. A frame configuration keeps the twelve points of the frame outside the
toggle pairs and one point of each toggle pair (indices of `Attained.pt`: the pairs are `{6, 11}`,
`{7, 9}`, `{8, 10}`); a labelling is an injective `keep : Fin 15 → Fin 18` onto such a set.
`local_optimality` (Local41/Chain.lean) is the inequality for an abstract frame; this file states
the theorem as the paper does (`local_optimality_frame`). `IsFrameKeep` and `minAngle` are defined
in FrameDefs.lean.
-/

open Real Matrix InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-! ## The strict form of the chain, and the pieces of the equality case -/

/-- A unit vector `x` with `tpart p x = 0` near the unit vector `p` is `p`. -/
theorem eq_of_tpart_eq_zero (p x : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hs : ‖x - p‖ ^ 2 < 2)
    (h : tpart p x = 0) : x = p := by
  unfold tpart at h
  -- h: (x - p) + (‖x - p‖ ^ 2 / 2) • p = 0
  have h_sub_eq : x - p = (-(‖x - p‖ ^ 2 / 2)) • p := by
    calc
      x - p = ((x - p) + (‖x - p‖ ^ 2 / 2) • p) - (‖x - p‖ ^ 2 / 2) • p := by abel_nf
      _ = 0 - (‖x - p‖ ^ 2 / 2) • p := by rw [h]
      _ = (-(‖x - p‖ ^ 2 / 2)) • p := by simp
  have hx_eq : x = (1 - ‖x - p‖ ^ 2 / 2) • p := by
    calc
      x = (x - p) + p := by abel_nf
      _ = ((-(‖x - p‖ ^ 2 / 2)) • p) + p := by
        simpa using congrArg (· + p) h_sub_eq
      _ = ((-(‖x - p‖ ^ 2 / 2)) • p) + ((1 : ℝ) • p) := by simp
      _ = ((-(‖x - p‖ ^ 2 / 2)) + 1) • p := by rw [← add_smul]
      _ = (1 - ‖x - p‖ ^ 2 / 2) • p := by ring
  have h_norm_eq : ‖x‖ = |1 - ‖x - p‖ ^ 2 / 2| * ‖p‖ := by
    conv =>
      lhs
      rw [hx_eq]
    rw [norm_smul, Real.norm_eq_abs]
  rw [hp, hx] at h_norm_eq
  simp at h_norm_eq
  -- h_norm_eq: |1 - ‖x - p‖ ^ 2 / 2| = 1
  by_cases h_nonneg : 0 ≤ 1 - ‖x - p‖ ^ 2 / 2
  · rw [abs_of_nonneg h_nonneg] at h_norm_eq
    have hsq : ‖x - p‖ ^ 2 = 0 := by linarith
    have h_norm_zero : ‖x - p‖ = 0 := by
      have h_nonneg' : 0 ≤ ‖x - p‖ := norm_nonneg _
      nlinarith
    have h_sub_zero : x - p = 0 := norm_eq_zero.mp h_norm_zero
    calc
      x = (x - p) + p := by abel_nf
      _ = 0 + p := by rw [h_sub_zero]
      _ = p := by simp
  · have h_nonpos : 1 - ‖x - p‖ ^ 2 / 2 ≤ 0 := by linarith
    rw [abs_of_nonpos h_nonpos] at h_norm_eq
    have hsq : ‖x - p‖ ^ 2 = 4 := by linarith
    nlinarith

/-- The chain of Theorem C with the strict radius condition: either the points are the frame, or
some contact is strictly shorter. -/
theorem chain_strict {n : ℕ} (q x : Fin n → E3) (S : Finset (Fin n × Fin n)) (u κ0 r : ℝ)
    (hq : ∀ i, ‖q i‖ = 1) (hx : ∀ i, ‖x i‖ = 1) (hS : ∀ ij ∈ S, ⟪q ij.1, q ij.2⟫ = u)
    (hu : 0 < u) (hκ : KappaBound q S κ0) (hr0 : 0 ≤ r)
    (hsum : ∑ i, ‖x i - q i‖ ^ 2 ≤ n * r ^ 2) (hcross : ∑ i, cross (q i) (x i) = 0)
    (hr : Real.sqrt n * r * (1.01 * (1 + u)) < κ0) (hr2 : (n : ℝ) * r ^ 2 < 0.02) :
    (∀ i, x i = q i) ∨ ∃ ij ∈ S, u < ⟪x ij.1, x ij.2⟫ := by
  set t := fun i : Fin n => tpart (q i) (x i) with ht
  set s := fun i : Fin n => ‖x i - q i‖ ^ 2 with hs
  set T := Real.sqrt (∑ i, ‖t i‖ ^ 2) with hT
  have hT_nonneg : 0 ≤ T := Real.sqrt_nonneg _
  have hT_sq : T ^ 2 = ∑ i, ‖t i‖ ^ 2 := by
    rw [hT]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have h_s_nonneg : ∀ k, 0 ≤ s k := by
    intro k
    rw [hs]
    positivity
  have h_s_lt_002 : ∀ k, s k < 0.02 := by
    intro k
    have h_single : s k ≤ ∑ i, s i :=
      Finset.single_le_sum (fun i hi => h_s_nonneg i) (Finset.mem_univ k)
    have h_sum_le : ∑ i, s i ≤ (n : ℝ) * r ^ 2 := by
      simpa [hs] using hsum
    have h_sum_lt : ∑ i, s i < 0.02 := by linarith
    linarith
  have h_s_le_101_norm_t_sq : ∀ k, s k ≤ 1.01 * ‖t k‖ ^ 2 := by
    intro k
    have h_sq_le : s k ≤ 1.01 * (s k * (1 - s k / 4)) :=
      sq_le_of_small (s k) ⟨h_s_nonneg k, h_s_lt_002 k⟩
    have h_norm_tpart_sq : ‖t k‖ ^ 2 = s k * (1 - s k / 4) := by
      rw [ht, hs]
      exact norm_tpart_sq (q k) (x k) (hq k) (hx k)
    simpa [h_norm_tpart_sq] using h_sq_le
  have h_s_le_101_T_sq : ∀ k, s k ≤ 1.01 * T ^ 2 := by
    intro k
    have h_norm_t_sq_le_T_sq : ‖t k‖ ^ 2 ≤ T ^ 2 := by
      rw [hT_sq]
      have h_single := Finset.single_le_sum
        (fun i hi => sq_nonneg (‖t i‖)) (Finset.mem_univ k)
      simpa using h_single
    nlinarith [h_s_le_101_norm_t_sq k, h_norm_t_sq_le_T_sq]
  have h_sum_sq_t_le : ∑ i, ‖t i‖ ^ 2 ≤ (n : ℝ) * r ^ 2 := by
    calc
      ∑ i, ‖t i‖ ^ 2 ≤ ∑ i, ‖x i - q i‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => norm_tpart_sq_le (q i) (x i) (hq i) (hx i)
      _ ≤ (n : ℝ) * r ^ 2 := by
        simpa using hsum
  have hT_le_sqrtn_r : T ≤ Real.sqrt (n : ℝ) * r := by
    calc
      T = Real.sqrt (∑ i, ‖t i‖ ^ 2) := rfl
      _ ≤ Real.sqrt ((n : ℝ) * r ^ 2) := Real.sqrt_le_sqrt h_sum_sq_t_le
      _ = Real.sqrt ((n : ℝ) * (r ^ 2)) := by ring
      _ = Real.sqrt (n : ℝ) * Real.sqrt (r ^ 2) := by
        rw [Real.sqrt_mul (by exact mod_cast Nat.zero_le n)]
      _ = Real.sqrt (n : ℝ) * |r| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (n : ℝ) * r := by rw [abs_of_nonneg hr0]
  have h_t_perp : TPerp q t := by
    refine ⟨fun i => inner_tpart (q i) (x i) (hq i) (hx i), ?_⟩
    calc
      ∑ i, cross (q i) (t i) = ∑ i, cross (q i) (tpart (q i) (x i)) := rfl
      _ = ∑ i, cross (q i) (x i) := by simp [cross_tpart]
      _ = 0 := hcross
  obtain ⟨ij, hijS, hκij⟩ := hκ t h_t_perp
  have hκij' : κ0 * T ≤ Lmap q t ij := by
    rw [hT]
    exact hκij
  have h_inner := inner_sub_ge (q ij.1) (q ij.2) (x ij.1) (x ij.2) (hq _) (hq _) (hx _) (hx _)
  have hS_ij : ⟪q ij.1, q ij.2⟫ = u := hS ij hijS
  have hLmap_expanded : ⟪q ij.1, tpart (q ij.2) (x ij.2)⟫ + ⟪q ij.2, tpart (q ij.1) (x ij.1)⟫ = Lmap q t ij := rfl
  rw [hLmap_expanded, hS_ij] at h_inner
  have hs_val : ∀ i, s i = ‖x i - q i‖ ^ 2 := by
    intro i; rw [hs]
  rw [← hs_val ij.1, ← hs_val ij.2] at h_inner
  have h_nonneg_u : 0 ≤ u := by linarith
  by_cases hT_zero : T = 0
  · -- Case T = 0: all t i = 0, so x i = q i for all i
    left
    have h_sum_sq_zero : ∑ i, ‖t i‖ ^ 2 = 0 := by
      rw [← hT_sq, hT_zero]
      simp
    have h_each_zero : ∀ i, ‖t i‖ ^ 2 = 0 := by
      have h_nonneg_sq : ∀ i, 0 ≤ ‖t i‖ ^ 2 := fun i => sq_nonneg _
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => h_nonneg_sq i)).mp h_sum_sq_zero
      intro i
      exact h i (Finset.mem_univ i)
    intro i
    have h_t_i_zero : t i = 0 := by
      have h_norm_zero : ‖t i‖ = 0 := by
        have h_sq_zero : ‖t i‖ ^ 2 = 0 := h_each_zero i
        nlinarith
      exact norm_eq_zero.mp h_norm_zero
    have h_s_i_lt_2 : s i < 2 := by
      have h_s_i_lt_002 : s i < 0.02 := h_s_lt_002 i
      linarith
    have h_tpart_zero : tpart (q i) (x i) = 0 := by
      have hti := congrFun ht i
      rw [← hti]
      exact h_t_i_zero
    exact eq_of_tpart_eq_zero (q i) (x i) (hq i) (hx i) h_s_i_lt_2 h_tpart_zero
  · -- Case T > 0
    right
    have hT_pos : 0 < T := by
      by_contra! hle
      apply hT_zero
      linarith
    have h_factor_pos : 0 < κ0 - 1.01 * (1 + u) * T := by
      have h_mul : 1.01 * (1 + u) * T ≤ 1.01 * (1 + u) * (Real.sqrt (n : ℝ) * r) := by
        nlinarith
      have h_eq : 1.01 * (1 + u) * (Real.sqrt (n : ℝ) * r) = Real.sqrt (n : ℝ) * r * (1.01 * (1 + u)) := by ring
      rw [h_eq] at h_mul
      linarith
    have h_main : u < ⟪x ij.1, x ij.2⟫ := by
      have h_sum_s_le : s ij.1 + s ij.2 ≤ 2 * (1.01 * T ^ 2) := by
        linarith [h_s_le_101_T_sq ij.1, h_s_le_101_T_sq ij.2]
      have h_ineq1 : Lmap q t ij - (1 + u) / 2 * (s ij.1 + s ij.2) ≤ ⟪x ij.1, x ij.2⟫ - u := h_inner
      have h_ineq2 : κ0 * T - (1 + u) / 2 * (s ij.1 + s ij.2) ≤ Lmap q t ij - (1 + u) / 2 * (s ij.1 + s ij.2) := by
        linarith
      have h_ineq3 : κ0 * T - (1 + u) / 2 * (s ij.1 + s ij.2) ≥ κ0 * T - (1 + u) * 1.01 * T ^ 2 := by
        have : (1 + u) / 2 * (s ij.1 + s ij.2) ≤ (1 + u) * 1.01 * T ^ 2 := by
          nlinarith
        linarith
      have h_ineq4 : κ0 * T - (1 + u) * 1.01 * T ^ 2 = T * (κ0 - 1.01 * (1 + u) * T) := by ring
      have h_pos_prod : 0 < T * (κ0 - 1.01 * (1 + u) * T) := by
        have hpos_factor : 0 < κ0 - 1.01 * (1 + u) * T := h_factor_pos
        nlinarith
      have h_pos_final : 0 < κ0 * T - (1 + u) / 2 * (s ij.1 + s ij.2) := by
        linarith
      linarith
    exact ⟨ij, hijS, h_main⟩

/-- Theorem C for an abstract frame with the strict radius condition: the points are an orthogonal
image of the frame, or some contact is strictly shorter. -/
theorem local_optimality_strict {n : ℕ} (p : Fin n → E3) (S : Finset (Fin n × Fin n))
    (u κ0 r : ℝ) (hp : ∀ i, ‖p i‖ = 1) (hS : ∀ ij ∈ S, ⟪p ij.1, p ij.2⟫ = u ∧ ij.1 ≠ ij.2)
    (hu : 0 < u) (hκ : KappaBound p S κ0) (hr : Real.sqrt (n : ℝ) * r * (1.01 * (1 + u)) < κ0)
    (hr2 : (n : ℝ) * r ^ 2 < 0.02) (hr0 : 0 ≤ r)
    (x : Fin n → E3) (hx : ∀ i, ‖x i‖ = 1) (R : E3 ≃ₗᵢ[ℝ] E3) (hxR : ∀ i, ‖x i - R (p i)‖ ≤ r) :
    (∃ R₀ : E3 ≃ₗᵢ[ℝ] E3, ∀ i, x i = R₀ (p i)) ∨ ∃ ij ∈ S, u < ⟪x ij.1, x ij.2⟫ := by
  -- Get the best orthogonal map R₀ for p, x
  obtain ⟨R₀, hR₀⟩ := exists_best_orthogonal p x
  set q := fun i : Fin n => R₀ (p i) with hq_def
  have hq_norm : ∀ i, ‖q i‖ = 1 := by
    intro i
    rw [hq_def]
    rw [LinearIsometryEquiv.norm_map]
    exact hp i
  have hq_inner : ∀ ij ∈ S, ⟪q ij.1, q ij.2⟫ = u := by
    intro ij hij
    rw [hq_def]
    rw [LinearIsometryEquiv.inner_map_map]
    exact (hS ij hij).1
  have hq_kappa : KappaBound q S κ0 := by
    rw [hq_def]
    exact kappaBound_orthogonal p S κ0 R₀ hκ
  have hq_cross : ∑ i : Fin n, cross (q i) (x i) = 0 := by
    rw [hq_def]
    exact best_orthogonal_cross p x R₀ hR₀
  -- Now prove the sum inequality: ∑ ‖x i - q i‖² ≤ n * r²
  have hsum : ∑ i : Fin n, ‖x i - q i‖ ^ 2 ≤ (n : ℝ) * r ^ 2 := by
    calc
      ∑ i : Fin n, ‖x i - q i‖ ^ 2 = ∑ i : Fin n, ‖x i - R₀ (p i)‖ ^ 2 := by
        simp [hq_def]
      _ ≤ ∑ i : Fin n, ‖x i - R (p i)‖ ^ 2 := by
        simpa [hq_def] using hR₀ R
      _ ≤ ∑ i : Fin n, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hxR_i := hxR i
        have hsq : ‖x i - R (p i)‖ ^ 2 ≤ r ^ 2 := by
          have hnorm_nonneg : 0 ≤ ‖x i - R (p i)‖ := norm_nonneg _
          nlinarith
        exact hsq
      _ = (n : ℝ) * r ^ 2 := by simp
  -- Apply chain_strict to get the conclusion
  have hchain := chain_strict q x S u κ0 r hq_norm hx hq_inner hu hq_kappa hr0 hsum hq_cross hr hr2
  rcases hchain with (h_all | h_contact)
  · -- Left alternative: ∀ i, x i = q i = R₀ (p i)
    left
    exact ⟨R₀, h_all⟩
  · -- Right alternative: ∃ ij ∈ S, u < ⟪x ij.1, x ij.2⟫
    right
    exact h_contact

/-- `κ` does not see the labels. -/
theorem kappaBound_relabel {n : ℕ} (p : Fin n → E3) (S S' : Finset (Fin n × Fin n)) (κ0 : ℝ)
    (σ : Fin n ≃ Fin n) (hS : ∀ ij ∈ S, (σ.symm ij.1, σ.symm ij.2) ∈ S')
    (h : KappaBound p S κ0) : KappaBound (fun i => p (σ i)) S' κ0 := by
  intro t' ht'
  rcases ht' with ⟨ht'_orth, ht'_cross⟩
  set t := fun i => t' (σ.symm i) with ht_def
  have ht_orth : ∀ i, ⟪p i, t i⟫ = 0 := by
    intro i
    dsimp [t]
    have := ht'_orth (σ.symm i)
    simpa using this
  have ht_cross : ∑ i, cross (p i) (t i) = 0 := by
    dsimp [t]
    calc
      ∑ i, cross (p i) (t' (σ.symm i)) = ∑ i, cross (p (σ i)) (t' i) := by
        simpa [σ.apply_symm_apply] using
          Equiv.sum_comp σ.symm (fun i => cross (p (σ i)) (t' i))
      _ = 0 := ht'_cross
  have ht : TPerp p t := ⟨ht_orth, ht_cross⟩
  rcases h t ht with ⟨ij, hij, hineq⟩
  set ij' := (σ.symm ij.1, σ.symm ij.2) with hij'_def
  have hij' : ij' ∈ S' := hS ij hij
  have hsum : ∑ i, ‖t' i‖ ^ 2 = ∑ i, ‖t i‖ ^ 2 := by
    dsimp [t]
    simpa using (Equiv.sum_comp σ.symm (fun i => ‖t' i‖ ^ 2)).symm
  have hlmap : Lmap (fun i => p (σ i)) t' ij' = Lmap p t ij := by
    dsimp [Lmap, t, ij']
    simp [σ.apply_symm_apply]
  refine ⟨ij', hij', ?_⟩
  simpa [hsum, hlmap] using hineq

/-- The radius condition of Theorem C, strict: `√15 · 1.04·10⁻³ · 1.01 (1 + u) < κ₀`. -/
theorem radius_lt (u : ℝ) (h0 : 0 < u) (hu : u < 0.5927) :
    Real.sqrt ((15 : ℕ) : ℝ) * rLocal * (1.01 * (1 + u)) < kappa0 := by
  have hsqrt15 : Real.sqrt ((15 : ℕ) : ℝ) < 3.873 := by
    have hsq : (15 : ℝ) < (3.873 : ℝ) ^ 2 := by norm_num
    exact ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3.873)).mpr hsq)
  have h_one_plus_u : 1 + u < 1.5927 := by linarith
  have hpos_rLocal : 0 < rLocal := by unfold rLocal; positivity
  have hpos_101 : 0 < (1.01 : ℝ) := by norm_num
  have hpos_1_plus_u : 0 < 1 + u := by linarith
  have h_mul1 : Real.sqrt ((15 : ℕ) : ℝ) * rLocal * (1.01 * (1 + u)) <
      3.873 * rLocal * (1.01 * (1 + u)) := by
    have hpos : 0 < rLocal * (1.01 * (1 + u)) := by positivity
    calc
      Real.sqrt ((15 : ℕ) : ℝ) * rLocal * (1.01 * (1 + u))
          = Real.sqrt ((15 : ℕ) : ℝ) * (rLocal * (1.01 * (1 + u))) := by ring
      _ < 3.873 * (rLocal * (1.01 * (1 + u))) := mul_lt_mul_of_pos_right hsqrt15 hpos
      _ = 3.873 * rLocal * (1.01 * (1 + u)) := by ring
  have h_mul2 : 3.873 * rLocal * (1.01 * (1 + u)) < 3.873 * rLocal * (1.01 * 1.5927) := by
    have hpos : 0 < 3.873 * rLocal := by positivity
    have hinner : 1.01 * (1 + u) < 1.01 * 1.5927 :=
      mul_lt_mul_of_pos_left h_one_plus_u hpos_101
    calc
      3.873 * rLocal * (1.01 * (1 + u))
          = (3.873 * rLocal) * (1.01 * (1 + u)) := by ring
      _ < (3.873 * rLocal) * (1.01 * 1.5927) := mul_lt_mul_of_pos_left hinner hpos
      _ = 3.873 * rLocal * (1.01 * 1.5927) := by ring
  have h_mul3 : 3.873 * rLocal * (1.01 * 1.5927) < kappa0 := by
    unfold rLocal kappa0
    norm_num
  linarith

theorem minAngle_le (x : Fin 15 → E3) (i j : Fin 15) (hij : i ≠ j) :
    minAngle x ≤ angle (x i) (x j) := by
  have hlt_or : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases hlt_or with (hlt | hlt)
  · have hmem : (i, j) ∈ (Finset.univ.filter (fun ij : Fin 15 × Fin 15 => ij.1 < ij.2)) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hlt⟩
    have hle := Finset.inf'_le (fun ij => angle (x ij.1) (x ij.2)) hmem
    simpa [minAngle] using hle
  · have hmem : (j, i) ∈ (Finset.univ.filter (fun ij : Fin 15 × Fin 15 => ij.1 < ij.2)) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hlt⟩
    have hle := Finset.inf'_le (fun ij => angle (x ij.1) (x ij.2)) hmem
    simpa [minAngle, angle_comm] using hle

theorem angle_le_of_le_inner (x y : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (u : ℝ)
    (h : u ≤ ⟪x, y⟫) : angle x y ≤ arccos u := by
  have h_angle_eq : angle x y = Real.arccos ⟪x, y⟫ := by
    unfold angle
    have h_norm_prod : ‖x‖ * ‖y‖ = 1 := by
      rw [hx, hy]
      norm_num
    rw [h_norm_prod, div_one]
  rw [h_angle_eq]
  exact Real.arccos_le_arccos h

theorem inner_le_of_arccos_le (x y : E3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (u : ℝ)
    (hu : -1 ≤ u ∧ u ≤ 1) (h : arccos u ≤ angle x y) : ⟪x, y⟫ ≤ u := by
  by_contra! hlt
  have hinner_abs_le_one : |⟪x, y⟫| ≤ 1 := by
    have h' := abs_real_inner_le_norm x y
    rw [hx, hy, mul_one] at h'
    exact h'
  have hinner_le_one : ⟪x, y⟫ ≤ 1 := by
    have := abs_le.mp hinner_abs_le_one
    exact this.2
  have hinner_ge_neg_one : -1 ≤ ⟪x, y⟫ := by
    have := abs_le.mp hinner_abs_le_one
    exact this.1
  have h_arccos_lt : arccos ⟪x, y⟫ < arccos u :=
    Real.arccos_lt_arccos hu.1 hlt hinner_le_one
  have h_angle_eq : angle x y = arccos ⟪x, y⟫ := by
    rw [InnerProductGeometry.angle, hx, hy, mul_one, div_one]
  rw [h_angle_eq] at h
  linarith

/-- Each frame configuration is the image of `C1` or `C3` under an element of `D`, on the indices. -/
theorem optima_four_idx (t : Fin 3 → Bool) :
    ∃ X : Bool, ∃ w : Fin 6, Finset.univ.image (fun m => dIdx w (keepX X m)) = frameIdx t := by
  revert t
  decide

/-- Theorem C as the paper states it, for the eight frame configurations, any labelling
and `r = rLocal = 1.04·10⁻³`, with `ψ* = arccos u`: the least distance is at most `ψ*`, with
equality only if the points are an orthogonal image of the frame configuration. -/
theorem local_optimality_frame (keep : Fin 15 → Fin 18) (hkeep : IsFrameKeep keep)
    (x : Fin 15 → E3) (hx : ∀ i, ‖x i‖ = 1) (R : E3 ≃ₗᵢ[ℝ] E3)
    (hxR : ∀ i, ‖x i - R (Attained.pt Attained.bR Attained.uR (keep i))‖ ≤ rLocal) :
    minAngle x ≤ arccos Attained.uR ∧
      (minAngle x = arccos Attained.uR →
        ∃ R' : E3 ≃ₗᵢ[ℝ] E3, ∀ i, x i = R' (Attained.pt Attained.bR Attained.uR (keep i))) := by
  obtain ⟨hinj, t, ht⟩ := hkeep
  obtain ⟨X, w, hXw⟩ := optima_four_idx t
  have hex : ∀ i, ∃ m, dIdx w (keepX X m) = keep i := by
    intro i
    have hi : keep i ∈ Finset.univ.image (fun m => dIdx w (keepX X m)) := by
      rw [hXw, ← ht]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
    exact ⟨m, hm⟩
  choose τ hτ using hex
  have hτinj : Function.Injective τ := by
    intro i j h
    apply hinj
    rw [← hτ i, ← hτ j, h]
  have hτbij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτinj
  set τe : Fin 15 ≃ Fin 15 := Equiv.ofBijective τ hτbij with hτe
  have hp : ∀ i, pt bR uR (keep i) = dWord w ((frameX X).p (τe i)) := by
    intro i
    rw [frameX_p, pt_dWord, hτe, Equiv.ofBijective_apply, hτ i]
  have hkX : KappaBound (frameX X).p (frameX X).S kappa0 := by
    cases X
    · exact Kappa.kappa_C1
    · exact Kappa.kappa_C3
  set S' : Finset (Fin 15 × Fin 15) :=
    Finset.univ.filter (fun ij => (τe ij.1, τe ij.2) ∈ (frameX X).S) with hS'
  have hκ : KappaBound (fun i => pt bR uR (keep i)) S' kappa0 := by
    have h1 : KappaBound (fun i => (frameX X).p (τe i)) S' kappa0 :=
      kappaBound_relabel (frameX X).p (frameX X).S S' kappa0 τe
        (by intro ij hij; simp [hS', hij]) hkX
    have h2 := kappaBound_orthogonal _ S' kappa0 (dWord w) h1
    have hfun : (fun i => pt bR uR (keep i)) = fun i => dWord w ((frameX X).p (τe i)) :=
      funext hp
    rw [hfun]
    exact h2
  have hq : ∀ i, ‖pt bR uR (keep i)‖ = 1 := by
    intro i
    rw [hp, LinearIsometryEquiv.norm_map, frameX_unit]
  have hS : ∀ ij ∈ S', ⟪pt bR uR (keep ij.1), pt bR uR (keep ij.2)⟫ = uR ∧ ij.1 ≠ ij.2 := by
    intro ij hij
    rw [hS', Finset.mem_filter] at hij
    obtain ⟨hne, hin⟩ := frameX_contact X _ hij.2
    refine ⟨?_, fun h => hne (by rw [h])⟩
    rw [hp, hp, LinearIsometryEquiv.inner_map_map]
    exact hin
  have hb := bounds_of_mem uR uR_spec.1
  have hu : 0 < uR := by linarith [hb.1]
  have huR : uR < 0.5927 := lt_of_le_of_lt uR_spec.1.2 (by norm_num [uh])
  have hr := radius_lt uR hu huR
  have hr2 : ((15 : ℕ) : ℝ) * rLocal ^ 2 < 0.02 := by
    unfold rLocal
    norm_num
  have hr0 : 0 ≤ rLocal := by
    unfold rLocal
    norm_num
  have hle : minAngle x ≤ arccos uR := by
    obtain ⟨ij, hij, hle⟩ := local_optimality (fun i => pt bR uR (keep i)) S' uR kappa0 rLocal hq
      hS hu hκ hr.le hr2 x hx R hxR
    exact (minAngle_le x ij.1 ij.2 (hS ij hij).2).trans
      (angle_le_of_le_inner _ _ (hx _) (hx _) uR hle)
  refine ⟨hle, fun heq => ?_⟩
  rcases local_optimality_strict (fun i => pt bR uR (keep i)) S' uR kappa0 rLocal hq hS hu hκ hr
      hr2 hr0 x hx R hxR with ⟨R₀, hR₀⟩ | ⟨ij, hij, hlt⟩
  · exact ⟨R₀, hR₀⟩
  · exfalso
    have hang := minAngle_le x ij.1 ij.2 (hS ij hij).2
    rw [heq] at hang
    have := inner_le_of_arccos_le (x ij.1) (x ij.2) (hx _) (hx _) uR
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ hang
    linarith

end Tammes15.PaperSteps
