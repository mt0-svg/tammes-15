import Tammes15.Local41.Rotation

/-!
# Theorem C: the inequality chain and the orthogonal invariance of `κ`


`chain_conclusion` is the proof of Theorem C after the choice of the best
orthogonal map `R` (so `q i = R (p i)`, `∑ |x_i - q_i|² ≤ n r²` and the first order condition
`∑ q_i × x_i = 0`); `kappaBound_orthogonal` is the orthogonal invariance of `κ`. Improper maps need no separate
case: the minimum is taken over all orthogonal maps, and `κ` is invariant under all of them.
-/

open Real Matrix WithLp
open scoped RealInnerProductSpace

namespace Tammes15

theorem inner_sub_unit (p x : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ⟪p, x - p⟫ = -(‖x - p‖ ^ 2 / 2) := by
  have hnorm : ‖x - p‖ ^ 2 = 2 - 2 * ⟪p, x⟫ := by
    calc
      ‖x - p‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, p⟫ + ‖p‖ ^ 2 := by rw [norm_sub_sq_real]
      _ = ‖x‖ ^ 2 - 2 * ⟪p, x⟫ + ‖p‖ ^ 2 := by rw [real_inner_comm x p]
      _ = 2 - 2 * ⟪p, x⟫ := by rw [hp, hx]; ring
  have hinner : ⟪p, x - p⟫ = ⟪p, x⟫ - 1 := by
    calc
      ⟪p, x - p⟫ = ⟪p, x⟫ - ⟪p, p⟫ := by rw [inner_sub_right]
      _ = ⟪p, x⟫ - ‖p‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪p, x⟫ - 1 := by rw [hp]; norm_num
  calc
    ⟪p, x - p⟫ = ⟪p, x⟫ - 1 := hinner
    _ = ((2 - ‖x - p‖ ^ 2) / 2) - 1 := by
      have : ⟪p, x⟫ = (2 - ‖x - p‖ ^ 2) / 2 := by linarith
      rw [this]
    _ = -(‖x - p‖ ^ 2 / 2) := by ring

theorem inner_tpart (p x : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) : ⟪p, tpart p x⟫ = 0 := by
  dsimp [tpart]
  calc
    ⟪p, (x - p) + (‖x - p‖ ^ 2 / 2) • p⟫
        = ⟪p, x - p⟫ + ⟪p, (‖x - p‖ ^ 2 / 2) • p⟫ := by rw [inner_add_right]
    _ = ⟪p, x - p⟫ + ((‖x - p‖ ^ 2 / 2) * ⟪p, p⟫) := by rw [inner_smul_right]
    _ = ⟪p, x - p⟫ + ((‖x - p‖ ^ 2 / 2) * ‖p‖ ^ 2) := by rw [real_inner_self_eq_norm_sq]
    _ = ⟪p, x - p⟫ + ((‖x - p‖ ^ 2 / 2) * (‖p‖ ^ 2)) := by ring
    _ = (-(‖x - p‖ ^ 2 / 2)) + ((‖x - p‖ ^ 2 / 2) * (‖p‖ ^ 2)) := by rw [inner_sub_unit p x hp hx]
    _ = (-(‖x - p‖ ^ 2 / 2)) + ((‖x - p‖ ^ 2 / 2) * (1 ^ 2)) := by rw [hp]
    _ = (-(‖x - p‖ ^ 2 / 2)) + ((‖x - p‖ ^ 2 / 2) * 1) := by ring
    _ = (-(‖x - p‖ ^ 2 / 2)) + (‖x - p‖ ^ 2 / 2) := by ring
    _ = 0 := by ring

theorem norm_tpart_sq (p x : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ‖tpart p x‖ ^ 2 = ‖x - p‖ ^ 2 * (1 - ‖x - p‖ ^ 2 / 4) := by
  set v := x - p with hv
  set s := ‖v‖ ^ 2 with hs
  set c := s / 2 with hc
  calc
    ‖tpart p x‖ ^ 2 = ‖v + c • p‖ ^ 2 := by
      dsimp [tpart, v, c, s]
    _ = ‖v‖ ^ 2 + 2 * inner ℝ v (c • p) + ‖c • p‖ ^ 2 := by rw [norm_add_sq_real]
    _ = ‖v‖ ^ 2 + 2 * (c * inner ℝ v p) + ‖c • p‖ ^ 2 := by rw [inner_smul_right]
    _ = ‖v‖ ^ 2 + 2 * (c * inner ℝ v p) + ((‖c‖ * ‖p‖) ^ 2) := by rw [norm_smul]
    _ = ‖v‖ ^ 2 + 2 * (c * inner ℝ v p) + (c ^ 2 * ‖p‖ ^ 2) := by
      simp [mul_pow]
    _ = ‖v‖ ^ 2 + 2 * (c * inner ℝ v p) + (c ^ 2 * 1 ^ 2) := by rw [hp]
    _ = ‖v‖ ^ 2 + 2 * (c * inner ℝ v p) + c ^ 2 := by norm_num
    _ = s + 2 * (c * inner ℝ v p) + c ^ 2 := by rw [hs]
    _ = s + 2 * ((s / 2) * inner ℝ v p) + (s / 2) ^ 2 := by rw [hc]
    _ = s + 2 * ((s / 2) * inner ℝ v p) + (s ^ 2 / 4) := by ring
    _ = s + (s * inner ℝ v p) + (s ^ 2 / 4) := by ring
    _ = s * (1 - s / 4) := by
      have hinner : inner ℝ v p = -(s / 2) := by
        calc
          inner ℝ v p = inner ℝ p v := by rw [real_inner_comm]
          _ = inner ℝ p (x - p) := by rw [hv]
          _ = -(‖x - p‖ ^ 2 / 2) := by rw [inner_sub_unit p x hp hx]
          _ = -(s / 2) := by rw [hs, hv]
      rw [hinner]
      ring
    _ = ‖x - p‖ ^ 2 * (1 - ‖x - p‖ ^ 2 / 4) := by rw [hs, hv]

theorem norm_tpart_sq_le (p x : E3) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ‖tpart p x‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
  have h := norm_tpart_sq p x hp hx
  rw [h]
  set s := ‖x - p‖ ^ 2 with hs
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    apply pow_two_nonneg
  nlinarith

theorem sq_le_of_small (s : ℝ) (hs : 0 ≤ s ∧ s < 0.02) : s ≤ 1.01 * (s * (1 - s / 4)) := by
  rcases hs with ⟨hs0, hs1⟩
  nlinarith

/-- The contact inner product to second order, with the error bounded below. -/
theorem inner_sub_ge (p q x y : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (⟪p, tpart q y⟫ + ⟪q, tpart p x⟫) - (1 + ⟪p, q⟫) / 2 * (‖x - p‖ ^ 2 + ‖y - q‖ ^ 2) ≤
      ⟪x, y⟫ - ⟪p, q⟫ := by
  set v := x - p with hv
  set w := y - q with hw
  have hx_eq : x = p + v := by
    dsimp [v]
    abel
  have hy_eq : y = q + w := by
    dsimp [w]
    abel
  have htpart_p : tpart p x = v + (‖v‖ ^ 2 / 2) • p := by
    dsimp [tpart, v]
  have htpart_q : tpart q y = w + (‖w‖ ^ 2 / 2) • q := by
    dsimp [tpart, w]
  rw [htpart_p, htpart_q, hx_eq, hy_eq]
  simp only [inner_add_right, inner_add_left, inner_smul_right]
  rw [real_inner_comm q p, real_inner_comm q v]
  have h_abs := abs_real_inner_le_norm v w
  have h_abs_lower : -‖v‖ * ‖w‖ ≤ ⟪v, w⟫ := by
    have := (abs_le.mp h_abs).1
    linarith
  have h_two_mul : ‖v‖ * ‖w‖ ≤ (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    have h := two_mul_le_add_sq (‖v‖) (‖w‖)
    linarith
  nlinarith

theorem cross_tpart (p x : E3) : cross p (tpart p x) = cross p x := by
  simp [cross, tpart, cross_self, map_add, map_smul]

/-- Cross products and orthogonal maps: `(O a) × (O b) = det O • O (a × b)`. -/
theorem cross_isometry (O : E3 ≃ₗᵢ[ℝ] E3) (a b : E3) :
    cross (O a) (O b) = LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) • O (cross a b) := by
  set d := LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) with hd
  refine ext_inner_right ℝ ?_
  intro y
  set c := O.symm y with hc
  have hOc : O c = y := by
    rw [hc]
    exact LinearIsometryEquiv.apply_symm_apply O y
  calc
    ⟪cross (O a) (O b), y⟫ = ⟪cross (O a) (O b), O c⟫ := by rw [hOc]
    _ = Matrix.det ![ofLp (O a), ofLp (O b), ofLp (O c)] := by rw [inner_cross_eq_det]
    _ = LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) * Matrix.det ![ofLp a, ofLp b, ofLp c] := by
      simpa using det_rows_linearMap (O.toLinearEquiv : E3 →ₗ[ℝ] E3) a b c
    _ = d * Matrix.det ![ofLp a, ofLp b, ofLp c] := by rw [hd]
    _ = d * ⟪cross a b, c⟫ := by rw [inner_cross_eq_det]
    _ = ⟪d • O (cross a b), O c⟫ := by
      rw [inner_smul_left, LinearIsometryEquiv.inner_map_map]
      simp
    _ = ⟪d • O (cross a b), y⟫ := by rw [hOc]

/-- `κ` is invariant under every orthogonal map. -/
theorem kappaBound_orthogonal {n : ℕ} (p : Fin n → E3) (S : Finset (Fin n × Fin n)) (κ0 : ℝ)
    (O : E3 ≃ₗᵢ[ℝ] E3) (h : KappaBound p S κ0) : KappaBound (fun i => O (p i)) S κ0 := by
  intro t ht
  rcases ht with ⟨ht_inner, ht_sum⟩
  let t' : Fin n → E3 := fun i => O.symm (t i)
  have inner_symm_eq : ∀ x y : E3, ⟪x, O.symm y⟫ = ⟪O x, y⟫ := by
    intro x y
    calc
      ⟪x, O.symm y⟫ = ⟪O x, O (O.symm y)⟫ := by rw [LinearIsometryEquiv.inner_map_map]
      _ = ⟪O x, y⟫ := by rw [O.apply_symm_apply]
  have h_inner : ∀ i, ⟪p i, t' i⟫ = 0 := by
    intro i
    calc
      ⟪p i, t' i⟫ = ⟪p i, O.symm (t i)⟫ := rfl
      _ = ⟪O (p i), t i⟫ := by rw [inner_symm_eq]
      _ = 0 := ht_inner i
  have h_norm : ∀ i, ‖t' i‖ = ‖t i‖ := by
    intro i
    calc
      ‖t' i‖ = ‖O.symm (t i)‖ := rfl
      _ = ‖t i‖ := by rw [LinearIsometryEquiv.norm_map]
  have h_lmap : ∀ (ij : Fin n × Fin n), Lmap p t' ij = Lmap (fun i => O (p i)) t ij := by
    intro ij
    dsimp [Lmap]
    calc
      ⟪p ij.1, t' ij.2⟫ + ⟪p ij.2, t' ij.1⟫
          = (⟪p ij.1, O.symm (t ij.2)⟫ + ⟪p ij.2, O.symm (t ij.1)⟫) := rfl
      _ = (⟪O (p ij.1), t ij.2⟫ + ⟪O (p ij.2), t ij.1⟫) := by
        simp [inner_symm_eq]
      _ = Lmap (fun i => O (p i)) t ij := rfl
  have h_sum : ∑ i, cross (p i) (t' i) = 0 := by
    have h_det_ne_zero : LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) ≠ 0 := by
      have h_unit : IsUnit (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) :=
        LinearEquiv.isUnit_det' (O.toLinearEquiv)
      exact h_unit.ne_zero
    have h_cross_eq : ∀ i, cross (O (p i)) (t i) =
        (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • O (cross (p i) (t' i)) := by
      intro i
      calc
        cross (O (p i)) (t i) = cross (O (p i)) (O (t' i)) := by rw [O.apply_symm_apply]
        _ = (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • O (cross (p i) (t' i)) :=
          by rw [cross_isometry O (p i) (t' i)]
    have h_sum_eq : ∑ i, cross (O (p i)) (t i) =
        (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • O (∑ i, cross (p i) (t' i)) := by
      calc
        ∑ i, cross (O (p i)) (t i) =
            ∑ i, ((LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • O (cross (p i) (t' i))) := by
          simp_rw [h_cross_eq]
        _ = (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • (∑ i, O (cross (p i) (t' i))) := by
          rw [Finset.smul_sum]
        _ = (LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3)) • O (∑ i, cross (p i) (t' i)) := by
          rw [map_sum]
    rw [h_sum_eq] at ht_sum
    have h_O_zero : O (∑ i, cross (p i) (t' i)) = 0 := by
      rcases smul_eq_zero.mp ht_sum with (hdet | hO)
      · exact absurd hdet h_det_ne_zero
      · exact hO
    have h_inj : Function.Injective O := LinearIsometryEquiv.injective O
    apply h_inj
    simpa using h_O_zero
  have ht'_tperp : TPerp p t' := ⟨h_inner, h_sum⟩
  rcases h t' ht'_tperp with ⟨ij, hij, h_ineq⟩
  refine ⟨ij, hij, ?_⟩
  have h_sum_norm : (∑ i : Fin n, ‖t' i‖ ^ 2) = (∑ i : Fin n, ‖t i‖ ^ 2) := by
    simp_rw [h_norm]
  calc
    κ0 * Real.sqrt (∑ i : Fin n, ‖t i‖ ^ 2) = κ0 * Real.sqrt (∑ i : Fin n, ‖t' i‖ ^ 2) := by
      rw [h_sum_norm]
    _ ≤ Lmap p t' ij := h_ineq
    _ = Lmap (fun i => O (p i)) t ij := by rw [h_lmap ij]

/-- Theorem C after the choice of the best orthogonal map. -/
theorem chain_conclusion {n : ℕ} (q x : Fin n → E3) (S : Finset (Fin n × Fin n)) (u κ0 r : ℝ)
    (hq : ∀ i, ‖q i‖ = 1) (hx : ∀ i, ‖x i‖ = 1) (hS : ∀ ij ∈ S, ⟪q ij.1, q ij.2⟫ = u)
    (hu : 0 < u) (hκ : KappaBound q S κ0) (hr0 : 0 ≤ r)
    (hsum : ∑ i, ‖x i - q i‖ ^ 2 ≤ n * r ^ 2) (hcross : ∑ i, cross (q i) (x i) = 0)
    (hr : Real.sqrt n * r * (1.01 * (1 + u)) ≤ κ0) (hr2 : (n : ℝ) * r ^ 2 < 0.02) :
    ∃ ij ∈ S, u ≤ ⟪x ij.1, x ij.2⟫ := by
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
      -- hsum : ∑ i, ‖x i - q i‖ ^ 2 ≤ n * r ^ 2  where n : ℕ is auto-cast to ℝ
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
        -- hsum : ∑ i, ‖x i - q i‖ ^ 2 ≤ n * r ^ 2  (n auto-cast)
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
  -- hκij : κ0 * Real.sqrt (∑ i, ‖t i‖ ^ 2) ≤ Lmap q t ij
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
  -- h_inner : Lmap q t ij - (1 + u) / 2 * (s ij.1 + s ij.2) ≤ ⟪x ij.1, x ij.2⟫ - u
  have h_nonneg_u : 0 ≤ u := by linarith
  have h_factor_nonneg : 0 ≤ 1.01 * (1 + u) := by nlinarith
  have h_T_bound : 1.01 * (1 + u) * T ≤ κ0 := by
    have h_mul : 1.01 * (1 + u) * T ≤ 1.01 * (1 + u) * (Real.sqrt (n : ℝ) * r) := by
      nlinarith
    have h_eq : 1.01 * (1 + u) * (Real.sqrt (n : ℝ) * r) = Real.sqrt (n : ℝ) * r * (1.01 * (1 + u)) := by ring
    rw [h_eq] at h_mul
    have h_hr : Real.sqrt (n : ℝ) * r * (1.01 * (1 + u)) ≤ κ0 := hr
    linarith
  have h_main : u ≤ ⟪x ij.1, x ij.2⟫ := by
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
    have h_nonneg_factor2 : 0 ≤ κ0 - 1.01 * (1 + u) * T := by linarith
    have h_nonneg_prod : 0 ≤ T * (κ0 - 1.01 * (1 + u) * T) := by
      nlinarith
    have h_final : 0 ≤ κ0 * T - (1 + u) / 2 * (s ij.1 + s ij.2) := by
      linarith
    linarith
  exact ⟨ij, hijS, h_main⟩

/-- Rotations about the axis `ω` at angular speed `|ω|`, as a curve of orthogonal maps. -/
theorem exists_rotation_curve (ω : E3) :
    ∃ Q : ℝ → (E3 ≃ₗᵢ[ℝ] E3), (∀ v, Q 0 v = v) ∧
      ∀ v, HasDerivAt (fun θ => Q θ v) (cross ω v) 0 := by
  by_cases hω0 : ω = 0
  · -- case ω = 0
    refine ⟨fun _ => LinearIsometryEquiv.refl ℝ E3, ?_, ?_⟩
    · intro v; simp
    · intro v
      rw [hω0]
      have hcross0 : cross (0 : E3) v = 0 := by
        simp [cross]
      simp [hcross0, hasDerivAt_const]
  · -- case ω ≠ 0
    have hs_pos : 0 < ‖ω‖ := (norm_pos_iff.mpr hω0)
    set s := ‖ω‖ with hs_def
    have hs_ne_zero : s ≠ 0 := by linarith
    set u := s⁻¹ • ω with hu_def
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹), hs_def]
      field_simp [hs_ne_zero]
    have hrodrigues_zero : ∀ v, rodrigues u 0 v = v := rodrigues_zero u
    have hderiv : ∀ v, HasDerivAt (fun θ => rodrigues u (s * θ) v) (s • cross u v) 0 :=
      fun v => hasDerivAt_rodrigues u v s
    refine ⟨fun θ => Classical.choose (exists_rodrigues_isometry u hu_norm (s * θ)), ?_, ?_⟩
    · intro v
      have h := Classical.choose_spec (exists_rodrigues_isometry u hu_norm (s * 0))
      rw [h v]
      rw [mul_zero, hrodrigues_zero v]
    · intro v
      have h_choose : ∀ (θ : ℝ), (Classical.choose (exists_rodrigues_isometry u hu_norm (s * θ))) v =
                              rodrigues u (s * θ) v := by
        intro θ
        exact (Classical.choose_spec (exists_rodrigues_isometry u hu_norm (s * θ))) v
      have h_eq : (fun θ => (Classical.choose (exists_rodrigues_isometry u hu_norm (s * θ))) v) =
                 (fun θ => rodrigues u (s * θ) v) := by
        funext θ; exact h_choose θ
      rw [h_eq]
      have hderiv_at := hderiv v
      have hcross_eq : cross ω v = s • cross u v := by
        calc
          cross ω v = cross (s • (s⁻¹ • ω)) v := by
            rw [smul_smul, mul_inv_cancel₀ hs_ne_zero, one_smul]
          _ = cross (s • u) v := by rw [hu_def]
          _ = s • cross u v := cross_smul_left u v s
      rw [hcross_eq]
      exact hderiv_at

/-- A best orthogonal map exists. -/
theorem exists_best_orthogonal {n : ℕ} (p x : Fin n → E3) :
    ∃ R : E3 ≃ₗᵢ[ℝ] E3, ∀ R' : E3 ≃ₗᵢ[ℝ] E3,
      ∑ i, ‖x i - R (p i)‖ ^ 2 ≤ ∑ i, ‖x i - R' (p i)‖ ^ 2 := by
  -- The set of orthogonal linear maps (as continuous linear maps)
  let K : Set (E3 →L[ℝ] E3) := {A | ∀ v, ‖A v‖ = ‖v‖}
  have hK_nonempty : K.Nonempty := by
    refine ⟨ContinuousLinearMap.id ℝ E3, λ v => ?_⟩
    simp
  have hK_closed : IsClosed K := by
    have h_eq : K = ⋂ (v : E3), {A : E3 →L[ℝ] E3 | ‖A v‖ = ‖v‖} := by
      ext A; simp [K]
    rw [h_eq]
    refine isClosed_iInter (λ v => ?_)
    have h_preimage : {A : E3 →L[ℝ] E3 | ‖A v‖ = ‖v‖} = (λ A : E3 →L[ℝ] E3 => ‖A v‖) ⁻¹' {‖v‖} := by
      ext A; simp
    rw [h_preimage]
    refine IsClosed.preimage ?_ isClosed_singleton
    -- A ↦ ‖A v‖ is continuous
    have h_apply_cont : Continuous (λ (A : E3 →L[ℝ] E3) => A v) :=
      ((ContinuousLinearMap.apply ℝ E3) v).continuous
    exact Continuous.norm h_apply_cont
  have hK_bounded : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1, λ A hA => ?_⟩
    have h_norm_bound : ‖A‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound A (M := 1) (by norm_num) (λ v => ?_)
      rw [hA v]
      simp
    exact h_norm_bound
  have hK_compact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded
  -- The objective function
  let f : (E3 →L[ℝ] E3) → ℝ := λ A => ∑ i, ‖x i - A (p i)‖ ^ 2
  have hf_cont : ContinuousOn f K := by
    have hf_cont_all : Continuous f := by
      refine continuous_finsetSum _ (λ i _ => ?_)
      have h_apply_cont : Continuous (λ (A : E3 →L[ℝ] E3) => A (p i)) :=
        ((ContinuousLinearMap.apply ℝ E3) (p i)).continuous
      have h_sub_cont : Continuous (λ (A : E3 →L[ℝ] E3) => x i - A (p i)) :=
        Continuous.sub continuous_const h_apply_cont
      have h_norm_cont : Continuous (λ (A : E3 →L[ℝ] E3) => ‖x i - A (p i)‖) :=
        Continuous.norm h_sub_cont
      exact Continuous.pow h_norm_cont 2
    exact hf_cont_all.continuousOn
  -- Get a minimizer of f on K
  obtain ⟨A₀, hA₀K, hA₀min⟩ := hK_compact.exists_isMinOn hK_nonempty hf_cont
  -- A₀ is a linear isometry
  let li : E3 →ₗᵢ[ℝ] E3 :=
    { toLinearMap := A₀.toLinearMap
      norm_map' := hA₀K }
  -- Convert to linear isometry equivalence using finite dimension
  have h_finrank : Module.finrank ℝ E3 = Module.finrank ℝ E3 := rfl
  let R : E3 ≃ₗᵢ[ℝ] E3 := li.toLinearIsometryEquiv h_finrank
  refine ⟨R, λ R' => ?_⟩
  -- Show that R minimizes the sum
  -- First, note that R (p i) = A₀ (p i)
  have hR_eq_A₀ (v : E3) : R v = A₀ v := by
    simp [R, li]
  -- For any R', R'.toContinuousLinearEquiv is in K
  have hR'_mem_K (R' : E3 ≃ₗᵢ[ℝ] E3) : (R'.toContinuousLinearEquiv : E3 →L[ℝ] E3) ∈ K := by
    intro v
    -- Need ‖R'.toContinuousLinearEquiv v‖ = ‖v‖
    -- R'.toContinuousLinearEquiv is a ContinuousLinearEquiv, but we need it as a function
    -- Actually, R'.toContinuousLinearEquiv v = R' v
    -- and ‖R' v‖ = ‖v‖ by LinearIsometryEquiv.norm_map
    simp
  -- Now, hA₀min says A₀ minimizes f on K
  -- So f A₀ ≤ f (R'.toContinuousLinearEquiv)
  have h_min : f A₀ ≤ f (R'.toContinuousLinearEquiv) :=
    (Filter.eventually_principal.mp hA₀min) (R'.toContinuousLinearEquiv) (hR'_mem_K R')
  -- Expand both sides
  -- f A₀ = ∑ ‖x i - A₀ (p i)‖² = ∑ ‖x i - R (p i)‖²
  -- f (R'.toContinuousLinearEquiv) = ∑ ‖x i - R'.toContinuousLinearEquiv (p i)‖² = ∑ ‖x i - R' (p i)‖²
  simpa [f, hR_eq_A₀] using h_min

/-- The first order condition at a best orthogonal map. -/
theorem best_orthogonal_cross {n : ℕ} (p x : Fin n → E3) (R : E3 ≃ₗᵢ[ℝ] E3)
    (hR : ∀ R' : E3 ≃ₗᵢ[ℝ] E3, ∑ i, ‖x i - R (p i)‖ ^ 2 ≤ ∑ i, ‖x i - R' (p i)‖ ^ 2) :
    ∑ i, cross (R (p i)) (x i) = 0 := by
  set c := ∑ i, cross (R (p i)) (x i) with hc_def
  have h_cross_self (v : E3) : cross v v = 0 := by
    simp [cross, cross_self]
  have h_inner : ⟪c, c⟫ = 0 := by
    obtain ⟨Q, hQ0, hQderiv⟩ := exists_rotation_curve c
    set g := fun (θ : ℝ) => ∑ i, ‖x i - Q θ (R (p i))‖ ^ 2 with hg_def
    have hg_min : ∀ θ, g 0 ≤ g θ := by
      intro θ
      have h0 : g 0 = ∑ i, ‖x i - R (p i)‖ ^ 2 := by
        simp [g, hQ0]
      have hθ : g θ = ∑ i, ‖x i - (R.trans (Q θ)) (p i)‖ ^ 2 := by
        simp [g, LinearIsometryEquiv.trans_apply]
      rw [h0, hθ]
      exact hR (R.trans (Q θ))
    have h_local_min : IsLocalMin g 0 := by
      have h_min_on : IsMinOn g Set.univ 0 := by
        intro θ hθ
        exact hg_min θ
      exact h_min_on.isLocalMin (Filter.univ_mem (f := nhds 0))
    have h_deriv : HasDerivAt g (-2 * ⟪c, c⟫) 0 := by
      have h_term (i : Fin n) : HasDerivAt (fun (θ : ℝ) => ‖x i - Q θ (R (p i))‖ ^ 2)
          (-2 * ⟪c, cross (R (p i)) (x i)⟫) 0 := by
        have h_f : HasDerivAt (fun (θ : ℝ) => x i - Q θ (R (p i))) (-(cross c (R (p i)))) 0 := by
          convert HasDerivAt.sub (hasDerivAt_const 0 (x i)) (hQderiv (R (p i))) using 1
          simp
        have h_norm_sq : HasDerivAt (fun (θ : ℝ) => ‖x i - Q θ (R (p i))‖ ^ 2)
            (2 * ⟪x i - Q 0 (R (p i)), -(cross c (R (p i)))⟫) 0 :=
          h_f.norm_sq
        have h_Q0 : Q 0 (R (p i)) = R (p i) := hQ0 (R (p i))
        rw [h_Q0] at h_norm_sq
        have h_simp : (2 * ⟪x i - R (p i), -(cross c (R (p i)))⟫) = (-2 * ⟪c, cross (R (p i)) (x i)⟫) := by
          calc
            (2 * ⟪x i - R (p i), -(cross c (R (p i)))⟫) = (-2 * ⟪x i - R (p i), cross c (R (p i))⟫) := by
              simp [inner_neg_right]
            _ = (-2 * (⟪x i, cross c (R (p i))⟫ - ⟪R (p i), cross c (R (p i))⟫)) := by
              rw [inner_sub_left]
            _ = (-2 * (⟪x i, cross c (R (p i))⟫ - ⟪c, cross (R (p i)) (R (p i))⟫)) := by
              rw [inner_cross_perm (R (p i)) c (R (p i))]
            _ = (-2 * (⟪x i, cross c (R (p i))⟫ - ⟪c, 0⟫)) := by
              rw [h_cross_self (R (p i))]
            _ = (-2 * (⟪x i, cross c (R (p i))⟫ - 0)) := by simp
            _ = (-2 * ⟪x i, cross c (R (p i))⟫) := by ring
            _ = (-2 * ⟪c, cross (R (p i)) (x i)⟫) := by simp [inner_cross_perm]
        rw [h_simp] at h_norm_sq
        exact h_norm_sq
      have h_sum : HasDerivAt (fun (θ : ℝ) => ∑ i : Fin n, ‖x i - Q θ (R (p i))‖ ^ 2)
          (∑ i : Fin n, (-2 * ⟪c, cross (R (p i)) (x i)⟫)) 0 := by
        have h := HasDerivAt.sum (u := Finset.univ) (A := fun (i : Fin n) (θ : ℝ) => ‖x i - Q θ (R (p i))‖ ^ 2)
          (A' := fun i => -2 * ⟪c, cross (R (p i)) (x i)⟫) (fun i hi => h_term i)
        have h_eq : (∑ i : Fin n, fun (θ : ℝ) => ‖x i - Q θ (R (p i))‖ ^ 2) =
            (fun (θ : ℝ) => ∑ i : Fin n, ‖x i - Q θ (R (p i))‖ ^ 2) := by
          funext θ; simp
        simpa [h_eq] using h
      have h_sum_simp : (∑ i : Fin n, (-2 * ⟪c, cross (R (p i)) (x i)⟫)) = -2 * ⟪c, c⟫ := by
        calc
          (∑ i : Fin n, (-2 * ⟪c, cross (R (p i)) (x i)⟫)) = (-2 * (∑ i : Fin n, ⟪c, cross (R (p i)) (x i)⟫)) := by
            simp [Finset.mul_sum]
          _ = (-2 * ⟪c, (∑ i : Fin n, cross (R (p i)) (x i))⟫) := by
            rw [inner_sum]
          _ = (-2 * ⟪c, c⟫) := by rw [hc_def]
      rw [h_sum_simp] at h_sum
      simpa [g] using h_sum
    have h_deriv_zero : -2 * ⟪c, c⟫ = 0 :=
      h_local_min.hasDerivAt_eq_zero h_deriv
    linarith
  have h_c_zero : c = 0 := by
    exact (inner_self_eq_zero (𝕜 := ℝ) (x := c)).mp h_inner
  simpa [hc_def] using h_c_zero

/-- Theorem C for an abstract frame `p` with contact set `S` at inner product `u`
(paper, Theorem C). -/
theorem local_optimality {n : ℕ} (p : Fin n → E3) (S : Finset (Fin n × Fin n)) (u κ0 r : ℝ)
    (hp : ∀ i, ‖p i‖ = 1) (hS : ∀ ij ∈ S, ⟪p ij.1, p ij.2⟫ = u ∧ ij.1 ≠ ij.2)
    (hu : 0 < u) (hκ : KappaBound p S κ0) (hr : Real.sqrt (n : ℝ) * r * (1.01 * (1 + u)) ≤ κ0)
    (hr2 : (n : ℝ) * r ^ 2 < 0.02)
    (x : Fin n → E3) (hx : ∀ i, ‖x i‖ = 1) (R : E3 ≃ₗᵢ[ℝ] E3) (hxR : ∀ i, ‖x i - R (p i)‖ ≤ r) :
    ∃ ij ∈ S, u ≤ ⟪x ij.1, x ij.2⟫ := by
  -- First, prove 0 ≤ r
  have hr0 : 0 ≤ r := by
    by_cases hne : Nonempty (Fin n)
    · obtain ⟨i⟩ := hne
      have hnorm := norm_nonneg (x i - R (p i))
      have hxR_i := hxR i
      linarith
    · have hisEmpty : IsEmpty (Fin n) := not_nonempty_iff.mp hne
      have hSempty : S = ∅ := Finset.eq_empty_of_isEmpty S
      have hTPerp : TPerp p (fun _ : Fin n => 0) := by
        refine ⟨fun i => hisEmpty.elim i, ?_⟩
        simp
      have hcontra := hκ (fun _ : Fin n => 0) hTPerp
      rcases hcontra with ⟨ij, hij, _⟩
      rw [hSempty] at hij
      simp at hij
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
      ∑ i : Fin n, ‖x i - q i‖ ^ 2 ≤ ∑ i : Fin n, ‖x i - R (p i)‖ ^ 2 := by
        simpa [hq_def] using hR₀ R
      _ ≤ ∑ i : Fin n, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hxR_i := hxR i
        have hsq : ‖x i - R (p i)‖ ^ 2 ≤ r ^ 2 := by
          have hnorm_nonneg : 0 ≤ ‖x i - R (p i)‖ := norm_nonneg _
          nlinarith
        exact hsq
      _ = (n : ℝ) * r ^ 2 := by simp
  -- Now apply chain_conclusion
  exact chain_conclusion q x S u κ0 r hq_norm hx hq_inner hu hq_kappa hr0 hsum hq_cross hr hr2

end Tammes15
