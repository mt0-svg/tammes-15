import Tammes15.Statement

/-!
# Saturation

Paper, proof of Proposition 8.3, step (2): a finite `c`-separated set of unit vectors,
`c < 1`, extends to a finite `c`-separated set `S` of unit vectors that is saturated: every unit
vector has inner product above `c` with some point of `S`.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.FejesToth

/-- The separated sets of unit vectors at a level `c < 1` have bounded size. -/
theorem sep_card_bound (c : ℝ) (hc : c < 1) :
    ∃ N : ℕ, ∀ S : Finset E3, (∀ x ∈ S, ‖x‖ = 1) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ ≤ c) → S.card ≤ N := by
  have h_two_minus_two_c_pos : 0 < 2 - 2 * c := by linarith
  have he_pos : 0 < Real.sqrt (2 - 2 * c) / 2 := by
    refine div_pos (Real.sqrt_pos.mpr ?_) (by norm_num)
    linarith
  set e := Real.sqrt (2 - 2 * c) / 2 with he_def
  have h_two_e : 2 * e = Real.sqrt (2 - 2 * c) := by
    dsimp [e]
    ring
  have hsphere_compact : IsCompact (Metric.sphere (0 : E3) 1) :=
    isCompact_sphere (0 : E3) 1
  rcases finite_cover_balls_of_compact hsphere_compact he_pos with ⟨t, ht_sub, ht_fin, ht_cover⟩
  let N := ht_fin.toFinset.card
  refine ⟨N, λ S hS_norm hS_sep => ?_⟩
  have hS_sphere : ∀ x ∈ S, x ∈ Metric.sphere (0 : E3) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm]
    exact hS_norm x hx
  have hS_cover : ∀ x ∈ S, ∃ y ∈ t, x ∈ Metric.ball y e := by
    intro x hx
    have hx_sphere := hS_sphere x hx
    have hx_cover := ht_cover hx_sphere
    rcases Set.mem_iUnion₂.1 hx_cover with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  choose f hf_mem hf_ball using hS_cover
  let f' : E3 → E3 := fun x => if h : x ∈ S then f x h else 0
  have hf'_mem : ∀ x (hx : x ∈ S), f' x = f x hx := by
    intro x hx
    simp [f', hx]
  have hf'_ball : ∀ x ∈ S, x ∈ Metric.ball (f' x) e := by
    intro x hx
    rw [hf'_mem x hx]
    exact hf_ball x hx
  have hf_maps_to : Set.MapsTo f' (S : Set E3) (ht_fin.toFinset : Set E3) := by
    intro x hx
    simp [hf'_mem x hx, hf_mem x hx]
  have hf_inj : (S : Set E3).InjOn f' := by
    intro x hxS y hyS h_eq
    have h_eq_f : f x hxS = f y hyS := by
      rw [← hf'_mem x hxS, ← hf'_mem y hyS, h_eq]
    by_contra h_ne
    have hx_ball : x ∈ Metric.ball (f x hxS) e := hf_ball x hxS
    have hy_ball : y ∈ Metric.ball (f y hyS) e := hf_ball y hyS
    rw [← h_eq_f] at hy_ball
    have h_dist_x : dist x (f x hxS) < e := Metric.mem_ball.1 hx_ball
    have h_dist_y : dist y (f x hxS) < e := Metric.mem_ball.1 hy_ball
    have h_dist_xy : dist x y < 2 * e := by
      calc
        dist x y ≤ dist x (f x hxS) + dist (f x hxS) y := dist_triangle _ _ _
        _ = dist x (f x hxS) + dist y (f x hxS) := by rw [dist_comm (f x hxS) y]
        _ < e + e := by linarith
        _ = 2 * e := by ring
    have h_norm_xy_lt : ‖x - y‖ < 2 * e := by
      rwa [dist_eq_norm] at h_dist_xy
    have h_norm_sq_xy : ‖x - y‖ ^ 2 ≥ 2 - 2 * c := by
      have h1 := hS_norm x hxS
      have h2 := hS_norm y hyS
      have h_inner := hS_sep x hxS y hyS h_ne
      rw [norm_sub_sq_real]
      rw [h1, h2]
      nlinarith
    have h_norm_xy_ge : Real.sqrt (2 - 2 * c) ≤ ‖x - y‖ := by
      calc
        Real.sqrt (2 - 2 * c) ≤ Real.sqrt (‖x - y‖ ^ 2) :=
          Real.sqrt_le_sqrt h_norm_sq_xy
        _ = ‖x - y‖ := Real.sqrt_sq (norm_nonneg _)
    have h_contra : 2 * e < 2 * e := by
      calc
        2 * e = Real.sqrt (2 - 2 * c) := h_two_e
        _ ≤ ‖x - y‖ := h_norm_xy_ge
        _ < 2 * e := h_norm_xy_lt
    exact lt_irrefl _ h_contra
  have h_card : S.card ≤ ht_fin.toFinset.card :=
    Finset.card_le_card_of_injOn f' hf_maps_to hf_inj
  simpa [N] using h_card

/-- A saturated separated superset (Proposition 8.3, step (2)). -/
theorem exists_saturated (c : ℝ) (hc : c < 1) (X : Finset E3) (hX : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ⟪x, y⟫ ≤ c) :
    ∃ S : Finset E3, X ⊆ S ∧ (∀ x ∈ S, ‖x‖ = 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ ≤ c) ∧ ∀ u : E3, ‖u‖ = 1 → ∃ s ∈ S, c < ⟪u, s⟫ := by
  rcases sep_card_bound c hc with ⟨N, hN⟩
  have h_exists_saturated : ∀ (k : ℕ) (S : Finset E3), X ⊆ S → (∀ x ∈ S, ‖x‖ = 1) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫ ≤ c) → N - S.card ≤ k →
    ∃ S' : Finset E3, X ⊆ S' ∧ S ⊆ S' ∧ (∀ x ∈ S', ‖x‖ = 1) ∧
    (∀ x ∈ S', ∀ y ∈ S', x ≠ y → ⟪x, y⟫ ≤ c) ∧
    ∀ u : E3, ‖u‖ = 1 → ∃ s ∈ S', c < ⟪u, s⟫ := by
    intro k
    induction' k using Nat.strong_induction_on with k IH
    intro S hXS hS_norm hS_sep hk
    by_cases hsat : ∀ u : E3, ‖u‖ = 1 → ∃ s ∈ S, c < ⟪u, s⟫
    · exact ⟨S, hXS, Finset.Subset.refl S, hS_norm, hS_sep, hsat⟩
    · push Not at hsat
      rcases hsat with ⟨u, hu_norm, hu⟩
      have hu_not_mem : u ∉ S := by
        intro huS
        have hle := hu u huS
        have hself : ⟪u, u⟫ = 1 := by
          simpa [hu_norm] using inner_self_eq_norm_sq (𝕜 := ℝ) (E := E3) u
        linarith
      have h_insert_norm : ∀ x ∈ insert u S, ‖x‖ = 1 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with (rfl | hxS)
        · exact hu_norm
        · exact hS_norm x hxS
      have h_insert_sep : ∀ x ∈ insert u S, ∀ y ∈ insert u S, x ≠ y → ⟪x, y⟫ ≤ c := by
        intro x hx y hy hne
        have hx_cases := Finset.mem_insert.mp hx
        have hy_cases := Finset.mem_insert.mp hy
        rcases hx_cases with (hx_eq | hxS)
        · -- hx_eq : x = u
          subst hx_eq
          rcases hy_cases with (hy_eq | hyS)
          · -- hy_eq : y = u, contradicts hne
            subst hy_eq
            exfalso; exact hne rfl
          · -- y ∈ S
            exact hu y hyS
        · -- hxS : x ∈ S
          rcases hy_cases with (hy_eq | hyS)
          · -- hy_eq : y = u
            subst hy_eq
            simpa [real_inner_comm] using hu x hxS
          · -- y ∈ S
            exact hS_sep x hxS y hyS hne
      have hS_card_le_N : S.card ≤ N := hN S hS_norm hS_sep
      have h_insert_card_le_N : (insert u S).card ≤ N :=
        hN (insert u S) h_insert_norm h_insert_sep
      have h_card_eq : (insert u S).card = S.card + 1 := by
        simp [hu_not_mem]
      have hS_card_lt_N : S.card < N := by
        rw [h_card_eq] at h_insert_card_le_N
        omega
      have hk_lt : N - (insert u S).card < k := by
        omega
      have hX_insert : X ⊆ insert u S :=
        Finset.Subset.trans hXS (Finset.subset_insert u S)
      rcases IH (N - (insert u S).card) hk_lt (insert u S) hX_insert h_insert_norm h_insert_sep (le_refl _) with
        ⟨S', hXS', hSS', hS'_norm, hS'_sep, hS'_sat⟩
      exact ⟨S', hXS', Finset.Subset.trans (Finset.subset_insert u S) hSS', hS'_norm, hS'_sep, hS'_sat⟩
  have hcard : N - X.card ≤ N - X.card := le_refl _
  rcases h_exists_saturated (N - X.card) X (Finset.Subset.refl X) hX hsep hcard with
    ⟨S, hXS, _, hS_norm, hS_sep, hS_sat⟩
  exact ⟨S, hXS, hS_norm, hS_sep, hS_sat⟩

end Tammes15.FejesToth
