import Tammes15.D2Regions.Arc
import Tammes15.Geom.Crofton
import Tammes15.Geom.Cover
import Tammes15.Geom.T8

/-!
# Strictly convex polygons in cone form (Lemma 3.20 of the paper)


For a polygon `A` in cone form (`Tammes15.Geom.IsCPoly`), the open polygon is
`{z | ‖z‖ = 1 ∧ Inside A z}`: nonempty, preconnected, with closure the closed polygon
`{z | ‖z‖ = 1 ∧ InClosed A z}`, whose difference with the open polygon is the union of the arcs of
the sides (`closedPoly_diff`). A preconnected set meeting the inside and the outside of the open
cone meets the boundary (`preconnected_meets_boundary`). The polygon step of the cover
(`fan_inClosed`): from a vertex `A 0` nearest to `z` among the vertices, with `z` in the corner
sector at `A 0`, contact sides and the packing bound, `z` lies in the closed polygon; the fan
triangle `(A 0, A j, A (j + 1))` whose cone holds `z` is found as in `IsCPoly.cone_of_inClosed`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open Tammes15.Geom

/-! ## The open and the closed polygon -/

/-- The open polygon is nonempty. -/
theorem poly_nonempty {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) :
    ∃ z : E3, ‖z‖ = 1 ∧ Inside A z := by
  have hm_pos : 0 < m := by
    have h3m : 3 ≤ m := hA.three
    omega
  set s := ∑ j ∈ Finset.range m, A j with hs
  have hs_inner_pos : ∀ i, 0 < ⟪cross (A i) (A (i + 1)), s⟫ := by
    intro i
    rw [hs, inner_sum]
    have h_nonneg : ∀ j, 0 ≤ ⟪cross (A i) (A (i + 1)), A j⟫ := by
      intro j
      have h_inclosed : InClosed A (A j) := hA.inClosed_vertex j
      exact h_inclosed i
    have h_pos_term : 0 < ⟪cross (A i) (A (i + 1)), A ((i + 2) % m)⟫ := by
      have h2_lt_m : 2 < m := by
        have h3m : 3 ≤ m := hA.three
        omega
      have h_support : 0 < ⟪cross (A i) (A (i + 1)), A (i + 2)⟫ :=
        hA.support i 2 (by omega) h2_lt_m
      rw [← hA.mod (i + 2)]
      exact h_support
    apply Finset.sum_pos'
    · intro j hj
      rw [Finset.mem_range] at hj
      exact h_nonneg j
    · refine ⟨(i + 2) % m, Finset.mem_range.mpr (Nat.mod_lt _ hm_pos), h_pos_term⟩
  have hs_ne_zero : s ≠ 0 := by
    intro hzero
    have hpos0 : 0 < ⟪cross (A 0) (A (0 + 1)), s⟫ := hs_inner_pos 0
    rw [hzero, inner_zero_right] at hpos0
    linarith
  set z := ‖s‖⁻¹ • s with hz
  refine ⟨z, ?_, ?_⟩
  · rw [hz]
    exact norm_smul_inv_norm hs_ne_zero
  · intro i
    rw [hz, real_inner_smul_right]
    have hpos_inner : 0 < ⟪cross (A i) (A (i + 1)), s⟫ := hs_inner_pos i
    have h_norm_pos : 0 < ‖s‖ := by
      rwa [norm_pos_iff]
    have h_inv_pos : 0 < ‖s‖⁻¹ := inv_pos.mpr h_norm_pos
    nlinarith

/-- The open polygon is preconnected (the radial projection of an open convex cone). -/
theorem poly_isPreconnected (A : ℕ → E3) : IsPreconnected {z : E3 | ‖z‖ = 1 ∧ Inside A z} := by
  set C : Set E3 := {y | Inside A y} with hC
  have hC_convex : Convex ℝ C := by
    intro y hy y' hy' a b ha hb hab
    intro i
    have hyi := hy i
    have hy'i := hy' i
    have hcalc : ⟪cross (A i) (A (i + 1)), a • y + b • y'⟫ =
        a * ⟪cross (A i) (A (i + 1)), y⟫ + b * ⟪cross (A i) (A (i + 1)), y'⟫ := by
      simp [inner_add_right, inner_smul_right]
    have hpos : 0 < a * ⟪cross (A i) (A (i + 1)), y⟫ + b * ⟪cross (A i) (A (i + 1)), y'⟫ := by
      by_cases ha' : a = 0
      · have hb' : b = 1 := by linarith
        rw [ha', hb']
        simp [hy'i]
      · have ha_pos : 0 < a := by
          by_contra! h
          apply ha'
          linarith
        by_cases hb' : b = 0
        · have ha'' : a = 1 := by linarith
          rw [hb', ha'']
          simp [hyi]
        · have hb_pos : 0 < b := by
            by_contra! h
            apply hb'
            linarith
          have h1 : 0 < a * ⟪cross (A i) (A (i + 1)), y⟫ := mul_pos ha_pos hyi
          have h2 : 0 < b * ⟪cross (A i) (A (i + 1)), y'⟫ := mul_pos hb_pos hy'i
          linarith
    rw [hcalc]
    exact hpos
  have hC_preconnected : IsPreconnected C := hC_convex.isPreconnected
  have h0_notin_C : (0 : E3) ∉ C := by
    intro h
    have h0 := h 0
    have hzero : ⟪cross (A 0) (A 1), (0 : E3)⟫ = 0 := by simp
    have hpos := h0
    linarith
  set f : E3 → E3 := fun y => ‖y‖⁻¹ • y with hf
  have h_image : f '' C = {z : E3 | ‖z‖ = 1 ∧ Inside A z} := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      have hy_norm_pos : 0 < ‖y‖ := by
        by_contra! h
        have h_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
        have hzero : ‖y‖ = 0 := by linarith
        have hy_eq_zero : y = 0 := norm_eq_zero.mp hzero
        rw [hy_eq_zero] at hy
        exact h0_notin_C hy
      have hnorm : ‖‖y‖⁻¹ • y‖ = 1 := by
        calc
          ‖‖y‖⁻¹ • y‖ = ‖(‖y‖⁻¹ : ℝ)‖ * ‖y‖ := norm_smul _ _
          _ = |‖y‖⁻¹| * ‖y‖ := by simp
          _ = ‖y‖⁻¹ * ‖y‖ := by rw [abs_of_pos (inv_pos.mpr hy_norm_pos)]
          _ = 1 := by field_simp [ne_of_gt hy_norm_pos]
      have hinside : Inside A (‖y‖⁻¹ • y) := by
        intro i
        have hyi := hy i
        have hpos' : 0 < ‖y‖⁻¹ * ⟪cross (A i) (A (i + 1)), y⟫ :=
          mul_pos (inv_pos.mpr hy_norm_pos) hyi
        simpa [real_inner_smul_right] using hpos'
      exact ⟨hnorm, hinside⟩
    · rintro ⟨hznorm, hzInside⟩
      have hzC : z ∈ C := hzInside
      refine ⟨z, hzC, ?_⟩
      dsimp [f]
      rw [hznorm]
      simp
  have h_cont : ContinuousOn f C := by
    have h_norm_cont : ContinuousOn (fun y : E3 => ‖y‖) C :=
      continuous_norm.continuousOn
    have h_norm_ne_zero : ∀ y ∈ C, ‖y‖ ≠ 0 := by
      intro y hy
      by_contra! h
      have hy_eq_zero : y = 0 := norm_eq_zero.mp h
      rw [hy_eq_zero] at hy
      exact h0_notin_C hy
    have h_inv_cont : ContinuousOn (fun y : E3 => (‖y‖)⁻¹) C :=
      h_norm_cont.inv₀ h_norm_ne_zero
    exact h_inv_cont.smul continuous_id.continuousOn
  have h_preconnected_image : IsPreconnected (f '' C) :=
    hC_preconnected.image f h_cont
  rw [h_image] at h_preconnected_image
  exact h_preconnected_image

/-- The closure of a nonempty open polygon is the closed polygon. -/
theorem closure_poly (A : ℕ → E3) (hne : ∃ w : E3, ‖w‖ = 1 ∧ Inside A w) :
    closure {z : E3 | ‖z‖ = 1 ∧ Inside A z} = {z : E3 | ‖z‖ = 1 ∧ InClosed A z} := by
  rcases hne with ⟨w, hw_norm, hw_inside⟩
  apply Set.Subset.antisymm
  · -- ⊆: closure of open polygon ⊆ closed polygon
    apply closure_minimal
    · -- open polygon ⊆ closed polygon
      intro z hz
      rcases hz with ⟨hz_norm, hz_inside⟩
      refine ⟨hz_norm, ?_⟩
      intro i
      exact le_of_lt (hz_inside i)
    · -- closed polygon is closed
      have h_closed_norm : IsClosed {z : E3 | ‖z‖ = 1} := by
        exact isClosed_eq continuous_norm continuous_const
      have h_closed_inner : IsClosed {z : E3 | InClosed A z} := by
        have h_eq : {z : E3 | InClosed A z} = ⋂ (i : ℕ), {z : E3 | 0 ≤ ⟪cross (A i) (A (i + 1)), z⟫} := by
          ext z; simp [InClosed, Set.mem_iInter]
        rw [h_eq]
        apply isClosed_iInter
        intro i
        have h_cont : Continuous (fun z : E3 => ⟪cross (A i) (A (i + 1)), z⟫) :=
          continuous_const.inner continuous_id
        exact isClosed_le continuous_const h_cont
      exact IsClosed.inter h_closed_norm h_closed_inner
  · -- ⊇: closed polygon ⊆ closure of open polygon
    intro z hz
    rcases hz with ⟨hz_norm, hz_inclosed⟩
    have hz_ne_zero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hz_norm
      linarith
    -- Define y(θ) = (1-θ)•z + θ•w
    set y : ℝ → E3 := fun θ => (1 - θ) • z + θ • w with hy_def
    have hy_cont : Continuous y := by
      unfold y; continuity
    have hy0 : y 0 = z := by
      dsimp [y]; simp
    -- For θ ∈ (0,1], the normalization of y(θ) lies in the open polygon
    have h_pos_cone : ∀ θ ∈ Set.Ioc (0 : ℝ) 1, ‖y θ‖⁻¹ • y θ ∈ {z : E3 | ‖z‖ = 1 ∧ Inside A z} := by
      intro θ hθ
      rcases hθ with ⟨hθ_pos, hθ_le_one⟩
      have hy_ne_zero : y θ ≠ 0 := by
        intro hzero
        have h_inner_pos : ∀ i, 0 < ⟪cross (A i) (A (i + 1)), y θ⟫ := by
          intro i
          dsimp [y]
          rw [inner_add_right, inner_smul_right, inner_smul_right]
          have hz_nonneg : 0 ≤ ⟪cross (A i) (A (i + 1)), z⟫ := hz_inclosed i
          have hw_pos : 0 < ⟪cross (A i) (A (i + 1)), w⟫ := hw_inside i
          have h1 : 0 ≤ (1 - θ) * ⟪cross (A i) (A (i + 1)), z⟫ :=
            mul_nonneg (by linarith) hz_nonneg
          have h2 : 0 < θ * ⟪cross (A i) (A (i + 1)), w⟫ :=
            mul_pos hθ_pos hw_pos
          nlinarith
        have hzero_inner : ∀ i, ⟪cross (A i) (A (i + 1)), (0 : E3)⟫ = 0 := by
          intro i; simp
        have h_contra := h_inner_pos 0
        rw [hzero, hzero_inner 0] at h_contra
        linarith
      have hy_norm_pos : 0 < ‖y θ‖ := norm_pos_iff.mpr hy_ne_zero
      refine ⟨?_, ?_⟩
      · -- ‖‖y θ‖⁻¹ • y θ‖ = 1
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : 0 ≤ ‖y θ‖)]
        field_simp [hy_norm_pos.ne.symm]
      · -- Inside A (‖y θ‖⁻¹ • y θ)
        intro i
        rw [inner_smul_right]
        have h_inner_pos : 0 < ⟪cross (A i) (A (i + 1)), y θ⟫ := by
          dsimp [y]
          rw [inner_add_right, inner_smul_right, inner_smul_right]
          have hz_nonneg : 0 ≤ ⟪cross (A i) (A (i + 1)), z⟫ := hz_inclosed i
          have hw_pos : 0 < ⟪cross (A i) (A (i + 1)), w⟫ := hw_inside i
          have h1 : 0 ≤ (1 - θ) * ⟪cross (A i) (A (i + 1)), z⟫ :=
            mul_nonneg (by linarith) hz_nonneg
          have h2 : 0 < θ * ⟪cross (A i) (A (i + 1)), w⟫ :=
            mul_pos hθ_pos hw_pos
          nlinarith
        have h_norm_pos : 0 < ‖y θ‖ := norm_pos_iff.mpr hy_ne_zero
        exact mul_pos (inv_pos_of_pos h_norm_pos) h_inner_pos
    -- Show that as θ → 0⁺, ‖y θ‖⁻¹ • y θ → z
    have h_tendsto : Filter.Tendsto (fun θ : ℝ => ‖y θ‖⁻¹ • y θ) (nhdsWithin 0 (Set.Ioc 0 1)) (nhds z) := by
      -- The normalization map g(x) = ‖x‖⁻¹ • x is continuous at z ≠ 0
      have hg_cont_at : ContinuousAt (fun x : E3 => ‖x‖⁻¹ • x) z := by
        have h_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
        have h_cont_inv_norm : ContinuousAt (fun x : E3 => (‖x‖)⁻¹) z :=
          continuous_norm.continuousAt.inv₀ h_norm_pos.ne.symm
        -- Now smul with identity
        exact h_cont_inv_norm.smul continuousAt_id
      have hg_tendsto : Filter.Tendsto (fun x : E3 => ‖x‖⁻¹ • x) (nhds z) (nhds (‖z‖⁻¹ • z)) :=
        hg_cont_at.tendsto
      have h_norm_z : ‖z‖⁻¹ • z = z := by
        simp [hz_norm]
      rw [h_norm_z] at hg_tendsto
      -- y(θ) → z as θ → 0
      have hy_tendsto_nhds : Filter.Tendsto y (nhds 0) (nhds z) := by
        simpa [hy0] using hy_cont.tendsto 0
      have hy_tendsto_ioc : Filter.Tendsto y (nhdsWithin 0 (Set.Ioc 0 1)) (nhds z) :=
        hy_tendsto_nhds.mono_left (by
          -- nhdsWithin 0 (Ioc 0 1) ≤ nhds 0 as filters
          -- This is true because Ioc 0 1 ⊆ {0}ᶜ... actually it's just a smaller set
          -- The lemma is: nhdsWithin_le_nhds
          -- But that's a lemma about sets, not filters
          -- We need: nhdsWithin a s ≤ nhds a
          -- This is true by definition of nhdsWithin
          exact inf_le_left)
      -- Compose: g(y(θ)) → g(z) = z
      -- Filter.Tendsto.comp : g → f → g ∘ f
      -- We have: hg_tendsto : Tendsto g (nhds z) (nhds z)
      --          hy_tendsto_ioc : Tendsto y (nhdsWithin 0 (Ioc 0 1)) (nhds z)
      -- Want: Tendsto (g ∘ y) (nhdsWithin 0 (Ioc 0 1)) (nhds z)
      apply Filter.Tendsto.comp hg_tendsto hy_tendsto_ioc
    -- Apply mem_closure_of_tendsto
    have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioc 0 1)).NeBot := by
      -- 0 < 1, so the left endpoint has a nonempty Ioc interval
      exact left_nhdsWithin_Ioc_neBot (by norm_num : (0 : ℝ) < 1)
    apply mem_closure_of_tendsto h_tendsto
    -- Need: ∀ᶠ θ in nhdsWithin 0 (Ioc 0 1), ...
    have h_mem : Set.Ioc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioc 0 1) :=
      self_mem_nhdsWithin
    apply Filter.mem_of_superset h_mem
    intro θ hθ
    exact h_pos_cone θ hθ

/-- A nonnegative combination of three vertices lies in the closed polygon. -/
theorem inClosed_of_cone {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (i j k : ℕ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : InClosed A (a • A i + b • A j + c • A k) := by
  intro l
  have hi : InClosed A (A i) := IsCPoly.inClosed_vertex hA i
  have hj : InClosed A (A j) := IsCPoly.inClosed_vertex hA j
  have hk : InClosed A (A k) := IsCPoly.inClosed_vertex hA k
  have hi' := hi l
  have hj' := hj l
  have hk' := hk l
  simp only [inner_add_right, real_inner_smul_right]
  nlinarith

/-- The closed polygon minus the open one is the union of the arcs of the sides. -/
theorem closedPoly_diff {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) :
    {z : E3 | ‖z‖ = 1 ∧ InClosed A z} \ {z : E3 | ‖z‖ = 1 ∧ Inside A z} =
      ⋃ i : ℕ, minorArc (A i) (A (i + 1)) := by
  ext z
  constructor
  · intro h
    rcases h with ⟨⟨hznorm, hzInClosed⟩, hzNotInside⟩
    have hzNotInside' : ¬ Inside A z := by
      intro hi
      apply hzNotInside
      exact ⟨hznorm, hi⟩
    have h_exists : ∃ i, ⟪cross (A i) (A (i + 1)), z⟫ = 0 := by
      have h_neg : ¬ ∀ i, 0 < ⟪cross (A i) (A (i + 1)), z⟫ := hzNotInside'
      push Not at h_neg
      rcases h_neg with ⟨i, hi⟩
      have hInClosed_i : 0 ≤ ⟪cross (A i) (A (i + 1)), z⟫ := hzInClosed i
      have hi_eq : ⟪cross (A i) (A (i + 1)), z⟫ = 0 := by linarith
      exact ⟨i, hi_eq⟩
    rcases h_exists with ⟨i, hi⟩
    have h_comb := hA.comb_of_side z hzInClosed i hi
    rcases h_comb with ⟨l, μ, hl, hμ, hz_eq⟩
    refine Set.mem_iUnion.mpr ⟨i, hznorm, l, μ, hl, hμ, hz_eq⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨i, hi_mem⟩
    rcases hi_mem with ⟨hznorm, s, t, hs, ht, hz_eq⟩
    have hInClosed : InClosed A z := by
      rw [hz_eq]
      have hcone := Tammes15.D2Regions.inClosed_of_cone hA i (i + 1) i s t 0 hs ht (by norm_num)
      simpa [add_zero] using hcone
    have hNotInside : z ∉ {z | ‖z‖ = 1 ∧ Inside A z} := by
      intro hzInside
      rcases hzInside with ⟨_, hInside⟩
      have hpos := hInside i
      rw [hz_eq] at hpos
      have hzero : ⟪cross (A i) (A (i + 1)), s • A i + t • A (i + 1)⟫ = 0 := by
        have h1 : ⟪cross (A i) (A (i + 1)), A i⟫ = 0 := by
          rw [cross_swap (A (i + 1)) (A i)]
          simp [inner_cross_right_zero]
        have h2 : ⟪cross (A i) (A (i + 1)), A (i + 1)⟫ = 0 := by
          simp [inner_cross_right_zero]
        simp [inner_add_right, inner_smul_right, h1, h2]
      rw [hzero] at hpos
      linarith
    exact ⟨⟨hznorm, hInClosed⟩, hNotInside⟩

/-- A preconnected set meeting the inside and the outside of the open polygon cone meets the
boundary. -/
theorem preconnected_meets_boundary {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (K : Set E3)
    (hK : IsPreconnected K) (hin : ∃ z ∈ K, Inside A z) (hout : ∃ z ∈ K, ¬ Inside A z) :
    ∃ z ∈ K, InClosed A z ∧ ¬ Inside A z := by
  set U := {y | Inside A y} with hUdef
  have hUopen : IsOpen U := by
    have h_eq : U = ⋂ i ∈ Finset.range m, {y | 0 < ⟪cross (A i) (A (i + 1)), y⟫} := by
      ext y; simp [hUdef, Tammes15.Geom.inside_iff hA y]
    rw [h_eq]
    refine isOpen_biInter_finset ?_
    intro i hi
    exact isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hinU : (K ∩ U).Nonempty := by
    rcases hin with ⟨z, hzK, hzU⟩
    exact ⟨z, hzK, hzU⟩
  have houtU : (K ∩ Uᶜ).Nonempty := by
    rcases hout with ⟨z, hzK, hzUc⟩
    exact ⟨z, hzK, hzUc⟩
  have h_frontier_nonempty : (K ∩ frontier U).Nonempty := by
    by_contra h_empty
    have h_empty' : K ∩ frontier U = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    have h_subset : K ⊆ U ∪ (closure U)ᶜ := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · by_cases hx_closure : x ∈ closure U
        · have hx_frontier : x ∈ frontier U := by
            rw [hUopen.frontier_eq]
            exact ⟨hx_closure, hxU⟩
          have hx_inter : x ∈ K ∩ frontier U := ⟨hx, hx_frontier⟩
          rw [h_empty'] at hx_inter
          simp at hx_inter
        · exact Or.inr hx_closure
    have h_empty_inter : U ∩ (closure U)ᶜ = ∅ := by
      ext x; constructor
      · intro hx
        rcases hx with ⟨hxU, hx_not_closure⟩
        exact hx_not_closure (subset_closure hxU)
      · intro hx; exfalso; simp at hx
    have h_closure_comp_nonempty : (K ∩ (closure U)ᶜ).Nonempty := by
      rcases houtU with ⟨z, hzK, hzUc⟩
      by_cases hz_frontier : z ∈ frontier U
      · have hz_inter : z ∈ K ∩ frontier U := ⟨hzK, hz_frontier⟩
        rw [h_empty'] at hz_inter
        simp at hz_inter
      · refine ⟨z, hzK, ?_⟩
        rw [Set.mem_compl_iff]
        intro hz_closure
        apply hz_frontier
        rw [hUopen.frontier_eq]
        exact ⟨hz_closure, hzUc⟩
    have h_contra := hK U ((closure U)ᶜ) hUopen isClosed_closure.isOpen_compl h_subset
      hinU h_closure_comp_nonempty
    rcases h_contra with ⟨z, hzK', hz_inter⟩
    have hz_inter' : z ∈ U ∩ (closure U)ᶜ := hz_inter
    rw [h_empty_inter] at hz_inter'
    simp at hz_inter'
  rcases h_frontier_nonempty with ⟨z, hzK, hz_frontier⟩
  have hz_not_U : z ∉ U := by
    intro hzU
    have : z ∈ U ∩ frontier U := ⟨hzU, hz_frontier⟩
    rw [hUopen.inter_frontier_eq] at this
    simp at this
  have hz_closure : z ∈ closure U := by
    rw [hUopen.frontier_eq] at hz_frontier
    exact hz_frontier.1
  have h_closed_contains_U : {y | Inside A y} ⊆ {y | InClosed A y} := by
    intro y hy
    have hy_inside : Inside A y := hy
    have hy_inclosed : InClosed A y := by
      rw [Tammes15.Geom.inClosed_iff hA]
      intro i hi
      rw [Tammes15.Geom.inside_iff hA] at hy_inside
      have hpos := hy_inside i hi
      exact le_of_lt hpos
    exact hy_inclosed
  have h_closed : IsClosed {y | InClosed A y} := by
    have h_eq : {y | InClosed A y} = ⋂ i ∈ (Finset.range m : Set ℕ), {y | 0 ≤ ⟪cross (A i) (A (i + 1)), y⟫} := by
      ext y; simp [Tammes15.Geom.inClosed_iff hA y]
    rw [h_eq]
    refine isClosed_biInter ?_
    intro i hi
    exact isClosed_le continuous_const (continuous_const.inner continuous_id)
  have hz_inClosed : InClosed A z := by
    have : z ∈ {y | InClosed A y} :=
      closure_minimal h_closed_contains_U h_closed hz_closure
    exact this
  exact ⟨z, hzK, hz_inClosed, hz_not_U⟩

/-! ## The polygon step of the cover -/

/-- The fan triangle algebra: `z = (X a + Y b + Z d) / ⟪cross a b, d⟫` with `Y, Z ≥ 0`; if `a` is
nearer to `z` than `b` and `d` is nearer to `b` than to `a`, then `X ≥ 0`. -/
theorem fan_coeff_nonneg (a b d z : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (ht : 0 < ⟪cross a b, d⟫) (hY : 0 ≤ ⟪cross d a, z⟫) (hZ : 0 ≤ ⟪cross a b, z⟫)
    (hmax : ⟪b, z⟫ ≤ ⟪a, z⟫) (hbd : ⟪a, d⟫ ≤ ⟪b, d⟫) : 0 ≤ ⟪cross b d, z⟫ := by
  set t := ⟪cross a b, d⟫ with ht_def
  set X := ⟪cross b d, z⟫ with hX_def
  set Y := ⟪cross d a, z⟫ with hY_def
  set Z := ⟪cross a b, z⟫ with hZ_def
  have ha_sq : ⟪a, a⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
  have hb_sq : ⟪b, b⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  have h_cramer := cramer_decomp a b d z
  -- h_cramer : ⟪cross a b, d⟫ • z = ⟪cross b d, z⟫ • a + ⟪cross d a, z⟫ • b + ⟪cross a b, z⟫ • d
  -- i.e., t • z = X • a + Y • b + Z • d
  have h_inner_eq : ⟪t • z, a - b⟫ = ⟪X • a + Y • b + Z • d, a - b⟫ := by
    rw [ht_def, hX_def, hY_def, hZ_def]
    exact congrArg (fun w => ⟪w, a - b⟫) h_cramer
  -- Expand both sides using inner product linearity
  have h_expanded : t * (⟪a, z⟫ - ⟪b, z⟫) = (X - Y) * (1 - ⟪a, b⟫) + Z * (⟪a, d⟫ - ⟪b, d⟫) := by
    calc
      t * (⟪a, z⟫ - ⟪b, z⟫) = t * ⟪a, z⟫ - t * ⟪b, z⟫ := by ring
      _ = t * ⟪z, a⟫ - t * ⟪z, b⟫ := by rw [real_inner_comm a z, real_inner_comm b z]
      _ = ⟪t • z, a⟫ - ⟪t • z, b⟫ := by
        simp [inner_smul_left]
      _ = ⟪t • z, a - b⟫ := by rw [inner_sub_right]
      _ = ⟪X • a + Y • b + Z • d, a - b⟫ := h_inner_eq
      _ = ⟪X • a + Y • b + Z • d, a⟫ - ⟪X • a + Y • b + Z • d, b⟫ := by rw [inner_sub_right]
      _ = (⟪X • a, a⟫ + ⟪Y • b, a⟫ + ⟪Z • d, a⟫) - (⟪X • a, b⟫ + ⟪Y • b, b⟫ + ⟪Z • d, b⟫) := by
        simp [inner_add_left]
      _ = (X * ⟪a, a⟫ + Y * ⟪b, a⟫ + Z * ⟪d, a⟫) - (X * ⟪a, b⟫ + Y * ⟪b, b⟫ + Z * ⟪d, b⟫) := by
        simp [inner_smul_left]
      _ = (X * 1 + Y * ⟪b, a⟫ + Z * ⟪d, a⟫) - (X * ⟪a, b⟫ + Y * 1 + Z * ⟪d, b⟫) := by rw [ha_sq, hb_sq]
      _ = (X - Y) * (1 - ⟪a, b⟫) + Z * (⟪a, d⟫ - ⟪b, d⟫) := by
        rw [real_inner_comm b a, real_inner_comm d a, real_inner_comm d b]
        ring
  -- h_expanded gives the key equation
  have h_one_sub_ab_pos : 0 < 1 - ⟪a, b⟫ := by
    have h_norm_sub_sq : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫ := by
      rw [norm_sub_sq_real, ha, hb]
      ring
    have h_norm_sub_pos : 0 < ‖a - b‖ ^ 2 := by
      have h_ne_zero : a - b ≠ 0 := sub_ne_zero.mpr hab
      have h_norm_pos : 0 < ‖a - b‖ := (norm_pos_iff.mpr h_ne_zero)
      exact pow_pos h_norm_pos 2
    rw [h_norm_sub_sq] at h_norm_sub_pos
    nlinarith
  have h_X_sub_Y_nonneg : 0 ≤ X - Y := by
    have h_eq2 : (X - Y) * (1 - ⟪a, b⟫) = t * (⟪a, z⟫ - ⟪b, z⟫) - Z * (⟪a, d⟫ - ⟪b, d⟫) := by
      linarith
    have h_rhs_nonneg : 0 ≤ t * (⟪a, z⟫ - ⟪b, z⟫) - Z * (⟪a, d⟫ - ⟪b, d⟫) := by
      have h1 : 0 ≤ t * (⟪a, z⟫ - ⟪b, z⟫) := by
        have h_diff_nonneg : 0 ≤ ⟪a, z⟫ - ⟪b, z⟫ := by linarith
        nlinarith
      have h2 : Z * (⟪a, d⟫ - ⟪b, d⟫) ≤ 0 := by
        have h_diff_d_nonpos : ⟪a, d⟫ - ⟪b, d⟫ ≤ 0 := by linarith
        nlinarith
      nlinarith
    rw [← h_eq2] at h_rhs_nonneg
    -- h_rhs_nonneg : 0 ≤ (X - Y) * (1 - ⟪a, b⟫)
    have : 0 * (1 - ⟪a, b⟫) ≤ (X - Y) * (1 - ⟪a, b⟫) := by
      simpa [zero_mul] using h_rhs_nonneg
    exact le_of_mul_le_mul_right this h_one_sub_ab_pos
  -- Then X ≥ Y ≥ 0, so X ≥ 0
  have hX_nonneg : 0 ≤ X := by
    linarith
  exact hX_nonneg

/-- The polygon step of the cover, for every face size: a point in the corner sector of a vertex
`A 0` that is nearest to it among the vertices lies in the closed polygon, when the sides are
contacts of inner product `c` and no vertex is nearer than `c` to `A 0`. -/
theorem fan_inClosed {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (c : ℝ)
    (hcont : ∀ i, ⟪A i, A (i + 1)⟫ = c) (hbound : ∀ j, A j ≠ A 0 → ⟪A 0, A j⟫ ≤ c) (z : E3)
    (hmax : ∀ j, ⟪A j, z⟫ ≤ ⟪A 0, z⟫) (hleft : 0 ≤ ⟪cross (A 0) (A 1), z⟫)
    (hright : 0 ≤ ⟪cross (A (m - 1)) (A 0), z⟫) : InClosed A z := by
  classical
  set f : ℕ → ℝ := fun k => ⟪cross (A 0) (A k), z⟫ with hf
  have hm3 : 3 ≤ m := hA.three
  have hf1 : 0 ≤ f 1 := hleft
  have hfm1 : f (m - 1) ≤ 0 := by
    show ⟪cross (A 0) (A (m - 1)), z⟫ ≤ 0
    rw [cross_swap (A (m - 1)) (A 0), inner_neg_left]
    linarith
  have hlast : f (m - 2 + 1) ≤ 0 := by rw [show m - 2 + 1 = m - 1 by omega]; exact hfm1
  have h_exists : ∃ k, 1 ≤ k ∧ f (k + 1) ≤ 0 := ⟨m - 2, by omega, hlast⟩
  have hj_spec := Nat.find_spec h_exists
  set j := Nat.find h_exists with hj
  have hj1 : 1 ≤ j := hj_spec.1
  have hj_f : ⟪cross (A 0) (A (j + 1)), z⟫ ≤ 0 := hj_spec.2
  have hj_le : j ≤ m - 2 := Nat.find_min' h_exists ⟨by omega, hlast⟩
  have hj_lt : j + 1 < m := by omega
  have hfj : 0 ≤ ⟪cross (A 0) (A j), z⟫ := by
    by_cases hj1' : j = 1
    · rw [hj1']; exact hf1
    · have hlt : j - 1 < j := by omega
      have hnot := Nat.find_min h_exists hlt
      rw [show j - 1 + 1 = j by omega] at hnot
      have hnot2 : ¬ f j ≤ 0 := fun h => hnot ⟨by omega, h⟩
      exact (lt_of_not_ge hnot2).le
  have hD : 0 < ⟪cross (A 0) (A j), A (j + 1)⟫ := by
    simpa using hA.triple_pos 0 j (j + 1) (by omega) (by omega) hj_lt
  have hsupp : 0 < ⟪cross (A j) (A (j + 1)), A 0⟫ := by
    apply hA.support_of_ne j 0
    · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : j < m)]; omega
    · rw [Nat.zero_mod, Nat.mod_eq_of_lt hj_lt]; omega
  have hz1 : ⟪cross (A j) (A (j + 1)), A j⟫ = 0 := by
    rw [triple_cycle]; exact inner_cross_right_zero _ _
  have hz2 : ⟪cross (A j) (A (j + 1)), A (j + 1)⟫ = 0 := inner_cross_right_zero _ _
  have h0j : A 0 ≠ A j := fun h => by rw [h, hz1] at hsupp; exact lt_irrefl 0 hsupp
  have h0j1 : A (j + 1) ≠ A 0 := fun h => by rw [← h, hz2] at hsupp; exact lt_irrefl 0 hsupp
  have hY : 0 ≤ ⟪cross (A (j + 1)) (A 0), z⟫ := by
    rw [cross_swap (A 0) (A (j + 1)), inner_neg_left]; linarith
  have hbd : ⟪A 0, A (j + 1)⟫ ≤ ⟪A j, A (j + 1)⟫ := by
    rw [hcont j]; exact hbound (j + 1) h0j1
  have hX := fan_coeff_nonneg (A 0) (A j) (A (j + 1)) z (hA.unit 0) (hA.unit j) h0j hD hY hfj
    (hmax j) hbd
  have hcr := cramer_decomp (A 0) (A j) (A (j + 1)) z
  have hD0 : ⟪cross (A 0) (A j), A (j + 1)⟫ ≠ 0 := hD.ne'
  have hzeq : z = (⟪cross (A j) (A (j + 1)), z⟫ / ⟪cross (A 0) (A j), A (j + 1)⟫) • A 0 +
      (⟪cross (A (j + 1)) (A 0), z⟫ / ⟪cross (A 0) (A j), A (j + 1)⟫) • A j +
      (⟪cross (A 0) (A j), z⟫ / ⟪cross (A 0) (A j), A (j + 1)⟫) • A (j + 1) := by
    calc z = (⟪cross (A 0) (A j), A (j + 1)⟫)⁻¹ • (⟪cross (A 0) (A j), A (j + 1)⟫ • z) := by
          rw [smul_smul, inv_mul_cancel₀ hD0, one_smul]
      _ = _ := by rw [hcr]; simp only [smul_add, smul_smul, div_eq_inv_mul]
  rw [hzeq]
  exact inClosed_of_cone hA 0 j (j + 1) _ _ _ (div_nonneg hX hD.le) (div_nonneg hY hD.le)
    (div_nonneg hfj hD.le)

end Tammes15.D2Regions
