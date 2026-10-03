import Tammes15.Draw.Angular

/-!
# Lemma A.2

If the corner after a dart at `v` is at least `π`, or `v` has a single neighbour, all neighbours
of `v` lie in a closed half-plane of the tangent plane (`exists_push_dir`); moving `v` a little
along the inner normal of that half-plane takes it farther than `d` from every other point
(`shift_config`, from the first variation step `shift_move`), and the contact graph loses the
edges at `v` (`contactCount_lt_of_shift`). The eight-point analogue is `pushing_vertex`,
`pushing_configuration` (PackingPush.lean, PackingReduction.lean of
github.com/lukasliehr/Energy-Minimization-8-Points at 50d14bc).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Lemma A.2, the half-plane step. -/
theorem exists_push_dir [DecidableRel G.Adj] (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hD : DistinctDirs G x) (R : RotSys G) (hR : IsAngular R x) (e : G.Dart)
    (he : π ≤ ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∨ R.rot e = e) :
    ∃ t : E3, ‖t‖ = 1 ∧ ⟪x e.fst, t⟫ = 0 ∧ ∀ w, G.Adj e.fst w → ⟪t, x w⟫ ≤ 0 := by
  set v := e.fst with hv_def
  have hv_norm : ‖x v‖ = 1 := hx v
  obtain ⟨e₀, he₀_norm, he₀_orth⟩ := exists_unit_orthogonal (x v)
  let ι : Type _ := {w // G.Adj v w}
  let z : ι → ℂ := λ w => tcoord (x v) e₀ (x w.1)
  have hz_ne_zero : ∀ i : ι, z i ≠ 0 := by
    intro i
    have htdir_ne_zero : tdir (x v) (x i.1) ≠ 0 := hD.1 v i.1 i.2
    have hnorm_eq : ‖tdir (x v) (x i.1)‖ = ‖tcoord (x v) e₀ (x i.1)‖ :=
      norm_tdir_eq_norm_tcoord (x v) e₀ (x i.1) hv_norm he₀_norm he₀_orth
    intro hzero
    apply htdir_ne_zero
    have hzero' : tcoord (x v) e₀ (x i.1) = 0 := by simpa [z] using hzero
    rw [← norm_eq_zero, hnorm_eq, hzero', norm_zero]
  set a₀ : ι := ⟨e.snd, e.adj⟩ with ha₀_def
  rcases he with (hθ | hrot_eq)
  · -- Case 1: π ≤ θ
    let θ := ocorner (x v) (x e.snd) (x (R.rot e).snd)
    have hθ_range : π ≤ θ ∧ θ ≤ 2 * π := by
      have hθ_le : θ ≤ 2 * π := by
        have hmem : θ ∈ Set.Ico (0 : ℝ) (2 * π) := by
          dsimp [θ, ocorner]
          simpa [zero_add] using toIcoMod_mem_Ico two_pi_pos 0 _
        exact (Set.mem_Ico.mp hmem).2.le
      exact ⟨hθ, hθ_le⟩
    have hgap : ∀ i : ι, i ≠ a₀ → θ ≤ toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a₀)) := by
      intro i hi_ne
      have hi_ne_snd : i.1 ≠ e.snd := by
        intro h_eq
        apply hi_ne
        ext; exact h_eq
      have hR_ineq : θ ≤ ocorner (x v) (x e.snd) (x i.1) := by
        have h := hR e (⟨(v, i.1), i.2⟩ : G.Dart) rfl (by
          intro h_eq
          apply hi_ne_snd
          simpa using congr_arg (·.snd) h_eq)
        simpa [θ, ocorner, hv_def] using h
      have h_eq : ocorner (x v) (x e.snd) (x i.1) =
          toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a₀)) := by
        rw [ocorner_eq_arg (x v) e₀ (x e.snd) (x i.1) hv_norm he₀_norm he₀_orth]
        have h1 : tcoord (x v) e₀ (x e.snd) = z a₀ := rfl
        have h2 : tcoord (x v) e₀ (x i.1) = z i := rfl
        rw [h1, h2]
        rw [toIcoMod_arg_conj_mul (z a₀) (z i) (hz_ne_zero a₀) (hz_ne_zero i)]
      calc
        θ ≤ ocorner (x v) (x e.snd) (x i.1) := hR_ineq
        _ = toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a₀)) := h_eq
    obtain ⟨u, hu_norm, hu_half⟩ := exists_halfplane_of_gap z hz_ne_zero a₀ θ hθ_range hgap
    let t := u.re • e₀ + u.im • cross (x v) e₀
    have h_tangent := tangent_of_complex (x v) e₀ hv_norm he₀_norm he₀_orth u
    refine ⟨t, ?_, ?_, ?_⟩
    · dsimp [t]
      exact h_tangent.1.trans hu_norm
    · dsimp [t]
      exact h_tangent.2.1
    · intro w hw
      dsimp [t]
      rw [h_tangent.2.2 (x w)]
      have hz_w : z ⟨w, hw⟩ = tcoord (x v) e₀ (x w) := rfl
      rw [← hz_w]
      exact hu_half ⟨w, hw⟩
  · -- Case 2: R.rot e = e
    let θ := π
    have hθ_range : π ≤ θ ∧ θ ≤ 2 * π := by
      dsimp [θ]
      have hπ_pos : 0 < π := Real.pi_pos
      exact ⟨le_refl π, by linarith⟩
    have hgap : ∀ i : ι, i ≠ a₀ → θ ≤ toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a₀)) := by
      intro i hi_ne
      have hi_eq_e_snd : i.1 = e.snd := by
        have h_dart_eq : (⟨(v, i.1), i.2⟩ : G.Dart) = e :=
          eq_of_rot_eq_self R e (⟨(v, i.1), i.2⟩ : G.Dart) rfl hrot_eq
        simpa using congr_arg (·.snd) h_dart_eq
      exfalso
      exact hi_ne (by ext; exact hi_eq_e_snd)
    obtain ⟨u, hu_norm, hu_half⟩ := exists_halfplane_of_gap z hz_ne_zero a₀ θ hθ_range hgap
    let t := u.re • e₀ + u.im • cross (x v) e₀
    have h_tangent := tangent_of_complex (x v) e₀ hv_norm he₀_norm he₀_orth u
    refine ⟨t, ?_, ?_, ?_⟩
    · dsimp [t]
      exact h_tangent.1.trans hu_norm
    · dsimp [t]
      exact h_tangent.2.1
    · intro w hw
      dsimp [t]
      rw [h_tangent.2.2 (x w)]
      have hz_w : z ⟨w, hw⟩ = tcoord (x v) e₀ (x w) := rfl
      rw [← hz_w]
      exact hu_half ⟨w, hw⟩

/-- Lemma A.2: `v` moves to a point farther than `d` from every other point. -/
theorem shift_config {N : ℕ} {d : ℝ} (hd : 0 < d ∧ d < π / 2) (X : Config N d) (i : Fin N)
    (t : E3) (ht : ‖t‖ = 1) (hit : ⟪X.pt i, t⟫ = 0)
    (hpush : ∀ j, j ≠ i → sdist (X.pt i) (X.pt j) = d → ⟪t, X.pt j⟫ ≤ 0) :
    ∃ X' : Config N d, (∀ j, j ≠ i → X'.pt j = X.pt j) ∧
      ∀ j, j ≠ i → d < sdist (X'.pt i) (X'.pt j) := by
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hd_nonneg : 0 ≤ d := by linarith
  have hd_le_pi : d ≤ π := by
    have hpi_pos : 0 < π := Real.pi_pos
    linarith
  have hcos_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  have hX_unit : ∀ j, ‖X.pt j‖ = 1 := X.unit
  have h_sep : ∀ j k, j ≠ k → d ≤ sdist (X.pt j) (X.pt k) := X.sep
  -- Index type for j ≠ i
  let ι := {j : Fin N // j ≠ i}
  let w : ι → E3 := fun j => X.pt j.val
  have hw : ∀ j : ι, ⟪X.pt i, w j⟫ < cos d ∨ (⟪X.pt i, w j⟫ = cos d ∧ ⟪t, w j⟫ < 0) ∨
      (⟪X.pt i, w j⟫ = cos d ∧ ⟪t, w j⟫ = 0 ∧ 0 < cos d) := by
    intro j
    have hji : j.val ≠ i := j.property
    have hsep := h_sep i j.val (Ne.symm hji)
    have hX_unit_i : ‖X.pt i‖ = 1 := hX_unit i
    have hX_unit_j : ‖X.pt j.val‖ = 1 := hX_unit j.val
    by_cases hlt : d < sdist (X.pt i) (X.pt j.val)
    · left
      have hcos_sdist_eq : cos (sdist (X.pt i) (X.pt j.val)) = ⟪X.pt i, X.pt j.val⟫ :=
        cos_sdist (X.pt i) (X.pt j.val) hX_unit_i hX_unit_j
      have hsdist_mem := sdist_mem_Icc (X.pt i) (X.pt j.val)
      have hcos_lt : cos (sdist (X.pt i) (X.pt j.val)) < cos d :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hd_nonneg hsdist_mem.2 hlt
      rw [hcos_sdist_eq] at hcos_lt
      exact hcos_lt
    · have heq : sdist (X.pt i) (X.pt j.val) = d := by linarith
      have hcos_sdist_eq : cos (sdist (X.pt i) (X.pt j.val)) = ⟪X.pt i, X.pt j.val⟫ :=
        cos_sdist (X.pt i) (X.pt j.val) hX_unit_i hX_unit_j
      have h_inner_eq_cos : ⟪X.pt i, X.pt j.val⟫ = cos d := by
        rw [← hcos_sdist_eq, heq]
      have h_t_le : ⟪t, X.pt j.val⟫ ≤ 0 := hpush j.val hji heq
      by_cases h_t_lt : ⟪t, X.pt j.val⟫ < 0
      · right; left; exact ⟨h_inner_eq_cos, h_t_lt⟩
      · right; right
        have h_t_eq : ⟪t, X.pt j.val⟫ = 0 := by linarith
        exact ⟨h_inner_eq_cos, h_t_eq, hcos_pos⟩
  obtain ⟨s, hs_pos, hs_lt_one, hs_inner⟩ :=
    shift_move d (X.pt i) t w hw 1 (by norm_num)
  let v' : E3 := cos s • X.pt i + sin s • t
  have hv'_unit : ‖v'‖ = 1 := norm_cos_sin_unit (X.pt i) t (hX_unit i) ht hit s
  have h_inner_lt : ∀ j : ι, ⟪v', w j⟫ < cos d := hs_inner
  -- Helper lemma: inner product bound from Cauchy-Schwarz for unit vectors
  have h_inner_ge_neg_one : ∀ (a b : E3), ‖a‖ = 1 → ‖b‖ = 1 → -1 ≤ ⟪a, b⟫ := by
    intro a b ha hb
    have h_abs := abs_real_inner_le_norm a b
    rw [ha, hb, mul_one] at h_abs
    exact neg_le_of_abs_le h_abs
  -- Rename outer i to avoid clash with structure field binder
  set i' : Fin N := i with hi'
  let h_pt : Fin N → E3 := Function.update X.pt i' v'
  have h_unit : ∀ j, ‖h_pt j‖ = 1 := by
    intro j
    dsimp [h_pt]
    by_cases hji : j = i'
    · rw [hji]; simpa [Function.update_self] using hv'_unit
    · simp [Function.update_of_ne hji, hX_unit j]
  have h_sep_proof : ∀ (a b : Fin N), a ≠ b → d ≤ sdist (h_pt a) (h_pt b) := by
    intro a b hne
    dsimp [h_pt]
    by_cases hia : a = i'
    · subst hia
      have hib : b ≠ i' := by intro h; apply hne; rw [h]
      have h_eq_a : (Function.update X.pt i' v') i' = v' := by simp
      have h_eq_b : (Function.update X.pt i' v') b = X.pt b := by simp [hib]
      rw [h_eq_a, h_eq_b]
      have h_inner_lt_b := h_inner_lt ⟨b, hi' ▸ hib⟩
      have hcos_sdist_eq : cos (sdist v' (X.pt b)) = ⟪v', X.pt b⟫ :=
        cos_sdist v' (X.pt b) hv'_unit (hX_unit b)
      have h_arccos_lt : Real.arccos (cos d) < Real.arccos ⟪v', X.pt b⟫ := by
        apply Real.arccos_lt_arccos
        · exact h_inner_ge_neg_one v' (X.pt b) hv'_unit (hX_unit b)
        · exact h_inner_lt_b
        · exact Real.cos_le_one d
      have h_sdist_eq_d : Real.arccos (cos d) = d :=
        Real.arccos_cos hd_nonneg hd_le_pi
      rw [h_sdist_eq_d] at h_arccos_lt
      have h_sdist_eq_arccos : sdist v' (X.pt b) = Real.arccos ⟪v', X.pt b⟫ := rfl
      rw [h_sdist_eq_arccos]
      linarith
    · by_cases hib : b = i'
      · subst hib
        have h_eq_b : (Function.update X.pt i' v') i' = v' := by simp
        have h_eq_a : (Function.update X.pt i' v') a = X.pt a := by simp [hia]
        rw [h_eq_a, h_eq_b]
        have h_inner_lt_a := h_inner_lt ⟨a, hi' ▸ hia⟩
        have hcos_sdist_eq : cos (sdist (X.pt a) v') = ⟪X.pt a, v'⟫ :=
          cos_sdist (X.pt a) v' (hX_unit a) hv'_unit
        have h_arccos_lt : Real.arccos (cos d) < Real.arccos ⟪X.pt a, v'⟫ := by
          apply Real.arccos_lt_arccos
          · exact h_inner_ge_neg_one (X.pt a) v' (hX_unit a) hv'_unit
          · rw [real_inner_comm]
            exact h_inner_lt_a
          · exact Real.cos_le_one d
        have h_sdist_eq_d : Real.arccos (cos d) = d :=
          Real.arccos_cos hd_nonneg hd_le_pi
        rw [h_sdist_eq_d] at h_arccos_lt
        have h_sdist_eq_arccos : sdist (X.pt a) v' = Real.arccos ⟪X.pt a, v'⟫ := rfl
        rw [h_sdist_eq_arccos]
        linarith
      · have h_eq_a : (Function.update X.pt i' v') a = X.pt a := by simp [hia]
        have h_eq_b : (Function.update X.pt i' v') b = X.pt b := by simp [hib]
        rw [h_eq_a, h_eq_b]
        exact X.sep a b hne
  let X' : Config N d := {
    pt := h_pt
    unit := h_unit
    sep := h_sep_proof
  }
  refine ⟨X', ?_, ?_⟩
  · intro j hj_ne
    have hj_ne' : j ≠ i' := by rwa [hi']
    dsimp [X', h_pt]
    simp [Function.update_of_ne (f := X.pt) hj_ne']
  · intro j hj_ne
    have hj_ne' : j ≠ i' := by rwa [hi']
    dsimp [X', h_pt]
    simp [Function.update_self, Function.update_of_ne (f := X.pt) hj_ne']
    have h_inner_lt_j := h_inner_lt ⟨j, hj_ne'⟩
    have hcos_sdist_eq : cos (sdist v' (X.pt j)) = ⟪v', X.pt j⟫ :=
      cos_sdist v' (X.pt j) hv'_unit (hX_unit j)
    have h_arccos_lt : Real.arccos (cos d) < Real.arccos ⟪v', X.pt j⟫ := by
      apply Real.arccos_lt_arccos
      · exact h_inner_ge_neg_one v' (X.pt j) hv'_unit (hX_unit j)
      · exact h_inner_lt_j
      · exact Real.cos_le_one d
    have h_sdist_eq_d : Real.arccos (cos d) = d :=
      Real.arccos_cos hd_nonneg hd_le_pi
    rw [h_sdist_eq_d] at h_arccos_lt
    have h_sdist_eq_arccos : sdist v' (X.pt j) = Real.arccos ⟪v', X.pt j⟫ := rfl
    rw [h_sdist_eq_arccos]
    linarith

/-- The shifted configuration has fewer contacts. -/
theorem contactCount_lt_of_shift {N : ℕ} {d : ℝ} (X X' : Config N d) (i : Fin N)
    (hsame : ∀ j, j ≠ i → X'.pt j = X.pt j) (hfar : ∀ j, j ≠ i → d < sdist (X'.pt i) (X'.pt j))
    (hcon : ∃ j, (contactGraph X).Adj i j) : contactCount X' < contactCount X := by
  dsimp [contactCount]
  have h_fin : ((contactGraph X).edgeSet : Set (Sym2 (Fin N))).Finite := by
    have : Finite (Sym2 (Fin N)) := inferInstance
    exact Set.toFinite _
  refine Set.ncard_lt_ncard ?_ h_fin
  rw [SimpleGraph.edgeSet_ssubset_edgeSet]
  rcases hcon with ⟨j, hj⟩
  rcases (contactGraph_adj_iff X i j).mp hj with ⟨hne_ij, hdist_ij⟩
  have h_not_adj' : ¬ (contactGraph X').Adj i j := by
    rw [contactGraph_adj_iff X']
    push Not
    intro hne
    have h_contra := hfar j hne.symm
    linarith
  constructor
  · intro a b h_adj
    rcases (contactGraph_adj_iff X' a b).mp h_adj with ⟨hne_ab, hdist_ab⟩
    have ha_ne_i : a ≠ i := by
      intro h_eq
      have hbi : b ≠ i := by
        intro h_eq2
        apply hne_ab
        rw [h_eq, h_eq2]
      have h_contra := hfar b hbi
      rw [h_eq] at hdist_ab
      rw [hdist_ab] at h_contra
      linarith
    have hb_ne_i : b ≠ i := by
      intro h_eq
      have hai : a ≠ i := by
        intro h_eq2
        apply hne_ab
        rw [h_eq2, h_eq]
      have h_contra := hfar a hai
      rw [h_eq] at hdist_ab
      rw [← sdist_comm (X'.pt a) (X'.pt i), hdist_ab] at h_contra
      linarith
    have hpt_a : X'.pt a = X.pt a := hsame a ha_ne_i
    have hpt_b : X'.pt b = X.pt b := hsame b hb_ne_i
    rw [hpt_a, hpt_b] at hdist_ab
    exact (contactGraph_adj_iff X a b).mpr ⟨hne_ab, hdist_ab⟩
  · intro h_eq
    have h_adj' : (contactGraph X').Adj i j := h_eq i j hj
    exact h_not_adj' h_adj'

end Tammes15
