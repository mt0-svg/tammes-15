import Tammes15.Local41.Defs

/-!
# Cross products, determinants and Rodrigues' rotations

Two statements of the proof of Theorem 4.1, each proved from smaller steps:
`cross_isometry` from `inner_cross_eq_det` and `det_rows_linearMap`;
`exists_rotation_curve` from Rodrigues' formula (`norm_rodrigues`, `exists_rodrigues_isometry`,
`hasDerivAt_rodrigues`). `inner_cross_self` and `inner_cross_perm` are used in `Chain`.
-/

open Real Matrix WithLp
open scoped RealInnerProductSpace

namespace Tammes15

/-- Rodrigues' formula: the rotation by `θ` about the unit axis `u`. -/
noncomputable def rodrigues (u : E3) (θ : ℝ) (v : E3) : E3 :=
  cos θ • v + sin θ • cross u v + ((1 - cos θ) * ⟪u, v⟫) • u

theorem inner_cross_self (a b : E3) : ⟪a, cross a b⟫ = 0 := by
  unfold cross
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp
  rw [dotProduct_comm, dot_self_cross]

theorem inner_cross_perm (a b c : E3) : ⟪a, cross b c⟫ = ⟪b, cross c a⟫ := by
  calc
    ⟪a, cross b c⟫
        = (cross b c).ofLp ⬝ᵥ star a.ofLp := by rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = (ofLp b ⨯₃ ofLp c) ⬝ᵥ star (ofLp a) := rfl
    _ = (ofLp b ⨯₃ ofLp c) ⬝ᵥ (ofLp a) := by simp
    _ = (ofLp a) ⬝ᵥ (ofLp b ⨯₃ ofLp c) := by rw [dotProduct_comm]
    _ = (ofLp b) ⬝ᵥ (ofLp c ⨯₃ ofLp a) := by rw [triple_product_permutation]
    _ = (ofLp c ⨯₃ ofLp a) ⬝ᵥ (ofLp b) := by rw [dotProduct_comm]
    _ = (cross c a).ofLp ⬝ᵥ star b.ofLp := rfl
    _ = ⟪b, cross c a⟫ := by rw [EuclideanSpace.inner_eq_star_dotProduct]

theorem cross_add_right (a b c : E3) : cross a (b + c) = cross a b + cross a c := by
  simp [cross, map_add]

theorem cross_smul_right (a b : E3) (r : ℝ) : cross a (r • b) = r • cross a b := by
  simp [cross, map_smul]

theorem cross_smul_left (a b : E3) (r : ℝ) : cross (r • a) b = r • cross a b := by
  simp [cross]

theorem inner_cross_right_self (a b : E3) : ⟪b, cross a b⟫ = 0 := by
  unfold cross
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm, dot_cross_self (ofLp a) (ofLp b)]

theorem norm_cross_sq (a b : E3) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have h1 : star ((cross a b).ofLp : Fin 3 → ℝ) = (cross a b).ofLp := by
    simpa using star_trivial ((cross a b).ofLp : Fin 3 → ℝ)
  rw [h1]
  unfold cross
  simp
  rw [cross_dot_cross]
  rw [dotProduct_comm (ofLp b) (ofLp a)]
  have hsq : (ofLp a ⬝ᵥ ofLp b) * (ofLp a ⬝ᵥ ofLp b) = (ofLp a ⬝ᵥ ofLp b) ^ 2 := by ring
  rw [hsq]
  have hdot_self_a : (ofLp a ⬝ᵥ ofLp a : ℝ) = ⟪a, a⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct a a]
    simp [star_trivial]
  have hdot_self_b : (ofLp b ⬝ᵥ ofLp b : ℝ) = ⟪b, b⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct b b]
    simp [star_trivial]
  have hdot_ab : (ofLp a ⬝ᵥ ofLp b : ℝ) = ⟪a, b⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct a b]
    simp [star_trivial, dotProduct_comm]
  rw [hdot_self_a, hdot_self_b, hdot_ab]
  rw [real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq b]

theorem inner_cross_eq_det (a b c : E3) :
    ⟪cross a b, c⟫ = Matrix.det ![ofLp a, ofLp b, ofLp c] := by
  calc
    ⟪cross a b, c⟫ = (ofLp c) ⬝ᵥ star (ofLp (cross a b)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = (ofLp c) ⬝ᵥ star (ofLp a ⨯₃ ofLp b) := by
      simp [cross]
    _ = (ofLp c) ⬝ᵥ (ofLp a ⨯₃ ofLp b) := by
      simp
    _ = (ofLp a) ⬝ᵥ (ofLp b ⨯₃ ofLp c) := by
      rw [triple_product_permutation]
    _ = Matrix.det ![ofLp a, ofLp b, ofLp c] := by
      rw [triple_product_eq_det]

theorem det_rows_linearMap (f : E3 →ₗ[ℝ] E3) (a b c : E3) :
    Matrix.det ![ofLp (f a), ofLp (f b), ofLp (f c)] =
      LinearMap.det f * Matrix.det ![ofLp a, ofLp b, ofLp c] := by
  let b' : Module.Basis (Fin 3) ℝ E3 := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let M := LinearMap.toMatrix b' b' f
  -- Lemma: ofLp (f x) i = (M *ᵥ (ofLp x)) i
  have h_entry (x : E3) (i : Fin 3) : ofLp (f x) i = (M *ᵥ (ofLp x)) i := by
    have h := LinearMap.toMatrix_mulVec_repr b' b' f x
    have h_repr (y : E3) (i : Fin 3) : (b'.repr y) i = ofLp y i := by
      simpa [b'] using PiLp.basisFun_repr (p := 2) (𝕜 := ℝ) (ι := Fin 3) y i
    have h_eq : (ofLp x) = ⇑(b'.repr x) := by
      ext i
      exact (h_repr x i).symm
    calc
      ofLp (f x) i = (⇑(b'.repr (f x))) i := by rw [h_repr]
      _ = ((LinearMap.toMatrix b' b') f *ᵥ ⇑(b'.repr x)) i := by rw [← h]
      _ = (M *ᵥ ⇑(b'.repr x)) i := rfl
      _ = (M *ᵥ (ofLp x)) i := by rw [h_eq]
  -- Expand both determinants using the explicit formula
  rw [Matrix.det_fin_three (R := ℝ) (A := ![ofLp (f a), ofLp (f b), ofLp (f c)])]
  rw [Matrix.det_fin_three (R := ℝ) (A := ![ofLp a, ofLp b, ofLp c])]
  simp
  -- Rewrite LinearMap.det f as M.det
  rw [← LinearMap.det_toMatrix b' f]
  -- Expand M.det using the same formula
  rw [Matrix.det_fin_three (R := ℝ) (A := M)]
  -- Now rewrite each (f x).ofLp i using h_entry
  simp [h_entry, Matrix.mulVec_apply, dotProduct, Fin.sum_univ_three]
  -- Now we have an equality of two big polynomial expressions
  ring

theorem norm_rodrigues (u : E3) (hu : ‖u‖ = 1) (θ : ℝ) (v : E3) :
    ‖rodrigues u θ v‖ = ‖v‖ := by
  set c := cos θ with hc
  set s := sin θ with hs
  set k := ⟪u, v⟫ with hk
  set w := cross u v with hw
  have hw_u : ⟪u, w⟫ = 0 := inner_cross_self u v
  have hw_v : ⟪v, w⟫ = 0 := inner_cross_right_self u v
  have hw_norm_sq : ‖w‖ ^ 2 = ‖v‖ ^ 2 - k ^ 2 := by
    calc
      ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := norm_cross_sq u v
      _ = 1 * ‖v‖ ^ 2 - k ^ 2 := by simp [hu, hk]
      _ = ‖v‖ ^ 2 - k ^ 2 := by ring
  have h_nonneg_left : 0 ≤ ‖rodrigues u θ v‖ := norm_nonneg _
  have h_nonneg_right : 0 ≤ ‖v‖ := norm_nonneg _
  apply (sq_eq_sq₀ h_nonneg_left h_nonneg_right).mp
  have h_norm_smul_sq (r : ℝ) (x : E3) : ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖r • x‖ ^ 2 = (|r| * ‖x‖) ^ 2 := by simp [norm_smul]
      _ = |r| ^ 2 * ‖x‖ ^ 2 := by ring
      _ = r ^ 2 * ‖x‖ ^ 2 := by simp [sq_abs]
  calc
    ‖rodrigues u θ v‖ ^ 2 = ‖c • v + s • w + ((1 - c) * k) • u‖ ^ 2 := by
      simp [rodrigues, hc, hs, hk, hw]
    _ = ‖c • v + s • w‖ ^ 2 + 2 * inner ℝ (c • v + s • w) (((1 - c) * k) • u) + ‖((1 - c) * k) • u‖ ^ 2 := by
      rw [norm_add_sq_real]
    _ = (‖c • v‖ ^ 2 + 2 * inner ℝ (c • v) (s • w) + ‖s • w‖ ^ 2) +
        2 * inner ℝ (c • v + s • w) (((1 - c) * k) • u) +
        ‖((1 - c) * k) • u‖ ^ 2 := by
      rw [norm_add_sq_real]
    _ = (c ^ 2 * ‖v‖ ^ 2 + 2 * (c * s * inner ℝ v w) + s ^ 2 * ‖w‖ ^ 2) +
        2 * (((1 - c) * k) * inner ℝ (c • v + s • w) u) +
        (((1 - c) * k) ^ 2 * ‖u‖ ^ 2) := by
      simp [h_norm_smul_sq, inner_smul_left, inner_smul_right, mul_left_comm, mul_assoc]
    _ = (c ^ 2 * ‖v‖ ^ 2 + 2 * (c * s * inner ℝ v w) + s ^ 2 * ‖w‖ ^ 2) +
        2 * (((1 - c) * k) * (c * inner ℝ v u + s * inner ℝ w u)) +
        (((1 - c) * k) ^ 2 * ‖u‖ ^ 2) := by
      simp [inner_add_left, inner_smul_left]
    _ = (c ^ 2 * ‖v‖ ^ 2 + 2 * (c * s * 0) + s ^ 2 * ‖w‖ ^ 2) +
        2 * (((1 - c) * k) * (c * k + s * 0)) +
        (((1 - c) * k) ^ 2 * 1) := by
      have hvw : inner ℝ v w = 0 := hw_v
      have hvu : inner ℝ v u = k := by rw [real_inner_comm u v, hk]
      have hwu : inner ℝ w u = 0 := by
        rw [← real_inner_comm w u]
        exact hw_u
      simp [hvw, hvu, hwu, hu]
    _ = (c ^ 2 * ‖v‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2) + 2 * ((1 - c) * k * (c * k)) + ((1 - c) * k) ^ 2 := by ring
    _ = (c ^ 2 * ‖v‖ ^ 2 + s ^ 2 * (‖v‖ ^ 2 - k ^ 2)) + 2 * c * (1 - c) * k ^ 2 + (1 - c) ^ 2 * k ^ 2 := by
      rw [hw_norm_sq]
      ring
    _ = ‖v‖ ^ 2 * (c ^ 2 + s ^ 2) + k ^ 2 * (-(s ^ 2) + 2 * c * (1 - c) + (1 - c) ^ 2) := by ring
    _ = ‖v‖ ^ 2 * (c ^ 2 + s ^ 2) + k ^ 2 * (1 - (c ^ 2 + s ^ 2)) := by ring
    _ = ‖v‖ ^ 2 * (cos θ ^ 2 + sin θ ^ 2) + k ^ 2 * (1 - (cos θ ^ 2 + sin θ ^ 2)) := by rw [hc, hs]
    _ = ‖v‖ ^ 2 * 1 + k ^ 2 * (1 - 1) := by
      rw [add_comm (cos θ ^ 2), Real.sin_sq_add_cos_sq θ]
    _ = ‖v‖ ^ 2 := by ring

theorem rodrigues_zero (u v : E3) : rodrigues u 0 v = v := by
  simp [rodrigues]

theorem exists_rodrigues_isometry (u : E3) (hu : ‖u‖ = 1) (θ : ℝ) :
    ∃ Q : E3 ≃ₗᵢ[ℝ] E3, ∀ v, Q v = rodrigues u θ v := by
  let L : E3 →ₗ[ℝ] E3 :=
    { toFun := rodrigues u θ
      map_add' := by
        intro v w
        dsimp [rodrigues]
        simp [cross_add_right, inner_add_right, smul_add, add_smul, mul_add]
        abel
      map_smul' := by
        intro r v
        dsimp [rodrigues]
        simp [cross_smul_right, inner_smul_right, smul_add, smul_smul, mul_comm, mul_left_comm]
    }
  have h_norm : ∀ v, ‖L v‖ = ‖v‖ := norm_rodrigues u hu θ
  let li : E3 →ₗᵢ[ℝ] E3 :=
    { L with
      norm_map' := h_norm
    }
  exact ⟨li.toLinearIsometryEquiv rfl, λ v => by simp [li, L]⟩

theorem hasDerivAt_rodrigues (u v : E3) (s : ℝ) :
    HasDerivAt (fun θ => rodrigues u (s * θ) v) (s • cross u v) 0 := by
  set w := cross u v
  set k := ⟪u, v⟫
  have h_rodrigues : (fun (θ : ℝ) => rodrigues u (s * θ) v) =
      (fun θ => cos (s * θ) • v + sin (s * θ) • w + ((1 - cos (s * θ)) * k) • u) := by
    ext θ; simp [rodrigues, w, k]
  rw [h_rodrigues]
  have h_inner : HasDerivAt (fun (θ : ℝ) => s * θ) s 0 := by
    simpa [mul_comm] using (hasDerivAt_id 0).const_mul s
  have h_cos_comp : HasDerivAt (fun θ => cos (s * θ)) 0 0 := by
    have := (HasDerivAt.cos h_inner)
    simpa [sin_zero, mul_zero] using this
  have h_sin_comp : HasDerivAt (fun θ => sin (s * θ)) s 0 := by
    have := (HasDerivAt.sin h_inner)
    simpa [cos_zero, one_mul] using this
  have h_one_sub_cos : HasDerivAt (fun θ => 1 - cos (s * θ)) 0 0 := by
    simpa using (HasDerivAt.const_sub 1 h_cos_comp)
  have h_term1 : HasDerivAt (fun θ => cos (s * θ) • v) ((0 : ℝ) • v) 0 :=
    HasDerivAt.smul_const h_cos_comp v
  have h_term2 : HasDerivAt (fun θ => sin (s * θ) • w) (s • w) 0 :=
    HasDerivAt.smul_const h_sin_comp w
  have h_term3 : HasDerivAt (fun θ => ((1 - cos (s * θ)) * k) • u) ((0 : ℝ) • u) 0 := by
    have h_mul : HasDerivAt (fun θ => (1 - cos (s * θ)) * k) ((0 : ℝ) * k) 0 :=
      HasDerivAt.mul_const h_one_sub_cos k
    simpa [zero_mul] using HasDerivAt.smul_const h_mul u
  have h_sum12 : HasDerivAt (fun θ => cos (s * θ) • v + sin (s * θ) • w) ((0 : ℝ) • v + s • w) 0 :=
    HasDerivAt.add h_term1 h_term2
  have h_sum : HasDerivAt (fun θ => (cos (s * θ) • v + sin (s * θ) • w) + ((1 - cos (s * θ)) * k) • u)
      (((0 : ℝ) • v + s • w) + ((0 : ℝ) • u)) 0 :=
    HasDerivAt.add h_sum12 h_term3
  simpa [w, add_assoc, zero_smul, add_zero] using h_sum

end Tammes15
