import Tammes15.Challenge.Glue.FramesAlg
import Tammes15.Challenge.Trigrows.Sphere

/-!
# Gluing: the frame of a child, the step bound and the path enclosure


A step of the tree is the matrix `R_z(φ) R_y(θ) Z` (Section 6.3). The child of a
frame `F` is `cos θ • F e₃ + sin θ • (cos φ • F e₁ + sin φ • F e₂)`, and the tangent direction from
the child back to the parent is `sin θ` times the first column of the child's frame (the reference
direction at the child is its parent). Along a path the product of steps moves `v` by at most the sum
of the angle differences (`frame_path_enclosure`, the bound `|Y(w) - Y_c(w)| ≤ ϱ(w)`).
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15

/-- The first basis vector `(1, 0, 0)`. -/
noncomputable def e1 : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The second basis vector `(0, 1, 0)`. -/
noncomputable def e2 : E3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)

/-- One step of the tree: `R_z(φ) R_y(θ) Z`. -/
noncomputable def stepM (φ θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := rotZ φ * rotY θ * flipZ

theorem toEuclideanLin_mul_apply (A B : Matrix (Fin 3) (Fin 3) ℝ) (v : E3) :
    toEuclideanLin (A * B) v = toEuclideanLin A (toEuclideanLin B v) := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

theorem toEuclideanLin_list_prod (l : List (Matrix (Fin 3) (Fin 3) ℝ)) (v : E3) :
    toEuclideanLin l.prod v =
      (l.map (fun M => (toEuclideanLin M : E3 →ₗ[ℝ] E3))).prod v := by
  induction' l with M l ih
  · simp
  · simp [List.prod_cons, List.map_cons, Module.End.mul_apply, ih]

theorem stepM_norm_apply (φ θ : ℝ) (v : E3) : ‖toEuclideanLin (stepM φ θ) v‖ = ‖v‖ := by
  unfold stepM
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, norm_rotZ_apply, norm_rotY_apply, norm_flipZ_apply]

theorem stepM_sub_apply_le (φ θ φ' θ' : ℝ) (v : E3) :
    ‖toEuclideanLin (stepM φ θ) v - toEuclideanLin (stepM φ' θ') v‖ ≤
      (|φ - φ'| + |θ - θ'|) * ‖v‖ := by
  set w := toEuclideanLin flipZ v with hw_def
  set a := toEuclideanLin (rotY θ) w with ha_def
  set a' := toEuclideanLin (rotY θ') w with ha'_def
  have hw_norm : ‖w‖ = ‖v‖ := by
    rw [hw_def]
    exact norm_flipZ_apply v
  have ha_norm : ‖a‖ = ‖v‖ := by
    rw [ha_def, hw_def]
    calc
      ‖toEuclideanLin (rotY θ) (toEuclideanLin flipZ v)‖ = ‖toEuclideanLin flipZ v‖ :=
        norm_rotY_apply θ _
      _ = ‖v‖ := norm_flipZ_apply v
  have ha'_norm : ‖a'‖ = ‖v‖ := by
    rw [ha'_def, hw_def]
    calc
      ‖toEuclideanLin (rotY θ') (toEuclideanLin flipZ v)‖ = ‖toEuclideanLin flipZ v‖ :=
        norm_rotY_apply θ' _
      _ = ‖v‖ := norm_flipZ_apply v
  have hL : toEuclideanLin (stepM φ θ) v = toEuclideanLin (rotZ φ) a := by
    calc
      toEuclideanLin (stepM φ θ) v = toEuclideanLin ((rotZ φ * rotY θ) * flipZ) v := rfl
      _ = toEuclideanLin (rotZ φ * rotY θ) (toEuclideanLin flipZ v) := by
        rw [toEuclideanLin_mul_apply]
      _ = toEuclideanLin (rotZ φ) (toEuclideanLin (rotY θ) (toEuclideanLin flipZ v)) := by
        rw [toEuclideanLin_mul_apply]
      _ = toEuclideanLin (rotZ φ) a := by rw [ha_def, hw_def]
  have hR : toEuclideanLin (stepM φ' θ') v = toEuclideanLin (rotZ φ') a' := by
    calc
      toEuclideanLin (stepM φ' θ') v = toEuclideanLin ((rotZ φ' * rotY θ') * flipZ) v := rfl
      _ = toEuclideanLin (rotZ φ' * rotY θ') (toEuclideanLin flipZ v) := by
        rw [toEuclideanLin_mul_apply]
      _ = toEuclideanLin (rotZ φ') (toEuclideanLin (rotY θ') (toEuclideanLin flipZ v)) := by
        rw [toEuclideanLin_mul_apply]
      _ = toEuclideanLin (rotZ φ') a' := by rw [ha'_def, hw_def]
  rw [hL, hR]
  calc
    ‖toEuclideanLin (rotZ φ) a - toEuclideanLin (rotZ φ') a'‖
        ≤ ‖toEuclideanLin (rotZ φ) a - toEuclideanLin (rotZ φ') a‖ +
          ‖toEuclideanLin (rotZ φ') a - toEuclideanLin (rotZ φ') a'‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |φ - φ'| * ‖a‖ + ‖toEuclideanLin (rotZ φ') a - toEuclideanLin (rotZ φ') a'‖ := by
      nlinarith [rotZ_sub_apply_le φ φ' a]
    _ = |φ - φ'| * ‖a‖ + ‖toEuclideanLin (rotZ φ') (a - a')‖ := by
      rw [map_sub (toEuclideanLin (rotZ φ')) a a']
    _ = |φ - φ'| * ‖a‖ + ‖a - a'‖ := by
      rw [norm_rotZ_apply φ' (a - a')]
    _ ≤ |φ - φ'| * ‖a‖ + |θ - θ'| * ‖w‖ := by
      nlinarith [rotY_sub_apply_le θ θ' w]
    _ = |φ - φ'| * ‖v‖ + |θ - θ'| * ‖v‖ := by rw [ha_norm, hw_norm]
    _ = (|φ - φ'| + |θ - θ'|) * ‖v‖ := by ring

theorem frame_path_enclosure (n : ℕ) (φ θ φ' θ' : Fin n → ℝ) (v : E3) :
    ‖toEuclideanLin (List.ofFn (fun i => stepM (φ i) (θ i))).prod v -
        toEuclideanLin (List.ofFn (fun i => stepM (φ' i) (θ' i))).prod v‖ ≤
      (∑ i, (|φ i - φ' i| + |θ i - θ' i|)) * ‖v‖ := by
  rw [toEuclideanLin_list_prod, toEuclideanLin_list_prod, List.map_ofFn, List.map_ofFn]
  refine prod_sub_apply_le n (fun i => toEuclideanLin (stepM (φ i) (θ i))) (fun i => toEuclideanLin (stepM (φ' i) (θ' i))) (fun i => |φ i - φ' i| + |θ i - θ' i|) ?hA ?hB ?hδ v
  · intro i w
    exact stepM_norm_apply (φ i) (θ i) w
  · intro i w
    exact stepM_norm_apply (φ' i) (θ' i) w
  · intro i w
    exact stepM_sub_apply_le (φ i) (θ i) (φ' i) (θ' i) w

theorem frame_child_eq (F : Matrix (Fin 3) (Fin 3) ℝ) (φ θ : ℝ) :
    toEuclideanLin (F * stepM φ θ) e3 = cos θ • toEuclideanLin F e3 +
      sin θ • (cos φ • toEuclideanLin F e1 + sin φ • toEuclideanLin F e2) := by
  rw [toEuclideanLin_mul_apply]
  have hstep : toEuclideanLin (stepM φ θ) e3 = cos θ • e3 + sin θ • (cos φ • e1 + sin φ • e2) := by
    ext i
    fin_cases i <;>
      simp [stepM, rotZ, rotY, flipZ, e1, e2, e3, Matrix.toLpLin_apply] <;>
      ring
  rw [hstep]
  simp [map_add, map_smul]

theorem frame_child_back (F : Matrix (Fin 3) (Fin 3) ℝ)
    (hF : F ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (φ θ : ℝ) :
    tdir (toEuclideanLin (F * stepM φ θ) e3) (toEuclideanLin F e3) =
      sin θ • toEuclideanLin (F * stepM φ θ) e1 := by
  have hF_transpose : Fᵀ * F = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hF
  have h_inner_preserve (a b : E3) : ⟪toEuclideanLin F a, toEuclideanLin F b⟫ = ⟪a, b⟫ := by
    calc
      ⟪toEuclideanLin F a, toEuclideanLin F b⟫
          = (toEuclideanLin F b).ofLp ⬝ᵥ star ((toEuclideanLin F a).ofLp) := by
            rw [EuclideanSpace.inner_eq_star_dotProduct]
      _ = (F *ᵥ b.ofLp) ⬝ᵥ star (F *ᵥ a.ofLp) := by
        simp only [toEuclideanLin, toLpLin_apply]
      _ = (F *ᵥ b.ofLp) ⬝ᵥ (F *ᵥ a.ofLp) := by simp
      _ = ((F *ᵥ b.ofLp) ᵥ* F) ⬝ᵥ a.ofLp := by rw [dotProduct_mulVec]
      _ = (b.ofLp ᵥ* (Fᵀ * F)) ⬝ᵥ a.ofLp := by rw [vecMul_mulVec]
      _ = (b.ofLp ᵥ* (1 : Matrix (Fin 3) (Fin 3) ℝ)) ⬝ᵥ a.ofLp := by rw [hF_transpose]
      _ = b.ofLp ⬝ᵥ (1 *ᵥ a.ofLp) := by rw [dotProduct_mulVec]
      _ = b.ofLp ⬝ᵥ a.ofLp := by simp
      _ = ⟪a, b⟫ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp
  set x := toEuclideanLin (stepM φ θ) e3 with hx
  have hw : toEuclideanLin (F * stepM φ θ) e3 = toEuclideanLin F x := by
    calc
      toEuclideanLin (F * stepM φ θ) e3 =
          (toEuclideanLin F ∘ₗ toEuclideanLin (stepM φ θ)) e3 := by
        rw [← toLpLin_mul_same (p := 2) (A := F) (B := stepM φ θ)]
      _ = toEuclideanLin F (toEuclideanLin (stepM φ θ) e3) := rfl
  have h_inner : ⟪toEuclideanLin F x, toEuclideanLin F e3⟫ = cos θ := by
    rw [h_inner_preserve x e3, hx]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [stepM, rotZ, rotY, flipZ, e3, toEuclideanLin, toLpLin_apply]
  have h_vec_eq : e3 - cos θ • x = sin θ • toEuclideanLin (stepM φ θ) e1 := by
    rw [hx]
    ext i
    fin_cases i
    · simp [stepM, rotZ, rotY, flipZ, e1, e3, toEuclideanLin, toLpLin_apply]; ring
    · simp [stepM, rotZ, rotY, flipZ, e1, e3, toEuclideanLin, toLpLin_apply]; ring
    · simp [stepM, rotZ, rotY, flipZ, e1, e3, toEuclideanLin, toLpLin_apply]
      ring_nf
      rw [Real.sin_sq]
  calc
    tdir (toEuclideanLin (F * stepM φ θ) e3) (toEuclideanLin F e3)
        = tdir (toEuclideanLin F x) (toEuclideanLin F e3) := by rw [hw]
    _ = (toEuclideanLin F e3) - ⟪toEuclideanLin F x, toEuclideanLin F e3⟫ • (toEuclideanLin F x) := rfl
    _ = (toEuclideanLin F e3) - cos θ • (toEuclideanLin F x) := by rw [h_inner]
    _ = toEuclideanLin F (e3 - cos θ • x) := by
      rw [map_sub, map_smul]
    _ = toEuclideanLin F (sin θ • toEuclideanLin (stepM φ θ) e1) := by rw [h_vec_eq]
    _ = sin θ • toEuclideanLin F (toEuclideanLin (stepM φ θ) e1) := by rw [map_smul]
    _ = sin θ • ((toEuclideanLin F ∘ₗ toEuclideanLin (stepM φ θ)) e1) := rfl
    _ = sin θ • toEuclideanLin (F * stepM φ θ) e1 := by
      rw [← toLpLin_mul_same (p := 2) (A := F) (B := stepM φ θ)]

end Tammes15
