import Tammes15.Glue.Frames

/-!
# Gluing: the algebra of the frames, the child point, Local

`rotZ`, `rotY`, `flipZ` are in `SO(3)` and compose as rotations; the child
point `F R_z(φ) R_y(d) Z e₃` of a frame `F` is at inner product `cos d` from `F e₃`;
`local_core` is the triangle inequality behind the Local discard.
-/

open Real Matrix
open scoped RealInnerProductSpace

namespace Tammes15

/-- The third basis vector `(0, 0, 1)`. -/
noncomputable def e3 : E3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

theorem rotZ_mul_rotZ (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rotY_mul_rotY (a b : ℝ) : rotY a * rotY b = rotY (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

theorem flipZ_mul_flipZ : flipZ * flipZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [flipZ, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_rotZ (φ : ℝ) : (rotZ φ).det = 1 := by
  simp [rotZ, Matrix.det_fin_three]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem det_rotY (θ : ℝ) : (rotY θ).det = 1 := by
  simp [rotY, Matrix.det_fin_three]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem det_flipZ : flipZ.det = 1 := by
  simp [flipZ, Matrix.det_fin_three]

theorem rotZ_mem_SO (φ : ℝ) : rotZ φ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
      nlinarith [Real.cos_sq_add_sin_sq φ]
  · rw [Matrix.det_fin_three]
    simp [rotZ]
    nlinarith [Real.cos_sq_add_sin_sq φ]

theorem rotY_mem_SO (θ : ℝ) : rotY θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotY, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
      <;> ring_nf
      <;> simp [Real.cos_sq_add_sin_sq]
  · rw [Matrix.det_fin_three]
    simp [rotY]
    ring_nf
    simp [Real.cos_sq_add_sin_sq]

theorem flipZ_mem_SO : flipZ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flipZ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  · exact det_flipZ

theorem frame_point_norm (F : Matrix (Fin 3) (Fin 3) ℝ) (hF : F ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ‖toEuclideanLin F e3‖ = 1 := by
  have hF' : Fᵀ * F = 1 := by
    simpa using (Matrix.mem_orthogonalGroup_iff' (n := Fin 3) (R := ℝ)).mp hF
  have h_inner : ⟪toEuclideanLin F e3, toEuclideanLin F e3⟫ = ⟪e3, e3⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp
    calc
      F *ᵥ e3.ofLp ⬝ᵥ F *ᵥ e3.ofLp = (F *ᵥ e3.ofLp) ᵥ* F ⬝ᵥ e3.ofLp := by
        rw [Matrix.dotProduct_mulVec]
      _ = e3.ofLp ᵥ* (Fᵀ * F) ⬝ᵥ e3.ofLp := by
        rw [Matrix.vecMul_mulVec]
      _ = e3.ofLp ᵥ* (1 : Matrix (Fin 3) (Fin 3) ℝ) ⬝ᵥ e3.ofLp := by rw [hF']
      _ = e3.ofLp ⬝ᵥ e3.ofLp := by simp
  have h_norm_e3 : ‖e3‖ = 1 := by
    simp [e3]
  have h_norm_sq : ‖toEuclideanLin F e3‖ ^ 2 = 1 := by
    calc
      ‖toEuclideanLin F e3‖ ^ 2 = RCLike.re ⟪toEuclideanLin F e3, toEuclideanLin F e3⟫ := by
        rw [inner_self_eq_norm_sq]
      _ = RCLike.re ⟪e3, e3⟫ := by rw [h_inner]
      _ = ‖e3‖ ^ 2 := by rw [inner_self_eq_norm_sq]
      _ = 1 ^ 2 := by rw [h_norm_e3]
      _ = 1 := by norm_num
  have h_nonneg : 0 ≤ ‖toEuclideanLin F e3‖ := norm_nonneg _
  nlinarith

theorem frame_child_inner (F : Matrix (Fin 3) (Fin 3) ℝ)
    (hF : F ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (φ d : ℝ) :
    ⟪toEuclideanLin F e3, toEuclideanLin (F * rotZ φ * rotY d * flipZ) e3⟫ = cos d := by
  have hF' : Fᵀ * F = 1 := ((Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hF)
  -- Helper lemma: toEuclideanLin A e3 = WithLp.toLp 2 (Aᵀ 2)
  have h_toEuclideanLin_e3 (A : Matrix (Fin 3) (Fin 3) ℝ) : toEuclideanLin A e3 = WithLp.toLp 2 (Aᵀ 2) := by
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    ext i
    simp [e3, PiLp.single_apply, Matrix.mulVec, dotProduct]
  rw [h_toEuclideanLin_e3 F, h_toEuclideanLin_e3 (F * rotZ φ * rotY d * flipZ)]
  -- Now goal: inner ℝ (WithLp.toLp 2 (Fᵀ 2)) (WithLp.toLp 2 ((F * rotZ φ * rotY d * flipZ)ᵀ 2)) = cos d
  rw [inner_matrix_col_col F (F * rotZ φ * rotY d * flipZ) 2 2]
  -- Goal: (Fᴴ * (F * rotZ φ * rotY d * flipZ)) 2 2 = cos d
  -- For real matrices, Fᴴ = Fᵀ
  have h_conj : (Fᴴ : Matrix (Fin 3) (Fin 3) ℝ) = Fᵀ := by simp
  rw [h_conj]
  -- Now: (Fᵀ * (F * rotZ φ * rotY d * flipZ)) 2 2 = cos d
  -- Using associativity and hF': Fᵀ * (F * M) = (Fᵀ * F) * M = 1 * M = M
  calc
    (Fᵀ * (F * rotZ φ * rotY d * flipZ)) 2 2 = ((Fᵀ * F) * rotZ φ * rotY d * flipZ) 2 2 := by
      simp [Matrix.mul_assoc]
    _ = ((1 : Matrix (Fin 3) (Fin 3) ℝ) * rotZ φ * rotY d * flipZ) 2 2 := by rw [hF']
    _ = (rotZ φ * rotY d * flipZ) 2 2 := by simp
    _ = cos d := by
      simp [rotZ, rotY, flipZ, Matrix.mul_apply, Fin.sum_univ_three]

/-- The Local discard: a point within `ϱ v` of the centre, whose centre is within
`ε - ϱ v` of the target, is within `ε` of the target. -/
theorem local_core {ι : Type*} (Y Yc T : ι → E3) (ϱ : ι → ℝ) (ε : ℝ)
    (h₁ : ∀ v, ‖Y v - Yc v‖ ≤ ϱ v) (h₂ : ∀ v, ‖Yc v - T v‖ + ϱ v ≤ ε) :
    ∀ v, ‖Y v - T v‖ ≤ ε := by
  intro v
  have htri := norm_sub_le_norm_sub_add_norm_sub (Y v) (Yc v) (T v)
  linarith [h₁ v, h₂ v]

end Tammes15
