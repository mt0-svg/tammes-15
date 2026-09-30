import Tammes15.Draw.FaceWalk
import Tammes15.Draw.Angular

/-!
# Reconstruction by the valid tree (Section 5.4)

The interface `glue_congruent` of `Tammes15.Hyps.Interfaces`, stated word for word as
`glue_congruent_proof` (the unused hypotheses are named `_hP`, `_hd`); the interface file closes the interface
with it.

For a vertex `v` of a realisation, `rframe g x v` is the matrix with columns `c`, `cross (x v) c`,
`x v`, where `c` is the unit tangent at `x v` towards the far end of the reference dart `refD v`;
it lies in `SO(3)`. By induction on the depth, the frame of the gluing is
`frame v = (rframe root)ᵀ * rframe v` (`frame_eq`): at a child `w` of `u`,
`rframe w = rframe u * stepM φ d` (`rframe_child`), since both lie in `SO(3)` and agree on `e₁`
(`frame_child_back`) and on `e₃` (`frame_child_eq` and the polar form `polar_form` of `x w` in the
frame of `u`), where the turn `φ` agrees with the oriented corner from the reference dart to the
tree dart modulo `2π` (`turn_cos_sin`). The free points follow from the same polar form at the
corner of their hexagon (`glueY_inr`), and the isometry is `(rframe root)ᵀ`.
-/

open Real InnerProductGeometry Matrix
open scoped RealInnerProductSpace

namespace Tammes15

namespace Reconstruct

/-! ## Frames and rotations -/

/-- The matrix with columns `c`, `cross v c`, `v`. -/
noncomputable def rmat (v c : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (![c, cross v c, v] j) i

theorem rmat_apply_e1 (v c : E3) : toEuclideanLin (rmat v c) e1 = c := by
  ext i; fin_cases i <;> simp [rmat, e1, e2, e3, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rmat_apply_e2 (v c : E3) : toEuclideanLin (rmat v c) e2 = cross v c := by
  ext i
  fin_cases i <;> simp [rmat, e2, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem rmat_apply_e3 (v c : E3) : toEuclideanLin (rmat v c) e3 = v := by
  ext i; fin_cases i <;> simp [rmat, e3, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- A unit `v` and a unit `c` orthogonal to it give a rotation. -/
theorem rmat_mem_SO (v c : E3) (hv : ‖v‖ = 1) (hc : ‖c‖ = 1) (hvc : ⟪v, c⟫ = 0) :
    rmat v c ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hv2 : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1 := by
    have h : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h
    linarith
  have hc2 : c 0 * c 0 + c 1 * c 1 + c 2 * c 2 = 1 := by
    have h : ⟪c, c⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hc, one_pow]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h
    linarith
  have hvc2 : v 0 * c 0 + v 1 * c 1 + v 2 * c 2 = 0 := by
    have h := hvc
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h
    linarith
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rmat, cross, cross_apply, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.star_eq_conjTranspose] <;>
      first
        | ring1
        | linear_combination hc2
        | linear_combination hv2
        | linear_combination hvc2
        | linear_combination (c 0 * c 0 + c 1 * c 1 + c 2 * c 2) * hv2 + hc2 -
            (v 0 * c 0 + v 1 * c 1 + v 2 * c 2) * hvc2
  · simp [rmat, cross, cross_apply, Matrix.det_fin_three]
    linear_combination (c 0 * c 0 + c 1 * c 1 + c 2 * c 2) * hv2 + hc2 -
      (v 0 * c 0 + v 1 * c 1 + v 2 * c 2) * hvc2

/-- An orthogonal matrix preserves the inner product. -/
theorem inner_toEuclideanLin (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (a b : E3) :
    ⟪toEuclideanLin M a, toEuclideanLin M b⟫ = ⟪a, b⟫ := by
  have hM_orth : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  calc
    ⟪toEuclideanLin M a, toEuclideanLin M b⟫ =
      (toEuclideanLin M b).ofLp ⬝ᵥ star ((toEuclideanLin M a).ofLp) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = (M *ᵥ b.ofLp) ⬝ᵥ star (M *ᵥ a.ofLp) := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    _ = (M *ᵥ b.ofLp) ⬝ᵥ (M *ᵥ a.ofLp) := by simp
    _ = Matrix.vecMul (M *ᵥ b.ofLp) M ⬝ᵥ a.ofLp := by
      rw [Matrix.dotProduct_mulVec]
    _ = Matrix.vecMul (b.ofLp) (Mᵀ * M) ⬝ᵥ a.ofLp := by
      rw [Matrix.vecMul_mulVec]
    _ = Matrix.vecMul (b.ofLp) 1 ⬝ᵥ a.ofLp := by rw [hM_orth]
    _ = b.ofLp ⬝ᵥ a.ofLp := by simp
    _ = ⟪a, b⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp

/-- The linear isometry of an orthogonal matrix. -/
theorem exists_isometry (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ∃ O : E3 ≃ₗᵢ[ℝ] E3, ∀ a, O a = toEuclideanLin M a := by
  have h_inner : ∀ a b : E3, ⟪toEuclideanLin M a, toEuclideanLin M b⟫ = ⟪a, b⟫ := by
    intro a b
    exact Tammes15.Reconstruct.inner_toEuclideanLin M hM a b
  let li : E3 →ₗᵢ[ℝ] E3 := (toEuclideanLin M).isometryOfInner h_inner
  refine ⟨li.toLinearIsometryEquiv (by rfl), ?_⟩
  intro a
  simp [li]

/-- Two rotations with the same images of `e₁` and `e₃` are equal. -/
theorem SO3_ext (M N : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hN : N ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h1 : toEuclideanLin M e1 = toEuclideanLin N e1)
    (h3 : toEuclideanLin M e3 = toEuclideanLin N e3) : M = N := by
  have col : ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (j i : Fin 3),
      (toEuclideanLin A (EuclideanSpace.single j 1)) i = A i j := by
    intro A j i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨hMo, hMd⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hM
  obtain ⟨hNo, hNd⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hN
  have hMo' : Mᵀ * M = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hMo
    simpa [Matrix.star_eq_conjTranspose] using this
  have hNo' : Nᵀ * N = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hNo
    simpa [Matrix.star_eq_conjTranspose] using this
  have hNo'' : N * Nᵀ = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hNo
    simpa [Matrix.star_eq_conjTranspose] using this
  have c0 : ∀ i, M i 0 = N i 0 := by
    intro i
    have := congrArg (fun v : E3 => v i) h1
    simpa [e1, col] using this
  have c2 : ∀ i, M i 2 = N i 2 := by
    intro i
    have := congrArg (fun v : E3 => v i) h3
    simpa [e3, col] using this
  set Q := Nᵀ * M with hQ
  have hQo : Qᵀ * Q = 1 := by
    rw [hQ, transpose_mul, transpose_transpose,
      show Mᵀ * N * (Nᵀ * M) = Mᵀ * (N * Nᵀ) * M by simp only [Matrix.mul_assoc], hNo'',
      Matrix.mul_one, hMo']
  have hQd : Q.det = 1 := by rw [hQ, det_mul, det_transpose, hNd, hMd, one_mul]
  have q0 : ∀ i, Q i 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0 := by
    intro i
    rw [← hNo', hQ, mul_apply, mul_apply]
    simp only [transpose_apply, c0]
  have q2 : ∀ i, Q i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := by
    intro i
    rw [← hNo', hQ, mul_apply, mul_apply]
    simp only [transpose_apply, c2]
  have e00 : Q 0 0 = 1 := by simpa using q0 0
  have e10 : Q 1 0 = 0 := by simpa using q0 1
  have e20 : Q 2 0 = 0 := by simpa using q0 2
  have e02 : Q 0 2 = 0 := by simpa using q2 0
  have e12 : Q 1 2 = 0 := by simpa using q2 1
  have e22 : Q 2 2 = 1 := by simpa using q2 2
  have o01 : Q 0 0 * Q 0 1 + Q 1 0 * Q 1 1 + Q 2 0 * Q 2 1 = 0 := by
    have := congrFun (congrFun hQo 0) 1
    simpa [mul_apply, Fin.sum_univ_three] using this
  have o21 : Q 0 2 * Q 0 1 + Q 1 2 * Q 1 1 + Q 2 2 * Q 2 1 = 0 := by
    have := congrFun (congrFun hQo 2) 1
    simpa [mul_apply, Fin.sum_univ_three] using this
  have hd := hQd
  rw [det_fin_three] at hd
  rw [e00, e10, e20] at o01
  rw [e02, e12, e22] at o21
  rw [e00, e10, e20, e02, e12, e22] at hd
  have e01 : Q 0 1 = 0 := by linarith
  have e21 : Q 2 1 = 0 := by linarith
  have e11 : Q 1 1 = 1 := by rw [e01, e21] at hd; linarith
  have hQ1 : Q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e01, e02, e10, e11, e12, e20, e21, e22]
  calc M = N * Nᵀ * M := by rw [hNo'', Matrix.one_mul]
    _ = N * Q := by rw [hQ, Matrix.mul_assoc]
    _ = N := by rw [hQ1, Matrix.mul_one]

/-- The point of `rotZ φ * rotY r` in a frame `F` (`flipZ` fixes `e₃`, so this is
`frame_child_eq`). -/
theorem rotZY_apply_e3 (F : Matrix (Fin 3) (Fin 3) ℝ) (φ r : ℝ) :
    toEuclideanLin (F * rotZ φ * rotY r) e3 = cos r • toEuclideanLin F e3 +
      sin r • (cos φ • toEuclideanLin F e1 + sin φ • toEuclideanLin F e2) := by
  ext i
  simp [rotZ, rotY, e1, e2, e3, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.mul_apply, Pi.single_apply]
  ring

/-- `rotZ` depends on the angle through its cosine and sine. -/
theorem rotZ_congr (φ ψ : ℝ) (hc : cos φ = cos ψ) (hs : sin φ = sin ψ) : rotZ φ = rotZ ψ := by
  unfold rotZ
  rw [hc, hs]

theorem stepM_congr (φ ψ θ : ℝ) (hc : cos φ = cos ψ) (hs : sin φ = sin ψ) :
    stepM φ θ = stepM ψ θ := by
  unfold stepM
  rw [rotZ_congr φ ψ hc hs]

/-! ## Oriented corners modulo `2π` -/

/-- The unit vector of `tdir v a`. -/
noncomputable def udir (v a : E3) : E3 := ‖tdir v a‖⁻¹ • tdir v a

theorem udir_norm (v a : E3) (ha : tdir v a ≠ 0) : ‖udir v a‖ = 1 := by
  dsimp [udir]
  have hnorm : ‖tdir v a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnonneg : 0 ≤ ‖tdir v a‖ := norm_nonneg _
  calc
    ‖‖tdir v a‖⁻¹ • tdir v a‖ = ‖(‖tdir v a‖⁻¹ : ℝ)‖ * ‖tdir v a‖ := by rw [norm_smul]
    _ = ‖‖tdir v a‖‖⁻¹ * ‖tdir v a‖ := by rw [norm_inv]
    _ = ‖tdir v a‖⁻¹ * ‖tdir v a‖ := by rw [Real.norm_of_nonneg hnonneg]
    _ = 1 := by rw [inv_mul_cancel₀ hnorm]

theorem inner_udir (v a : E3) (hv : ‖v‖ = 1) : ⟪v, udir v a⟫ = 0 := by
  dsimp [udir, tdir]
  rw [inner_smul_right]
  have h : ⟪v, a - ⟪v, a⟫ • v⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  rw [h, mul_zero]

/-- The polar form of a unit `y` about a unit `v`, in the frame of the unit tangent towards `a`. -/
theorem polar_form (v a y : E3) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1) (ha : tdir v a ≠ 0) :
    y = cos (sdist v y) • v + sin (sdist v y) •
      (cos (ocorner v a y) • udir v a + sin (ocorner v a y) • cross v (udir v a)) := by
  have he : ‖udir v a‖ = 1 := udir_norm v a ha
  have hve : ⟪v, udir v a⟫ = 0 := inner_udir v a hv
  have hn : 0 < ‖tdir v a‖ := norm_pos_iff.mpr ha
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have h1 : ⟪a, tdir v a⟫ = ‖tdir v a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold tdir
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hvv,
      real_inner_comm a v]
    ring
  have hae : ⟪a, udir v a⟫ = ‖tdir v a‖ := by
    unfold udir
    rw [real_inner_smul_right, h1]
    field_simp
  have hace : ⟪a, cross v (udir v a)⟫ = 0 := by
    unfold udir tdir
    generalize ‖a - ⟪v, a⟫ • v‖⁻¹ = k
    generalize ⟪v, a⟫ = c
    simp [cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  have hs : tcoord v (udir v a) a = (‖tdir v a‖ : ℂ) := by
    apply Complex.ext <;> simp [tcoord, hae, hace]
  set t := tcoord v (udir v a) y with ht_def
  have hψ : ocorner v a y = toIcoMod two_pi_pos 0 (Complex.arg t) := by
    rw [ocorner_eq_arg v (udir v a) a y hv he hve, hs, Complex.conj_ofReal,
      Complex.arg_real_mul t hn]
  have hcos : cos (ocorner v a y) = cos (Complex.arg t) := by
    rw [hψ, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, Real.cos_sub_int_mul_two_pi]
  have hsin : sin (ocorner v a y) = sin (Complex.arg t) := by
    rw [hψ, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, Real.sin_sub_int_mul_two_pi]
  have hnt : ‖t‖ = sin (sdist v y) := by
    rw [ht_def, ← norm_tdir_eq_norm_tcoord v (udir v a) y hv he hve, tdir_norm v y hv hy]
  have hre : sin (sdist v y) * cos (ocorner v a y) = ⟪y, udir v a⟫ := by
    rw [hcos, ← hnt, Complex.norm_mul_cos_arg, ht_def]
    rfl
  have him : sin (sdist v y) * sin (ocorner v a y) = ⟪y, cross v (udir v a)⟫ := by
    rw [hsin, ← hnt, Complex.norm_mul_sin_arg, ht_def]
    rfl
  have hcr : cos (sdist v y) = ⟪y, v⟫ := by rw [cos_sdist v y hv hy, real_inner_comm]
  rw [smul_add, smul_smul, smul_smul, hre, him, hcr, ← add_assoc]
  exact frame_expand v (udir v a) y hv he hve

/-- Oriented corners add modulo `2π`. -/
theorem cos_sin_ocorner_add (v a b c : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0) (hb : tdir v b ≠ 0)
    (hc : tdir v c ≠ 0) :
    cos (ocorner v a b + ocorner v b c) = cos (ocorner v a c) ∧
      sin (ocorner v a b + ocorner v b c) = sin (ocorner v a c) := by
  rcases Tammes15.exists_unit_orthogonal v with ⟨e, he_norm, he_inner⟩
  have h_ab := Tammes15.ocorner_eq_fangle_sub v e a b hv he_norm he_inner ha hb
  have h_bc := Tammes15.ocorner_eq_fangle_sub v e b c hv he_norm he_inner hb hc
  have h_ac := Tammes15.ocorner_eq_fangle_sub v e a c hv he_norm he_inner ha hc
  rw [h_ab, h_bc, h_ac]
  set fa := Tammes15.fangle v e a
  set fb := Tammes15.fangle v e b
  set fc := Tammes15.fangle v e c
  set n1 := toIcoDiv Real.two_pi_pos 0 (fb - fa)
  set n2 := toIcoDiv Real.two_pi_pos 0 (fc - fb)
  set n3 := toIcoDiv Real.two_pi_pos 0 (fc - fa)
  have h1 : toIcoMod Real.two_pi_pos 0 (fb - fa) = (fb - fa) - n1 • (2 * π) := rfl
  have h2 : toIcoMod Real.two_pi_pos 0 (fc - fb) = (fc - fb) - n2 • (2 * π) := rfl
  have h3 : toIcoMod Real.two_pi_pos 0 (fc - fa) = (fc - fa) - n3 • (2 * π) := rfl
  rw [h1, h2, h3]
  have harg : (fb - fa) - n1 • (2 * π) + ((fc - fb) - n2 • (2 * π)) = (fc - fa) - (n1 + n2) • (2 * π) := by
    ring
  rw [harg]
  have hcos1 : cos ((fc - fa) - (n1 + n2) • (2 * π)) = cos (fc - fa) := by
    simpa [zsmul_eq_mul] using Real.cos_sub_int_mul_two_pi (fc - fa) (n1 + n2)
  have hcos2 : cos ((fc - fa) - n3 • (2 * π)) = cos (fc - fa) := by
    simpa [zsmul_eq_mul] using Real.cos_sub_int_mul_two_pi (fc - fa) n3
  have hsin1 : sin ((fc - fa) - (n1 + n2) • (2 * π)) = sin (fc - fa) := by
    simpa [zsmul_eq_mul] using Real.sin_sub_int_mul_two_pi (fc - fa) (n1 + n2)
  have hsin2 : sin ((fc - fa) - n3 • (2 * π)) = sin (fc - fa) := by
    simpa [zsmul_eq_mul] using Real.sin_sub_int_mul_two_pi (fc - fa) n3
  exact And.intro (by rw [hcos1, hcos2]) (by rw [hsin1, hsin2])

/-- The telescoped form along a sequence of directions. -/
theorem cos_sin_sum_ocorner (v : E3) (p : ℕ → E3) (hv : ‖v‖ = 1) (hp : ∀ t, tdir v (p t) ≠ 0)
    (s : ℕ) :
    cos (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) = cos (ocorner v (p 0) (p s)) ∧
      sin (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) = sin (ocorner v (p 0) (p s)) := by
  induction s with
  | zero =>
      constructor
      · simp [Tammes15.ocorner_self v (p 0)]
      · simp [Tammes15.ocorner_self v (p 0)]
  | succ s ih =>
      rw [Finset.sum_range_succ]
      rcases ih with ⟨hcos, hsin⟩
      have h_add := Tammes15.Reconstruct.cos_sin_ocorner_add v (p 0) (p s) (p (s + 1)) hv (hp 0) (hp s) (hp (s + 1))
      rcases h_add with ⟨hcos_add, hsin_add⟩
      have hcos' : cos ((∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) + ocorner v (p s) (p (s + 1))) = cos (ocorner v (p 0) (p (s + 1))) := by
        calc
          cos ((∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) + ocorner v (p s) (p (s + 1)))
              = cos (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) * cos (ocorner v (p s) (p (s + 1))) - sin (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) * sin (ocorner v (p s) (p (s + 1))) := by rw [Real.cos_add]
          _ = cos (ocorner v (p 0) (p s)) * cos (ocorner v (p s) (p (s + 1))) - sin (ocorner v (p 0) (p s)) * sin (ocorner v (p s) (p (s + 1))) := by rw [hcos, hsin]
          _ = cos (ocorner v (p 0) (p s) + ocorner v (p s) (p (s + 1))) := by rw [Real.cos_add]
          _ = cos (ocorner v (p 0) (p (s + 1))) := by rw [hcos_add]
      have hsin' : sin ((∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) + ocorner v (p s) (p (s + 1))) = sin (ocorner v (p 0) (p (s + 1))) := by
        calc
          sin ((∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) + ocorner v (p s) (p (s + 1)))
              = sin (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) * cos (ocorner v (p s) (p (s + 1))) + cos (∑ t ∈ Finset.range s, ocorner v (p t) (p (t + 1))) * sin (ocorner v (p s) (p (s + 1))) := by rw [Real.sin_add]
          _ = sin (ocorner v (p 0) (p s)) * cos (ocorner v (p s) (p (s + 1))) + cos (ocorner v (p 0) (p s)) * sin (ocorner v (p s) (p (s + 1))) := by rw [hcos, hsin]
          _ = sin (ocorner v (p 0) (p s) + ocorner v (p s) (p (s + 1))) := by rw [Real.sin_add]
          _ = sin (ocorner v (p 0) (p (s + 1))) := by rw [hsin_add]
      constructor
      · exact hcos'
      · exact hsin'

/-- The number of rotation steps between two darts at a vertex reaches the second one. -/
theorem rot_pow_turnSteps {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (R : RotSys G) (a b : G.Dart) (h : a.fst = b.fst) :
    (R.rot ^ turnSteps R a b) a = b := by
  have hcycle : R.rot.SameCycle a b := R.rot_cycle a b h
  have h_exists : ∃ s, (R.rot ^ s) a = b :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq hcycle
  have h_turn : turnSteps R a b = Nat.find h_exists := by
    unfold turnSteps
    rw [dite_eq_left h_exists]
  rw [h_turn]
  exact Nat.find_spec h_exists

/-! ## The frames of a realisation -/

open scoped Classical

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

/-- The frame of a realisation at `v`, from the reference dart of the gluing. -/
noncomputable def rframe (g : GlueData P k) (x : Pts P k → E3) (v : Fin P.n) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  rmat (x (.inl v)) (udir (x (.inl v)) (x (.inl (g.refD v).snd)))

theorem tdir_adj_ne_zero (hx : Realisation P H d x) (f : P.G.Dart) :
    tdir (x (.inl f.fst)) (x (.inl f.snd)) ≠ 0 := by
  set v := x (.inl f.fst) with hv
  set w := x (.inl f.snd) with hw
  have hv_norm : ‖v‖ = 1 := hx.unit (.inl f.fst)
  have hw_norm : ‖w‖ = 1 := hx.unit (.inl f.snd)
  have h_sdist : sdist v w = d := hx.edge f.fst f.snd f.adj
  have hd_pos : 0 < d := hx.d_mem.1
  have hd_lt_pi_div_two : d < π / 2 := hx.d_mem.2
  have h_inner_mem : ⟪v, w⟫ ∈ Set.Icc (-1 : ℝ) 1 :=
    real_inner_mem_Icc_of_norm_eq_one hv_norm hw_norm
  have h_cos_sdist_eq_inner : cos (sdist v w) = ⟪v, w⟫ := by
    rw [sdist]
    rw [Real.cos_arccos h_inner_mem.1 h_inner_mem.2]
  have h_inner_eq_cos_d : ⟪v, w⟫ = cos d := by
    rw [← h_cos_sdist_eq_inner, h_sdist]
  have h_cos_d_pos : 0 < cos d := by
    have hmem : d ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> linarith
    exact Real.cos_pos_of_mem_Ioo hmem
  have h_cos_d_lt_one : cos d < 1 := by
    have h_low : -(2 * π) < d := by linarith
    have h_high : d < 2 * π := by linarith
    have h_ne_zero : d ≠ 0 := by linarith
    have h_eq_one_iff := (Real.cos_eq_one_iff_of_lt_of_lt h_low h_high).mp
    by_contra! hge
    have h_eq_one : cos d = 1 := by linarith [Real.cos_le_one d, hge]
    have h_d_zero : d = 0 := h_eq_one_iff h_eq_one
    exact h_ne_zero h_d_zero
  by_contra! h_tdir_zero
  have h_w_eq : w = ⟪v, w⟫ • v := by
    have hzero : tdir v w = 0 := h_tdir_zero
    dsimp [tdir] at hzero
    exact sub_eq_zero.mp hzero
  have h_norm_eq : ‖⟪v, w⟫ • v‖ = |⟪v, w⟫| * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_norm_w : ‖w‖ = |⟪v, w⟫| * ‖v‖ := by
    have h1 : ‖w‖ = ‖⟪v, w⟫ • v‖ := congrArg norm h_w_eq
    have h2 : ‖⟪v, w⟫ • v‖ = |⟪v, w⟫| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    rw [h1, h2]
  rw [hw_norm, hv_norm, mul_one] at h_norm_w
  have h_abs_eq_one : |⟪v, w⟫| = 1 := by
    linarith
  have h_inner_pos : 0 < ⟪v, w⟫ := by
    rw [h_inner_eq_cos_d]
    exact h_cos_d_pos
  have h_abs_eq : |⟪v, w⟫| = ⟪v, w⟫ := abs_of_pos h_inner_pos
  rw [h_abs_eq] at h_abs_eq_one
  rw [h_inner_eq_cos_d] at h_abs_eq_one
  linarith

theorem refD_fst (g : GlueData P k) (hg : g.Valid) (v : Fin P.n) : (g.refD v).fst = v := by
  unfold GlueData.refD
  split_ifs with h
  · -- h : v = g.root
    rw [h]
    exact hg.root_fst
  · -- h : v ≠ g.root
    have hsymm : (g.par v).symm.fst = (g.par v).snd := by
      simp [SimpleGraph.Dart.symm]
    rw [hsymm, hg.par_snd v h]

theorem rframe_mem_SO (hx : Realisation P H d x) (g : GlueData P k) (hg : g.Valid) (v : Fin P.n) :
    rframe g x v ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  unfold rframe
  have hv_unit : ‖x (.inl v)‖ = 1 := hx.unit (.inl v)
  have h_refD_fst : (g.refD v).fst = v := refD_fst g hg v
  have h_tdir_ne_zero : tdir (x (.inl v)) (x (.inl (g.refD v).snd)) ≠ 0 := by
    simpa [h_refD_fst] using tdir_adj_ne_zero hx (g.refD v)
  have h_udir_norm : ‖udir (x (.inl v)) (x (.inl (g.refD v).snd))‖ = 1 :=
    udir_norm (x (.inl v)) (x (.inl (g.refD v).snd)) h_tdir_ne_zero
  have h_inner : ⟪x (.inl v), udir (x (.inl v)) (x (.inl (g.refD v).snd))⟫ = 0 :=
    inner_udir (x (.inl v)) (x (.inl (g.refD v).snd)) hv_unit
  exact rmat_mem_SO (x (.inl v)) (udir (x (.inl v)) (x (.inl (g.refD v).snd))) hv_unit h_udir_norm h_inner

/-- The turn of `assignOf` between two darts at a vertex is their oriented corner modulo `2π`. -/
theorem turn_cos_sin (hx : Realisation P H d x) (a b : P.G.Dart) (h : a.fst = b.fst) :
    cos ((assignOf P H d x).turn a b) =
        cos (ocorner (x (.inl a.fst)) (x (.inl a.snd)) (x (.inl b.snd))) ∧
      sin ((assignOf P H d x).turn a b) =
        sin (ocorner (x (.inl a.fst)) (x (.inl a.snd)) (x (.inl b.snd))) := by
  have hs := rot_pow_turnSteps P.R a b h
  have hsum : (assignOf P H d x).turn a b = ∑ t ∈ Finset.range (turnSteps P.R a b),
      ocorner (x (.inl a.fst)) (x (.inl ((P.R.rot ^ t) a).snd))
        (x (.inl ((P.R.rot ^ (t + 1)) a).snd)) := by
    unfold Assign.turn
    apply Finset.sum_congr rfl
    intro t _
    show ocorner (x (.inl ((P.R.rot ^ t) a).fst)) (x (.inl ((P.R.rot ^ t) a).snd))
      (x (.inl (P.R.rot ((P.R.rot ^ t) a)).snd)) = _
    rw [rot_pow_fst P.R a t, pow_succ', Equiv.Perm.mul_apply]
  rw [hsum]
  have hp := cos_sin_sum_ocorner (x (.inl a.fst)) (fun t => x (.inl ((P.R.rot ^ t) a).snd))
    (hx.unit _) (fun t => by
      have h' := tdir_adj_ne_zero hx ((P.R.rot ^ t) a)
      rwa [rot_pow_fst] at h') (turnSteps P.R a b)
  simp only [pow_zero, Equiv.Perm.one_apply, hs] at hp
  exact hp

/-- The step of the tree in the frames of the realisation. -/
theorem rframe_child (hx : Realisation P H d x) (g : GlueData P k) (hg : g.Valid) (w : Fin P.n)
    (hw : w ≠ g.root) :
    rframe g x w = rframe g x (g.par w).fst *
      stepM ((assignOf P H d x).turn (g.refD (g.par w).fst) (g.par w)) d := by
  have hfw : (g.par w).snd = w := hg.par_snd w hw
  have hru : (g.refD (g.par w).fst).fst = (g.par w).fst := refD_fst g hg _
  have hMu := rframe_mem_SO hx g hg (g.par w).fst
  obtain ⟨hc, hs⟩ := turn_cos_sin hx (g.refD (g.par w).fst) (g.par w) hru
  rw [hru, hfw] at hc hs
  rw [stepM_congr _ _ d hc hs]
  set ψ := ocorner (x (.inl (g.par w).fst)) (x (.inl (g.refD (g.par w).fst).snd)) (x (.inl w))
  have hsd : sdist (x (.inl (g.par w).fst)) (x (.inl w)) = d := by
    have h' := hx.edge _ _ (g.par w).adj
    rwa [hfw] at h'
  have hta : tdir (x (.inl (g.par w).fst)) (x (.inl (g.refD (g.par w).fst).snd)) ≠ 0 := by
    have h' := tdir_adj_ne_zero hx (g.refD (g.par w).fst)
    rwa [hru] at h'
  have hstep : stepM ψ d ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    unfold stepM
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (rotZ_mem_SO ψ) (rotY_mem_SO d)) flipZ_mem_SO
  have he3 : toEuclideanLin (rframe g x (g.par w).fst * stepM ψ d) e3 = x (.inl w) := by
    have hp := polar_form (x (.inl (g.par w).fst)) (x (.inl (g.refD (g.par w).fst).snd))
      (x (.inl w)) (hx.unit _) (hx.unit _) hta
    rw [hsd] at hp
    rw [frame_child_eq]
    simp only [rframe, rmat_apply_e1, rmat_apply_e2, rmat_apply_e3]
    exact hp.symm
  apply SO3_ext _ _ (rframe_mem_SO hx g hg w) (Submonoid.mul_mem _ hMu hstep)
  · have hb := frame_child_back (rframe g x (g.par w).fst)
      (Matrix.mem_specialOrthogonalGroup_iff.mp hMu).1 ψ d
    rw [he3, show toEuclideanLin (rframe g x (g.par w).fst) e3 = x (.inl (g.par w).fst) from
      rmat_apply_e3 _ _] at hb
    have hn : ‖tdir (x (.inl w)) (x (.inl (g.par w).fst))‖ = sin d := by
      rw [tdir_norm _ _ (hx.unit _) (hx.unit _), sdist_comm, hsd]
    have hsin : sin d ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi hx.d_mem.1 (by linarith [hx.d_mem.2, pi_pos])).ne'
    have hrw : (g.refD w).snd = (g.par w).fst := by
      simp [GlueData.refD, hw]
    rw [show toEuclideanLin (rframe g x w) e1 = udir (x (.inl w)) (x (.inl (g.refD w).snd)) from
      rmat_apply_e1 _ _, hrw, udir, hn, hb, smul_smul, inv_mul_cancel₀ hsin, one_smul]
  · rw [show toEuclideanLin (rframe g x w) e3 = x (.inl w) from rmat_apply_e3 _ _, he3]

/-- The frames of the gluing are those of the realisation seen from the root. -/
theorem frame_eq (hx : Realisation P H d x) (g : GlueData P k) (hg : g.Valid) (v : Fin P.n) :
    g.frame (assignOf P H d x) v = (rframe g x g.root)ᵀ * rframe g x v := by
  have hroot : (rframe g x g.root)ᵀ * rframe g x g.root = 1 := by
    have h := (Matrix.mem_specialOrthogonalGroup_iff.mp (rframe_mem_SO hx g hg g.root)).1
    rw [Matrix.mem_orthogonalGroup_iff'] at h
    simpa [Matrix.star_eq_conjTranspose] using h
  have hAd : (assignOf P H d x).d = d := rfl
  suffices h : ∀ n v, g.depth v = n →
      g.frameN (assignOf P H d x) n v = (rframe g x g.root)ᵀ * rframe g x v from h _ v rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    have hvr : v = g.root := by
      by_contra h
      have := hg.par_depth v h
      omega
    subst hvr
    rw [hroot]
    rfl
  | succ n ih =>
    intro v hv
    by_cases h : v = g.root
    · subst h
      rw [hg.depth_root] at hv
      omega
    · rw [GlueData.frameN]
      simp only [h, ↓reduceIte]
      rw [ih _ (by have := hg.par_depth v h; omega), hAd, mul_assoc, ← rframe_child hx g hg v h]

/-- The free points of the gluing. -/
theorem glueY_inr (hx : Realisation P H d x) (g : GlueData P k) (hg : g.Valid)
    (m : Fin k) :
    glueY H (assignOf P H d x) g (.inr m) = toEuclideanLin (rframe g x g.root)ᵀ (x (.inr m)) := by
  rw [glueY]
  have hP6 : fsize P (H.base m) = 6 := H.hex m
  set c : Fin 6 := g.freeCorner m with hc_def
  set f := (P.R.face ^ (c : ℕ)) (H.base m) with hf_def
  set y := x (.inr m) with hy_def
  have hfa : (g.refD f.fst).fst = f.fst := refD_fst g hg _
  have hta : tdir (x (.inl f.fst)) (x (.inl (g.refD f.fst).snd)) ≠ 0 := by
    have h' := tdir_adj_ne_zero hx (g.refD f.fst)
    rwa [hfa] at h'
  have htf : tdir (x (.inl f.fst)) (x (.inl f.snd)) ≠ 0 := tdir_adj_ne_zero hx f
  have hin : 0 < ⟪cross (x (.inl f.fst)) (x (.inl f.snd)), y⟫ := hx.inside m c
  have hsy : 0 < sdist (x (.inl f.fst)) y ∧ sdist (x (.inl f.fst)) y < π := by
    have hz : ⟪cross (x (.inl f.fst)) (x (.inl f.snd)), x (.inl f.fst)⟫ = 0 := by
      rw [real_inner_comm]
      exact inner_cross_self _ _
    refine FaceWalk.sdist_mem_Ioo _ _ (hx.unit _) (hx.unit _) ?_ ?_
    · intro h
      rw [← h, hz] at hin
      exact lt_irrefl _ hin
    · intro h
      have h' : y = -x (.inl f.fst) := by rw [h, neg_neg]
      rw [h', inner_neg_right, hz, neg_zero] at hin
      exact lt_irrefl _ hin
  have hty : tdir (x (.inl f.fst)) y ≠ 0 := by
    intro h
    have hn := tdir_norm _ _ (hx.unit (.inl f.fst)) (hx.unit (.inr m))
    rw [← hy_def, h, norm_zero] at hn
    exact (sin_pos_of_pos_of_lt_pi hsy.1 hsy.2).ne hn
  have hsf : sdist (x (.inl f.fst)) (x (.inl f.snd)) = d := hx.edge _ _ f.adj
  have hidx : ((c + 1 : Fin 6) : ℕ) = ((c : ℕ) + 1) % fsize P (H.base m) := by
    rw [hP6, Fin.val_add]
    simp
  have hr1 : (assignOf P H d x).r m (c + 1) = sdist y (x (.inl f.snd)) := by
    show sdist y (x (.inl (FaceWalk.fv P (H.base m) ((c + 1 : Fin 6) : ℕ)))) = _
    rw [hidx, ← FaceWalk.fv_mod, hf_def, FaceWalk.face_pow_snd]
  have hr0 : (assignOf P H d x).r m c = sdist y (x (.inl f.fst)) := rfl
  have hAd : (assignOf P H d x).d = d := rfl
  have hγ : gam ((assignOf P H d x).r m (c + 1)) ((assignOf P H d x).r m c) (assignOf P H d x).d =
      ocorner (x (.inl f.fst)) (x (.inl f.snd)) y := by
    rw [hr1, hr0, hAd, FaceWalk.ocorner_eq_angle_of_nonneg _ _ _ (hx.unit _) htf hty hin.le,
      angle_tdir_eq_gam _ _ _ (hx.unit _) (hx.unit _) (hx.unit _)
        (by rw [hsf]; exact ⟨hx.d_mem.1, by linarith [hx.d_mem.2, pi_pos]⟩) hsy,
      hsf, sdist_comm y, sdist_comm y, FaceWalk.gam_comm]
  obtain ⟨htc, hts⟩ := turn_cos_sin hx (g.refD f.fst) f hfa
  rw [hfa] at htc hts
  obtain ⟨hac, has⟩ := cos_sin_ocorner_add (x (.inl f.fst)) (x (.inl (g.refD f.fst).snd))
    (x (.inl f.snd)) y (hx.unit _) hta htf hty
  have hcos : cos ((assignOf P H d x).turn (g.refD f.fst) f +
      gam ((assignOf P H d x).r m (c + 1)) ((assignOf P H d x).r m c) (assignOf P H d x).d) =
      cos (ocorner (x (.inl f.fst)) (x (.inl (g.refD f.fst).snd)) y) := by
    rw [Real.cos_add, htc, hts, hγ, ← Real.cos_add, hac]
  have hsin : sin ((assignOf P H d x).turn (g.refD f.fst) f +
      gam ((assignOf P H d x).r m (c + 1)) ((assignOf P H d x).r m c) (assignOf P H d x).d) =
      sin (ocorner (x (.inl f.fst)) (x (.inl (g.refD f.fst).snd)) y) := by
    rw [Real.sin_add, htc, hts, hγ, ← Real.sin_add, has]
  have hY : toEuclideanLin (rframe g x f.fst *
      rotZ ((assignOf P H d x).turn (g.refD f.fst) f +
        gam ((assignOf P H d x).r m (c + 1)) ((assignOf P H d x).r m c) (assignOf P H d x).d) *
      rotY ((assignOf P H d x).r m c)) e3 = y := by
    rw [rotZ_congr _ _ hcos hsin, rotZY_apply_e3]
    simp only [rframe, rmat_apply_e1, rmat_apply_e2, rmat_apply_e3]
    have hp := polar_form (x (.inl f.fst)) (x (.inl (g.refD f.fst).snd)) y (hx.unit _) (hx.unit _)
      hta
    rw [hr0, sdist_comm y]
    exact hp.symm
  rw [frame_eq hx g hg, show ∀ A B C D : Matrix (Fin 3) (Fin 3) ℝ, A * B * C * D = A * (B * C * D)
    from fun A B C D => by simp only [Matrix.mul_assoc], toEuclideanLin_mul_apply, hY]

end Reconstruct

/-- `glue_congruent` of `Tammes15.Hyps.Interfaces`. -/
theorem glue_congruent_proof {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ}
    {x : Pts P k → E3} (_hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi) (hx : Realisation P H d x)
    (g : GlueData P k) (hg : g.Valid) :
    ∃ O : E3 ≃ₗᵢ[ℝ] E3, ∀ a, glueY H (assignOf P H d x) g a = O (x a) := by
  have hM := (Matrix.mem_specialOrthogonalGroup_iff.mp (Reconstruct.rframe_mem_SO hx g hg g.root)).1
  have hMt : (Reconstruct.rframe g x g.root)ᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Matrix.transpose_mem_unitaryGroup_iff.mpr hM
  obtain ⟨O, hO⟩ := Reconstruct.exists_isometry _ hMt
  refine ⟨O, fun a => ?_⟩
  rw [hO]
  cases a with
  | inl v =>
    rw [glueY, Reconstruct.frame_eq hx g hg v, toEuclideanLin_mul_apply]
    simp only [Reconstruct.rframe, Reconstruct.rmat_apply_e3]
  | inr m => exact Reconstruct.glueY_inr hx g hg m

end Tammes15
