import Tammes15.Draw.Defs
import Tammes15.Local41.Rotation
import Tammes15.Trigrows.Sdist

/-!
# The tangent plane at a vertex as the complex line

For a unit vector `v` and a unit vector `e ⊥ v`, the frame `(v, e, v × e)` is orthonormal and
`tcoord v e p = ⟪p, e⟫ + i ⟪p, v × e⟫` is the complex coordinate of the tangent part of `p`. In
this coordinate the corner `ocorner v a b` is the argument of `conj (tcoord a) * tcoord b`
reduced to `[0, 2π)`, so corners at one vertex are differences of the frame angles `fangle`.
Everything about the cyclic order of the neighbours of a vertex is then a statement about
complex numbers.
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

/-- Complex coordinate of `p` in the tangent frame `(e, v × e)` at `v`. -/
noncomputable def tcoord (v e p : E3) : ℂ := ⟨⟪p, e⟫, ⟪p, cross v e⟫⟩

/-- The frame angle of `p` at `v`, in `[0, 2π)`. -/
noncomputable def fangle (v e p : E3) : ℝ := toIcoMod two_pi_pos 0 (Complex.arg (tcoord v e p))

/-! ## The frame -/

theorem exists_unit_orthogonal (v : E3) : ∃ e : E3, ‖e‖ = 1 ∧ ⟪v, e⟫ = 0 := by
  by_cases hv : v = 0
  · -- v = 0 case: any unit vector works, e.g., EuclideanSpace.single 0 1
    refine ⟨EuclideanSpace.single 0 1, ?_, ?_⟩
    · -- ‖EuclideanSpace.single 0 1‖ = 1
      simp [PiLp.norm_single]
    · -- ⟪v, EuclideanSpace.single 0 1⟫ = 0
      rw [hv]
      simp
  · -- v ≠ 0 case: use orthogonal complement
    have hfinrank : Module.finrank ℝ (ℝ ∙ v)ᗮ = 2 := by
      haveI : Fact (Module.finrank ℝ E3 = 2 + 1) :=
        ⟨by
          have h := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
          simpa [show (3 : ℕ) = 2 + 1 by decide] using h⟩
      have := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 2) hv
      exact this
    have hne_bot : (ℝ ∙ v)ᗮ ≠ ⊥ := by
      intro h_eq
      have : Module.finrank ℝ (ℝ ∙ v)ᗮ = 0 := by
        simpa [h_eq] using finrank_bot ℝ (ℝ ∙ v)ᗮ
      rw [hfinrank] at this
      linarith
    obtain ⟨w, hw, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    have hinner : ⟪v, w⟫ = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw)
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · -- ‖‖w‖⁻¹ • w‖ = 1
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw_ne)
    · -- ⟪v, ‖w‖⁻¹ • w⟫ = 0
      rw [inner_smul_right, hinner, mul_zero]

theorem norm_cross_frame (v e : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    ‖cross v e‖ = 1 := by
  have hsq : ‖cross v e‖ ^ 2 = 1 := by
    calc
      ‖cross v e‖ ^ 2 = ‖v‖ ^ 2 * ‖e‖ ^ 2 - ⟪v, e⟫ ^ 2 := norm_cross_sq v e
      _ = 1 ^ 2 * 1 ^ 2 - 0 ^ 2 := by rw [hv, he, hve]
      _ = 1 := by norm_num
  have hnonneg : 0 ≤ ‖cross v e‖ := norm_nonneg _
  nlinarith

open Matrix WithLp in
theorem frame_expand (v e p : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    p = ⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e := by
  -- Let V = ofLp v, E = ofLp e, P = ofLp p, F = V × E
  -- First, note the key identities on Fin 3 → ℝ
  set V := ofLp v with hV
  set E := ofLp e with hE
  set P := ofLp p with hP
  set F := (crossProduct V) E with hF
  -- Goal: P = (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E + (P ⬝ᵥ F) • F
  -- We have hv: ‖v‖ = 1, so ‖V‖ = 1, i.e., V ⬝ᵥ V = 1
  have hVV : V ⬝ᵥ V = 1 := by
    rw [hV]
    -- v.ofLp ⬝ᵥ v.ofLp = inner ℝ v v = ‖v‖ ^ 2 = 1
    -- Use the explicit formula for inner product
    have h_eq : v.ofLp ⬝ᵥ v.ofLp = inner ℝ v v := by
      -- Both sides equal ∑ i, v.ofLp i * v.ofLp i
      calc
        v.ofLp ⬝ᵥ v.ofLp = ∑ i : Fin 3, v.ofLp i * v.ofLp i := rfl
        _ = ∑ i : Fin 3, (v.ofLp i)^2 := by simp [sq]
        _ = ∑ i : Fin 3, inner ℝ (v.ofLp i) (v.ofLp i) := by simp
        _ = inner ℝ v v := by rw [PiLp.inner_apply]
    rw [h_eq]
    rw [real_inner_self_eq_norm_sq v]
    rw [hv]
    norm_num
  have hEE : E ⬝ᵥ E = 1 := by
    rw [hE]
    have h_eq : e.ofLp ⬝ᵥ e.ofLp = inner ℝ e e := by
      calc
        e.ofLp ⬝ᵥ e.ofLp = ∑ i : Fin 3, e.ofLp i * e.ofLp i := rfl
        _ = ∑ i : Fin 3, (e.ofLp i)^2 := by simp [sq]
        _ = ∑ i : Fin 3, inner ℝ (e.ofLp i) (e.ofLp i) := by simp
        _ = inner ℝ e e := by rw [PiLp.inner_apply]
    rw [h_eq]
    rw [real_inner_self_eq_norm_sq e]
    rw [he]
    norm_num
  have hVE : V ⬝ᵥ E = 0 := by
    rw [hV, hE]
    -- v.ofLp ⬝ᵥ e.ofLp = inner ℝ v e = ⟪v, e⟫ = 0
    have h_eq : v.ofLp ⬝ᵥ e.ofLp = inner ℝ v e := by
      calc
        v.ofLp ⬝ᵥ e.ofLp = ∑ i : Fin 3, v.ofLp i * e.ofLp i := rfl
        _ = ∑ i : Fin 3, e.ofLp i * v.ofLp i := by
          apply Finset.sum_congr rfl; intro i _; rw [mul_comm]
        _ = ∑ i : Fin 3, inner ℝ (v.ofLp i) (e.ofLp i) := by simp
        _ = inner ℝ v e := by rw [PiLp.inner_apply]
    rw [h_eq]
    exact hve
  -- Key cross product identities
  have hVF : V ⬝ᵥ F = 0 := by
    -- dot_self_cross
    simpa [hF] using dot_self_cross V E
  have hEF : E ⬝ᵥ F = 0 := by
    -- dot_cross_self
    simpa [hF] using dot_cross_self V E
  have hFF : F ⬝ᵥ F = 1 := by
    -- cross_dot_cross: (V×E)·(V×E) = (V·V)(E·E) - (V·E)(E·V)
    -- = 1*1 - 0*0 = 1
    calc
      F ⬝ᵥ F = (V ⬝ᵥ V) * (E ⬝ᵥ E) - (V ⬝ᵥ E) * (E ⬝ᵥ V) := by
        simpa [hF] using cross_dot_cross V E V E
      _ = 1 * 1 - 0 * (E ⬝ᵥ V) := by rw [hVV, hEE, hVE]
      _ = 1 * 1 - 0 * 0 := by rw [dotProduct_comm E V, hVE]
      _ = 1 := by ring
  -- Now use the triple product identity
  -- cross_cross_eq_smul_sub_smul V E P: (V × E) × P = (V·P) E - (E·P) V
  -- i.e., F × P = (P·V) E - (P·E) V
  have h_cross_FP : (crossProduct F) P = (P ⬝ᵥ V) • E - (P ⬝ᵥ E) • V := by
    calc
      (crossProduct F) P = (crossProduct ((crossProduct V) E)) P := by
        simp [hF]
      _ = (V ⬝ᵥ P) • E - (E ⬝ᵥ P) • V := by
        simpa using cross_cross_eq_smul_sub_smul V E P
      _ = (P ⬝ᵥ V) • E - (P ⬝ᵥ E) • V := by
        simp [dotProduct_comm]
  -- Now compute F × (F × P) in two ways
  -- First way: F × (F × P) = F × ((P·V) E - (P·E) V) = (P·V) (F × E) - (P·E) (F × V)
  -- We need F × E and F × V
  have h_cross_FE : (crossProduct F) E = -V := by
    -- (V × E) × E = (V·E) E - (E·E) V = 0 - 1·V = -V
    rw [hF]
    -- crossProduct ((crossProduct V) E) E = (V ⬝ᵥ E) • E - (E ⬝ᵥ E) • V
    rw [cross_cross_eq_smul_sub_smul V E E]
    rw [hVE, hEE]
    simp
  have h_cross_FV : (crossProduct F) V = E := by
    -- (V × E) × V = (V·V) E - (E·V) V = 1·E - 0 = E
    rw [hF]
    rw [cross_cross_eq_smul_sub_smul V E V]
    rw [hVV, dotProduct_comm E V, hVE]
    simp
  -- Now compute F × (F × P) using the above
  have h_FFP : (crossProduct F) ((crossProduct F) P) = -((P ⬝ᵥ V) • V) - ((P ⬝ᵥ E) • E) := by
    rw [h_cross_FP]
    -- F × ((P·V) E - (P·E) V) = (P·V) (F × E) - (P·E) (F × V)
    -- crossProduct is linear in the second argument
    have h_linear : (crossProduct F) ((P ⬝ᵥ V) • E - (P ⬝ᵥ E) • V) =
        (P ⬝ᵥ V) • ((crossProduct F) E) - (P ⬝ᵥ E) • ((crossProduct F) V) := by
      -- crossProduct is linear in the second argument
      -- crossProduct F (a - b) = crossProduct F a - crossProduct F b
      -- crossProduct F (c • a) = c • crossProduct F a
      rw [map_sub]
      rw [LinearMap.map_smul, LinearMap.map_smul]
    calc
      (crossProduct F) ((P ⬝ᵥ V) • E - (P ⬝ᵥ E) • V) =
          (P ⬝ᵥ V) • ((crossProduct F) E) - (P ⬝ᵥ E) • ((crossProduct F) V) := by
        rw [h_linear]
      _ = (P ⬝ᵥ V) • (-V) - (P ⬝ᵥ E) • E := by rw [h_cross_FE, h_cross_FV]
      _ = -((P ⬝ᵥ V) • V) - ((P ⬝ᵥ E) • E) := by simp
  -- Second way: cross_cross_eq_smul_sub_smul' F F P
  have h_FFP' : (crossProduct F) ((crossProduct F) P) = (F ⬝ᵥ P) • F - (F ⬝ᵥ F) • P := by
    simpa [hF] using cross_cross_eq_smul_sub_smul' F F P
  -- Equate the two expressions for F × (F × P)
  have h_eq : -((P ⬝ᵥ V) • V) - ((P ⬝ᵥ E) • E) = (F ⬝ᵥ P) • F - (F ⬝ᵥ F) • P := by
    rw [← h_FFP, h_FFP']
  -- Rearrange: (F·F) • P = (F·P) • F + (P·V) • V + (P·E) • E
  -- Since F·F = 1, we get P = (F·P) • F + (P·V) • V + (P·E) • E
  -- This is exactly the goal in Fin 3 → ℝ

  -- From h_eq and hFF, we derive the key equation
  have h_key : P = (P ⬝ᵥ F) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E := by
    -- h_eq: -((P ⬝ᵥ V) • V) - ((P ⬝ᵥ E) • E) = (F ⬝ᵥ P) • F - (F ⬝ᵥ F) • P
    -- hFF: F ⬝ᵥ F = 1
    -- Rearranging: (F ⬝ᵥ F) • P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    -- Since F ⬝ᵥ F = 1, we get P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    have h_temp : (F ⬝ᵥ F) • P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E := by
      -- Rearrange h_eq by adding ((P ⬝ᵥ V) • V) + ((P ⬝ᵥ E) • E) + (F ⬝ᵥ F) • P to both sides
      -- This is component-wise algebra, so we use ext
      ext i
      have h_eq_i := congrArg (fun f : Fin 3 → ℝ => f i) h_eq
      simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply] at h_eq_i ⊢
      linarith
    rw [hFF] at h_temp
    -- h_temp: 1 • P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    -- So P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    -- But we want the terms in a different order
    -- h_temp: 1 • P = (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    -- So (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E = P
    -- But we want P = (P ⬝ᵥ F) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E
    -- Use dotProduct_comm to swap F and P
    have h_temp' : (F ⬝ᵥ P) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E = P := by
      simpa [one_smul] using h_temp.symm
    simpa [add_comm, add_left_comm, add_assoc, dotProduct_comm F P] using h_temp'.symm

  -- Now lift back to E3
  -- The goal is: p = ⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e
  -- We'll show that taking ofLp of both sides gives the same result

  -- Compute the ofLp of the RHS
  have h_rhs : ofLp (⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e) =
      (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E + (P ⬝ᵥ F) • F := by
    -- ofLp is linear, so we can distribute component-wise
    ext i
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.inner_apply, cross, hP, hV, hE, hF, dotProduct_comm]
    -- Now we have an equality of sums; expand both sides
    -- The right side has terms like (∑ a) * b; expand them
    -- The left side is already expanded as ∑ (a * b * c)
    -- We just need to expand the right side and then ring
    unfold dotProduct
    simp only [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  -- Now the goal follows from h_key and h_rhs
  apply_fun ofLp
  · -- Goal: ofLp p = ofLp (⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e)
    calc
      ofLp p = P := by rw [hP]
      _ = (P ⬝ᵥ F) • F + (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E := h_key
      _ = (P ⬝ᵥ V) • V + (P ⬝ᵥ E) • E + (P ⬝ᵥ F) • F := by ring
      _ = ofLp (⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e) := by rw [h_rhs]
  · -- ofLp is injective
    exact fun _ _ h => by
      apply_fun toLp 2 at h
      simpa using h

theorem tdir_frame (v e p : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    tdir v p = ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e := by
  unfold tdir
  have h := frame_expand v e p hv he hve
  calc
    p - ⟪v, p⟫ • v = (⟪p, v⟫ • v + ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e) - ⟪v, p⟫ • v := by
      nth_rw 1 [h]
    _ = ⟪p, e⟫ • e + ⟪p, cross v e⟫ • cross v e := by
      rw [real_inner_comm v p]
      abel

theorem inner_tdir_frame (v e a b : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    ⟪tdir v a, tdir v b⟫ = ⟪a, e⟫ * ⟪b, e⟫ + ⟪a, cross v e⟫ * ⟪b, cross v e⟫ := by
  rw [tdir_frame v e a hv he hve, tdir_frame v e b hv he hve]
  simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have h1 : ‖e‖ ^ 2 = 1 := by
    rw [he]
    norm_num
  have h2 : ⟪e, cross v e⟫ = 0 := inner_cross_right_self v e
  have h3 : ⟪cross v e, e⟫ = 0 := by
    rw [real_inner_comm, h2]
  have h4 : ‖cross v e‖ ^ 2 = 1 := by
    rw [norm_cross_frame v e hv he hve]
    norm_num
  rw [h1, h2, h3, h4]
  ring

theorem cross_self_eq_zero (a : E3) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_anticomm_E3 (a b : E3) : cross a b = -cross b a := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_cross_frame (v e : E3) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    cross e (cross v e) = v := by
  have h : WithLp.ofLp (cross e (cross v e)) = WithLp.ofLp v := by
    calc
      WithLp.ofLp (cross e (cross v e)) =
          (crossProduct (WithLp.ofLp e)) ((crossProduct (WithLp.ofLp v)) (WithLp.ofLp e)) := by
        simp [cross]
      _ = (WithLp.ofLp e ⬝ᵥ WithLp.ofLp e) • WithLp.ofLp v -
          (WithLp.ofLp v ⬝ᵥ WithLp.ofLp e) • WithLp.ofLp e := by
        rw [cross_cross_eq_smul_sub_smul']
      _ = ⟪e, e⟫ • WithLp.ofLp v - ⟪v, e⟫ • WithLp.ofLp e := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct_comm]
      _ = ‖e‖ ^ 2 • WithLp.ofLp v - 0 • WithLp.ofLp e := by simp [hve]
      _ = WithLp.ofLp v := by simp [he]
  have := congrArg (WithLp.toLp 2) h
  simpa using this

/-- The corner from an arc to itself is `0`. -/
theorem det_tdir_frame (v e a b : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    ⟪v, cross (tdir v a) (tdir v b)⟫ = ⟪a, e⟫ * ⟪b, cross v e⟫ - ⟪a, cross v e⟫ * ⟪b, e⟫ := by
  set f := cross v e with hf
  have ha := tdir_frame v e a hv he hve
  have hb := tdir_frame v e b hv he hve
  rw [ha, hb]
  have hcross_add_right (x y z : E3) : cross x (y + z) = cross x y + cross x z := by
    ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
  have hcross_add_left (x y z : E3) : cross (x + y) z = cross x z + cross y z := by
    ext i; fin_cases i <;> simp [cross, crossProduct]
  have hcross_smul_right (x y : E3) (r : ℝ) : cross x (r • y) = r • cross x y := by
    ext i; fin_cases i <;> simp [cross, crossProduct]
  have hcross_smul_left (x y : E3) (r : ℝ) : cross (r • x) y = r • cross x y := by
    ext i; fin_cases i <;> simp [cross, crossProduct]
  have hcross_self (x : E3) : cross x x = 0 := cross_self_eq_zero x
  have hcross_anticomm (x y : E3) : cross x y = -cross y x := cross_anticomm_E3 x y
  have hcross_triple : cross e f = v := cross_cross_frame v e he hve
  have hcross_f_e : cross f e = -v := by
    calc
      cross f e = -(-cross f e) := by simp
      _ = -cross e f := by rw [hcross_anticomm e f]
      _ = -v := by rw [hcross_triple]
  calc
    ⟪v, cross (⟪a, e⟫ • e + ⟪a, f⟫ • f) (⟪b, e⟫ • e + ⟪b, f⟫ • f)⟫
        = ⟪v, cross (⟪a, e⟫ • e) (⟪b, e⟫ • e + ⟪b, f⟫ • f) + cross (⟪a, f⟫ • f) (⟪b, e⟫ • e + ⟪b, f⟫ • f)⟫ := by rw [hcross_add_left]
    _ = ⟪v, (cross (⟪a, e⟫ • e) (⟪b, e⟫ • e) + cross (⟪a, e⟫ • e) (⟪b, f⟫ • f)) + (cross (⟪a, f⟫ • f) (⟪b, e⟫ • e) + cross (⟪a, f⟫ • f) (⟪b, f⟫ • f))⟫ := by rw [hcross_add_right, hcross_add_right]
    _ = ⟪v, (⟪a, e⟫ • ⟪b, e⟫ • cross e e + ⟪a, e⟫ • ⟪b, f⟫ • cross e f) + (⟪a, f⟫ • ⟪b, e⟫ • cross f e + ⟪a, f⟫ • ⟪b, f⟫ • cross f f)⟫ := by simp [hcross_smul_left, hcross_smul_right]
    _ = ⟪v, (⟪a, e⟫ • ⟪b, e⟫ • 0 + ⟪a, e⟫ • ⟪b, f⟫ • v) + (⟪a, f⟫ • ⟪b, e⟫ • (-v) + ⟪a, f⟫ • ⟪b, f⟫ • 0)⟫ := by rw [hcross_self e, hcross_self f, hcross_triple, hcross_f_e]
    _ = ⟪v, (⟪a, e⟫ • ⟪b, f⟫ • v - ⟪a, f⟫ • ⟪b, e⟫ • v)⟫ := by
      simp [smul_zero, sub_eq_add_neg]
    _ = ⟪v, (⟪a, e⟫ * ⟪b, f⟫ - ⟪a, f⟫ * ⟪b, e⟫) • v⟫ := by
      simp [smul_smul, sub_smul]
    _ = (⟪a, e⟫ * ⟪b, f⟫ - ⟪a, f⟫ * ⟪b, e⟫) * ⟪v, v⟫ := by simp [inner_smul_right]
    _ = (⟪a, e⟫ * ⟪b, f⟫ - ⟪a, f⟫ * ⟪b, e⟫) * ‖v‖^2 := by rw [real_inner_self_eq_norm_sq]
    _ = (⟪a, e⟫ * ⟪b, f⟫ - ⟪a, f⟫ * ⟪b, e⟫) * 1 := by rw [hv, one_pow]
    _ = ⟪a, e⟫ * ⟪b, f⟫ - ⟪a, f⟫ * ⟪b, e⟫ := by ring
    _ = ⟪a, e⟫ * ⟪b, cross v e⟫ - ⟪a, cross v e⟫ * ⟪b, e⟫ := by rfl

theorem ocorner_eq_arg (v e a b : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    ocorner v a b = toIcoMod two_pi_pos 0 (Complex.arg (conj (tcoord v e a) * tcoord v e b)) := by
  dsimp [ocorner]
  congr 2
  apply Complex.ext
  · rw [inner_tdir_frame v e a b hv he hve]
    simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  · rw [det_tdir_frame v e a b hv he hve]
    simp [tcoord, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

theorem norm_tdir_eq_norm_tcoord (v e a : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) :
    ‖tdir v a‖ = ‖tcoord v e a‖ := by
  have h := inner_tdir_frame v e a a hv he hve
  have hsq_eq : ‖tdir v a‖ ^ 2 = ‖tcoord v e a‖ ^ 2 := by
    calc
      ‖tdir v a‖ ^ 2 = ⟪tdir v a, tdir v a⟫ := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪a, e⟫ * ⟪a, e⟫ + ⟪a, cross v e⟫ * ⟪a, cross v e⟫ := h
      _ = (⟪a, e⟫ ^ 2) + (⟪a, cross v e⟫ ^ 2) := by simp [sq]
      _ = Complex.normSq (tcoord v e a) := by
        simp [tcoord, Complex.normSq_apply, sq]
      _ = ‖tcoord v e a‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
  calc
    ‖tdir v a‖ = Real.sqrt (‖tdir v a‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt (‖tcoord v e a‖ ^ 2) := by rw [hsq_eq]
    _ = ‖tcoord v e a‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

theorem norm_tdir_sq (v a : E3) (hv : ‖v‖ = 1) : ‖tdir v a‖ ^ 2 = ‖a‖ ^ 2 - ⟪v, a⟫ ^ 2 := by
  unfold tdir
  calc
    ‖a - ⟪v, a⟫ • v‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, ⟪v, a⟫ • v⟫ + ‖⟪v, a⟫ • v‖ ^ 2 := by
      simpa using norm_sub_sq_real a (⟪v, a⟫ • v)
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ * ⟪a, v⟫) + ‖⟪v, a⟫ • v‖ ^ 2 := by simp [real_inner_smul_right]
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ * ⟪v, a⟫) + ‖⟪v, a⟫ • v‖ ^ 2 := by rw [real_inner_comm a v]
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ ^ 2) + ‖⟪v, a⟫ • v‖ ^ 2 := by ring
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ ^ 2) + ((⟪v, a⟫ ^ 2) * ‖v‖ ^ 2) := by
      simp [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ ^ 2) + ((⟪v, a⟫ ^ 2) * 1) := by simp [hv]
    _ = ‖a‖ ^ 2 - 2 * (⟪v, a⟫ ^ 2) + (⟪v, a⟫ ^ 2) := by ring
    _ = ‖a‖ ^ 2 - (⟪v, a⟫ ^ 2) := by ring

/-! ## Complex numbers and `toIcoMod` -/

theorem toIcoMod_arg_conj_mul (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    toIcoMod two_pi_pos 0 (Complex.arg (conj z * w)) =
      toIcoMod two_pi_pos 0 (Complex.arg w - Complex.arg z) := by
  have hz' : conj z ≠ 0 := by
    rw [starRingEnd_apply]
    rwa [star_ne_zero]
  have h_angle_eq : (Complex.arg (conj z * w) : Real.Angle) = (Complex.arg w - Complex.arg z : Real.Angle) := by
    calc
      (Complex.arg (conj z * w) : Real.Angle) = (Complex.arg (conj z) : Real.Angle) + (Complex.arg w : Real.Angle) :=
        Complex.arg_mul_coe_angle hz' hw
      _ = (-Complex.arg z : Real.Angle) + (Complex.arg w : Real.Angle) := by
        rw [Complex.arg_conj_coe_angle z]
      _ = (Complex.arg w : Real.Angle) - (Complex.arg z : Real.Angle) := by
        abel
  have h_dvd : ∃ k : ℤ, Complex.arg (conj z * w) - (Complex.arg w - Complex.arg z) = 2 * Real.pi * (k : ℝ) :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h_angle_eq
  rcases h_dvd with ⟨k, hk⟩
  rw [toIcoMod_eq_toIcoMod]
  use -k
  have hcalc : (Complex.arg w - Complex.arg z) - Complex.arg (conj z * w) = (-k : ℤ) • (2 * Real.pi) := by
    calc
      (Complex.arg w - Complex.arg z) - Complex.arg (conj z * w) = -(Complex.arg (conj z * w) - (Complex.arg w - Complex.arg z)) := by ring
      _ = -(2 * Real.pi * (k : ℝ)) := by rw [hk]
      _ = 2 * Real.pi * ((-k : ℤ) : ℝ) := by
        push_cast
        ring
      _ = (-k : ℤ) • (2 * Real.pi) := by
        rw [zsmul_eq_mul, mul_comm]
  exact hcalc

theorem toIcoMod_sub_toIcoMod (x y : ℝ) :
    toIcoMod two_pi_pos 0 (toIcoMod two_pi_pos 0 x - toIcoMod two_pi_pos 0 y) =
      toIcoMod two_pi_pos 0 (x - y) := by
  apply (toIcoMod_eq_toIcoMod (a := 0) two_pi_pos).mpr
  refine ⟨toIcoDiv two_pi_pos 0 x - toIcoDiv two_pi_pos 0 y, ?_⟩
  calc
    (x - y) - (toIcoMod two_pi_pos 0 x - toIcoMod two_pi_pos 0 y)
        = (x - y) - ((x - toIcoDiv two_pi_pos 0 x • (2 * π)) -
          (y - toIcoDiv two_pi_pos 0 y • (2 * π))) := by
      rw [self_sub_toIcoDiv_zsmul two_pi_pos 0 x, self_sub_toIcoDiv_zsmul two_pi_pos 0 y]
    _ = (toIcoDiv two_pi_pos 0 x - toIcoDiv two_pi_pos 0 y) • (2 * π) := by
      ring

theorem arccos_le_toIcoMod_arg (w : ℂ) (hw : w ≠ 0) :
    arccos (w.re / ‖w‖) ≤ toIcoMod two_pi_pos 0 (Complex.arg w) := by
  have hcos := Complex.cos_arg hw
  have h_le_pi : Complex.arg w ≤ π := Complex.arg_le_pi w
  have h_neg_pi_lt : -π < Complex.arg w := Complex.neg_pi_lt_arg w
  rw [← hcos]
  by_cases h_nonneg : 0 ≤ Complex.arg w
  · -- case 0 ≤ arg w ≤ π
    have h_cos_eq : Real.arccos (Real.cos (Complex.arg w)) = Complex.arg w :=
      Real.arccos_cos h_nonneg h_le_pi
    rw [h_cos_eq]
    have h_mem : Complex.arg w ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      rw [zero_add]
      have h_lt : Complex.arg w < 2 * π := by
        linarith [Real.pi_pos]
      exact ⟨h_nonneg, h_lt⟩
    have h_toIcoMod_eq : toIcoMod two_pi_pos 0 (Complex.arg w) = Complex.arg w :=
      (toIcoMod_eq_self two_pi_pos).mpr h_mem
    rw [h_toIcoMod_eq]
  · -- case arg w < 0
    have h_neg : Complex.arg w < 0 := by linarith
    have h_cos_neg : Real.cos (Complex.arg w) = Real.cos (-(Complex.arg w)) := by
      rw [Real.cos_neg]
    rw [h_cos_neg]
    have h_nonneg_neg : 0 ≤ -(Complex.arg w) := by linarith
    have h_le_pi_neg : -(Complex.arg w) ≤ π := by linarith
    have h_cos_eq : Real.arccos (Real.cos (-(Complex.arg w))) = -(Complex.arg w) :=
      Real.arccos_cos h_nonneg_neg h_le_pi_neg
    rw [h_cos_eq]
    have h_toIcoMod_eq : toIcoMod two_pi_pos 0 (Complex.arg w) = Complex.arg w + 2 * π := by
      have h_add : toIcoMod two_pi_pos 0 (Complex.arg w + 2 * π) = Complex.arg w + 2 * π := by
        apply (toIcoMod_eq_self two_pi_pos).mpr
        constructor
        · linarith
        · linarith [Real.pi_pos]
      have h_add_right := toIcoMod_add_right two_pi_pos 0 (Complex.arg w)
      -- h_add_right : toIcoMod two_pi_pos 0 ((Complex.arg w) + (2 * π)) = toIcoMod two_pi_pos 0 (Complex.arg w)
      exact h_add_right.symm.trans h_add
    rw [h_toIcoMod_eq]
    linarith

theorem eq_of_toIcoMod_arg_conj_mul_eq_zero (z w : ℂ) (hz : z ≠ 0) (hn : ‖z‖ = ‖w‖)
    (h : toIcoMod two_pi_pos 0 (Complex.arg (conj z * w)) = 0) : z = w := by
  set q := conj z * w with hq_def
  have hw : w ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hn, norm_ne_zero_iff]
    exact hz
  have hq_ne : q ≠ 0 := mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hz) hw
  have harg_eq_zero : Complex.arg q = 0 := by
    rcases (toIcoMod_eq_iff two_pi_pos).mp h with ⟨h_mem, n, h_eq⟩
    have h_eq' : Complex.arg q = (n : ℝ) * (2 * Real.pi) := by
      simpa [add_comm, zsmul_eq_mul] using h_eq
    have h_lower : -Real.pi < (n : ℝ) * (2 * Real.pi) := by
      rw [← h_eq']
      exact Complex.neg_pi_lt_arg q
    have h_upper : (n : ℝ) * (2 * Real.pi) ≤ Real.pi := by
      rw [← h_eq']
      exact Complex.arg_le_pi q
    have hn_abs_lt_one : |(n : ℝ)| < 1 := by
      have h_abs_lt : - (2 * Real.pi) < (n : ℝ) * (2 * Real.pi) ∧ (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
        constructor
        · nlinarith
        · nlinarith
      rcases h_abs_lt with ⟨hlt_low, hlt_high⟩
      have h_abs_mul : |(n : ℝ) * (2 * Real.pi)| = |(n : ℝ)| * |2 * Real.pi| := abs_mul _ _
      have h_abs_two_pi : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
      have h_abs_lt' : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨hlt_low, hlt_high⟩
      rw [h_abs_mul, h_abs_two_pi] at h_abs_lt'
      have h_pos : 0 < 2 * Real.pi := by positivity
      nlinarith
    have hn_abs_lt_one_int : |n| < (1 : ℤ) := by
      have : (|n| : ℝ) < (1 : ℝ) := by
        calc
          (|n| : ℝ) = |(n : ℝ)| := by simp
          _ < 1 := hn_abs_lt_one
      exact_mod_cast this
    rw [Int.abs_lt_one_iff] at hn_abs_lt_one_int
    have hn_zero : (n : ℝ) = 0 := by exact_mod_cast hn_abs_lt_one_int
    rw [hn_zero] at h_eq'
    simpa using h_eq'
  have hq_real : q.re ≥ 0 ∧ q.im = 0 := by
    rw [← Complex.arg_eq_zero_iff]
    exact harg_eq_zero
  rcases hq_real with ⟨hq_re_nonneg, hq_im_zero⟩
  have hq_eq_re : q = (q.re : ℂ) := by
    calc
      q = (q.re : ℂ) + (q.im : ℂ) * Complex.I := by rw [Complex.re_add_im q]
      _ = (q.re : ℂ) := by simp [hq_im_zero]
  have h_norm_q : ‖q‖ = q.re := by
    rw [hq_eq_re]
    calc
      ‖(q.re : ℂ)‖ = ‖q.re‖ := Complex.norm_real _
      _ = |q.re| := Real.norm_eq_abs _
      _ = q.re := abs_of_nonneg hq_re_nonneg
  have h_norm_q_sq : ‖q‖ = ‖z‖ ^ 2 := by
    calc
      ‖q‖ = ‖conj z * w‖ := rfl
      _ = ‖conj z‖ * ‖w‖ := by rw [Complex.norm_mul]
      _ = ‖z‖ * ‖w‖ := by rw [Complex.norm_conj]
      _ = ‖z‖ * ‖z‖ := by rw [hn]
      _ = ‖z‖ ^ 2 := by ring
  have h_conj_mul_z : conj z * z = ((‖z‖ : ℂ) ^ 2) := by
    rw [Complex.conj_mul']
  have hq_eq_conj_mul_z : q = conj z * z := by
    calc
      q = (q.re : ℂ) := hq_eq_re
      _ = (‖q‖ : ℂ) := by simp [h_norm_q]
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [h_norm_q_sq]
      _ = ((‖z‖ : ℂ) ^ 2) := by simp
      _ = conj z * z := by rw [h_conj_mul_z]
  have h_conj_ne : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  rw [hq_def] at hq_eq_conj_mul_z
  -- hq_eq_conj_mul_z : conj z * w = conj z * z
  have h_eq : w = z := mul_left_cancel₀ h_conj_ne hq_eq_conj_mul_z
  rw [h_eq]

/-- The half-plane step of Lemma A.2, in the complex line: if the gap after `z a` in the cyclic
order is at least `π`, a unit `u` has every `z i` in the closed half-plane `Re (conj u * z) ≤ 0`. -/
theorem exists_halfplane_of_gap {ι : Type*} (z : ι → ℂ) (hz : ∀ i, z i ≠ 0) (a : ι) (θ : ℝ)
    (hθ : π ≤ θ ∧ θ ≤ 2 * π)
    (hgap : ∀ i, i ≠ a → θ ≤ toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, (conj u * z i).re ≤ 0 := by
  rcases hθ with ⟨hθl, hθr⟩
  have hθ_half_l : π / 2 ≤ θ / 2 := by linarith
  have hθ_half_r : θ / 2 ≤ π := by linarith
  set u := Complex.exp (↑(Complex.arg (z a) + θ / 2) * Complex.I) with hu_def
  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def]
    exact Complex.norm_exp_ofReal_mul_I _
  refine ⟨u, hu_norm, ?_⟩
  intro i
  have hz_polar : z i = ‖z i‖ * Complex.exp (↑(Complex.arg (z i)) * Complex.I) := by
    simpa [mul_comm] using (Complex.norm_mul_exp_arg_mul_I (z i)).symm
  rw [hz_polar]
  -- Target: (conj u * (‖z i‖ * exp(arg(z i)*I))).re ≤ 0
  -- Rearrange to (‖z i‖ * (conj u * exp(arg(z i)*I))).re ≤ 0
  have h_mul : conj u * (‖z i‖ * Complex.exp (↑(Complex.arg (z i)) * Complex.I)) =
      ‖z i‖ * (conj u * Complex.exp (↑(Complex.arg (z i)) * Complex.I)) := by ring
  rw [h_mul]
  rw [hu_def]
  have h_conj_exp : conj (Complex.exp (↑(Complex.arg (z a) + θ / 2) * Complex.I)) =
      Complex.exp (-(↑(Complex.arg (z a) + θ / 2) * Complex.I)) := by
    calc
      conj (Complex.exp (↑(Complex.arg (z a) + θ / 2) * Complex.I))
          = Complex.exp (conj (↑(Complex.arg (z a) + θ / 2) * Complex.I)) := by
        rw [Complex.exp_conj]
      _ = Complex.exp (conj (↑(Complex.arg (z a) + θ / 2)) * conj Complex.I) := by
        rw [map_mul]
      _ = Complex.exp ((↑(Complex.arg (z a) + θ / 2)) * (-Complex.I)) := by
        rw [Complex.conj_ofReal (Complex.arg (z a) + θ / 2), Complex.conj_I]
      _ = Complex.exp (-(↑(Complex.arg (z a) + θ / 2) * Complex.I)) := by
        rw [mul_neg]
  rw [h_conj_exp]
  rw [← Complex.exp_add]
  have h_arg : -(↑(Complex.arg (z a) + θ / 2) * Complex.I) + ↑(Complex.arg (z i)) * Complex.I =
      (↑(Complex.arg (z i) - Complex.arg (z a) - θ / 2)) * Complex.I := by
    push_cast
    ring
  rw [h_arg]
  rw [Complex.re_ofReal_mul]
  rw [Complex.exp_ofReal_mul_I_re]
  have h_norm_nonneg : 0 ≤ ‖z i‖ := norm_nonneg _
  by_cases hi : i = a
  · rw [hi]
    have hcos : Real.cos (Complex.arg (z a) - Complex.arg (z a) - θ / 2) = Real.cos (θ / 2) := by
      simp [Real.cos_neg]
    rw [hcos]
    have hcos_nonpos : Real.cos (θ / 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hθ_half_l (by linarith)
    have h_norm_nonneg_a : 0 ≤ ‖z a‖ := norm_nonneg _
    exact mul_nonpos_of_nonneg_of_nonpos h_norm_nonneg_a hcos_nonpos
  · set ψ := toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a)) with hψ_def
    have hψ_mem : ψ ∈ Set.Ico θ (2 * π) := by
      have hle : θ ≤ ψ := hgap i hi
      have hmem := toIcoMod_mem_Ico two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))
      rcases (Set.mem_Ico.1 hmem) with ⟨hlo, hhi⟩
      -- hlo : 0 ≤ ψ, hhi : ψ < 0 + 2*π
      have hhi' : ψ < 2 * π := by simpa [zero_add] using hhi
      exact Set.mem_Ico.mpr ⟨hle, hhi'⟩
    rcases hψ_mem with ⟨hψ_l, hψ_r⟩
    have h_eq : Complex.arg (z i) - Complex.arg (z a) =
        ψ + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) := by
      calc
        Complex.arg (z i) - Complex.arg (z a)
            = ((Complex.arg (z i) - Complex.arg (z a)) -
                (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π))
              + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) := by ring
        _ = toIcoMod two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))
              + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) := by
          rw [self_sub_toIcoDiv_zsmul two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))]
        _ = ψ + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) := by
          rw [hψ_def]
    have h_cos_eq : Real.cos (Complex.arg (z i) - Complex.arg (z a) - θ / 2) =
        Real.cos (ψ - θ / 2) := by
      rw [h_eq]
      -- cos((ψ + n*(2π)) - θ/2) = cos(ψ - θ/2 + n*(2π)) = cos(ψ - θ/2)
      have h_add : (ψ + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π)) - θ / 2 =
          (ψ - θ / 2) + (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) := by ring
      rw [h_add]
      -- Rewrite zsmul • (2*π) as (n : ℝ) * (2*π)
      have h_zsmul : (toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) • (2 * π) =
          ((toIcoDiv two_pi_pos 0 (Complex.arg (z i) - Complex.arg (z a))) : ℝ) * (2 * π) := by
        simp
      rw [h_zsmul]
      rw [Real.cos_add_int_mul_two_pi]
    rw [h_cos_eq]
    have h_lower : π / 2 ≤ ψ - θ / 2 := by linarith
    have h_upper : ψ - θ / 2 ≤ π + π / 2 := by linarith
    have hcos_nonpos : Real.cos (ψ - θ / 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h_lower h_upper
    exact mul_nonpos_of_nonneg_of_nonpos h_norm_nonneg hcos_nonpos

/-! ## Corners in the frame -/

theorem ocorner_eq_fangle_sub (v e a b : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0)
    (ha : tdir v a ≠ 0) (hb : tdir v b ≠ 0) :
    ocorner v a b = toIcoMod two_pi_pos 0 (fangle v e b - fangle v e a) := by
  rw [ocorner_eq_arg v e a b hv he hve]
  have hza : tcoord v e a ≠ 0 := by
    intro hzero
    apply ha
    have hnorm := norm_tdir_eq_norm_tcoord v e a hv he hve
    have hzero' : ‖tcoord v e a‖ = 0 := by simp [hzero]
    rw [hzero'] at hnorm
    exact norm_eq_zero.mp hnorm
  have hzb : tcoord v e b ≠ 0 := by
    intro hzero
    apply hb
    have hnorm := norm_tdir_eq_norm_tcoord v e b hv he hve
    have hzero' : ‖tcoord v e b‖ = 0 := by simp [hzero]
    rw [hzero'] at hnorm
    exact norm_eq_zero.mp hnorm
  rw [toIcoMod_arg_conj_mul (tcoord v e a) (tcoord v e b) hza hzb]
  unfold fangle
  rw [toIcoMod_sub_toIcoMod]

theorem tangent_of_complex (v e : E3) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hve : ⟪v, e⟫ = 0) (u : ℂ) :
    ‖u.re • e + u.im • cross v e‖ = ‖u‖ ∧ ⟪v, u.re • e + u.im • cross v e⟫ = 0 ∧
      ∀ p, ⟪u.re • e + u.im • cross v e, p⟫ = (conj u * tcoord v e p).re := by
  set f := cross v e
  have hf_norm : ‖f‖ = 1 := norm_cross_frame v e hv he hve
  have h_inner_v_f : ⟪v, f⟫ = 0 := inner_cross_self v e
  have h_inner_e_f : ⟪e, f⟫ = 0 := inner_cross_right_self v e
  have h_sq_eq : ‖u.re • e + u.im • f‖ ^ 2 = ‖u‖ ^ 2 := by
    calc
      ‖u.re • e + u.im • f‖ ^ 2 = ‖u.re • e‖ ^ 2 + 2 * ⟪u.re • e, u.im • f⟫ + ‖u.im • f‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = (|u.re| * ‖e‖) ^ 2 + 2 * (u.re * u.im * ⟪e, f⟫) + (|u.im| * ‖f‖) ^ 2 := by
        simp [norm_smul, real_inner_smul_right, real_inner_smul_left, mul_left_comm, mul_assoc]
      _ = (|u.re| ^ 2 * ‖e‖ ^ 2) + 2 * (u.re * u.im * ⟪e, f⟫) + (|u.im| ^ 2 * ‖f‖ ^ 2) := by ring
      _ = (u.re ^ 2 * ‖e‖ ^ 2) + 2 * (u.re * u.im * ⟪e, f⟫) + (u.im ^ 2 * ‖f‖ ^ 2) := by
        simp [sq_abs]
      _ = (u.re ^ 2 * 1) + 2 * (u.re * u.im * 0) + (u.im ^ 2 * 1) := by
        simp [he, hf_norm, h_inner_e_f]
      _ = u.re ^ 2 + u.im ^ 2 := by ring
      _ = u.re * u.re + u.im * u.im := by ring
      _ = Complex.normSq u := by rw [Complex.normSq_apply]
      _ = ‖u‖ ^ 2 := by rw [Complex.sq_norm]
  have h_norm_eq : ‖u.re • e + u.im • f‖ = ‖u‖ := by
    have h_nonneg_left : 0 ≤ ‖u.re • e + u.im • f‖ := norm_nonneg _
    have h_nonneg_right : 0 ≤ ‖u‖ := norm_nonneg _
    nlinarith
  have h_inner_v : ⟪v, u.re • e + u.im • f⟫ = 0 := by
    rw [inner_add_right]
    simp [real_inner_smul_right, hve, h_inner_v_f]
  have h_formula : ∀ p, ⟪u.re • e + u.im • f, p⟫ = (conj u * tcoord v e p).re := by
    intro p
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp [tcoord, f, Complex.mul_re, Complex.conj_re, Complex.conj_im, real_inner_comm]
  exact And.intro h_norm_eq (And.intro h_inner_v h_formula)

/-- Lemma A.1 in oriented form: the oriented corner is at least the unoriented one. -/
theorem angle_le_ocorner (v a b : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0) (hb : tdir v b ≠ 0) :
    angle (tdir v a) (tdir v b) ≤ ocorner v a b := by
  obtain ⟨e, he, hve⟩ := exists_unit_orthogonal v
  set z := tcoord v e a with hz_def
  set w := tcoord v e b with hw_def
  set q := conj z * w with hq_def
  have hz_ne_zero : z ≠ 0 := by
    intro hz0
    apply ha
    have : ‖tdir v a‖ = 0 := by
      rw [norm_tdir_eq_norm_tcoord v e a hv he hve, ← hz_def, hz0, norm_zero]
    exact norm_eq_zero.mp this
  have hw_ne_zero : w ≠ 0 := by
    intro hw0
    apply hb
    have : ‖tdir v b‖ = 0 := by
      rw [norm_tdir_eq_norm_tcoord v e b hv he hve, ← hw_def, hw0, norm_zero]
    exact norm_eq_zero.mp this
  have hq_ne_zero : q ≠ 0 := by
    rw [hq_def]
    have h_conj_ne_zero : conj z ≠ 0 := by
      intro h
      apply hz_ne_zero
      apply (starRingEnd ℂ).injective
      simpa using h
    exact mul_ne_zero h_conj_ne_zero hw_ne_zero
  have h_ocorner : ocorner v a b = toIcoMod two_pi_pos 0 (Complex.arg q) := by
    rw [hq_def]
    exact ocorner_eq_arg v e a b hv he hve
  have h_inner : ⟪tdir v a, tdir v b⟫ = q.re := by
    rw [hq_def, hz_def, hw_def]
    rw [inner_tdir_frame v e a b hv he hve]
    simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have h_norm : ‖tdir v a‖ * ‖tdir v b‖ = ‖q‖ := by
    rw [hq_def, hz_def, hw_def]
    rw [norm_tdir_eq_norm_tcoord v e a hv he hve, norm_tdir_eq_norm_tcoord v e b hv he hve]
    calc
      ‖z‖ * ‖w‖ = ‖z‖ * ‖w‖ := rfl
      _ = ‖conj z‖ * ‖w‖ := by rw [Complex.norm_conj]
      _ = ‖conj z * w‖ := by rw [norm_mul]
  have h_angle : angle (tdir v a) (tdir v b) = Real.arccos (q.re / ‖q‖) := by
    rw [angle, h_inner, h_norm]
  rw [h_angle, h_ocorner]
  exact arccos_le_toIcoMod_arg q hq_ne_zero

/-- Two points at the same distance from `v` in the same direction are equal. -/
theorem eq_of_ocorner_eq_zero (v a b : E3) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪v, a⟫ = ⟪v, b⟫) (hta : tdir v a ≠ 0) (h : ocorner v a b = 0) : a = b := by
  -- Get a unit vector e orthogonal to v
  obtain ⟨e, he, hve⟩ := exists_unit_orthogonal v
  -- From norm_tdir_sq, both ‖tdir v a‖² and ‖tdir v b‖² equal 1 - ⟪v, a⟫², so they are equal
  have h_norm_tdir_eq : ‖tdir v a‖ = ‖tdir v b‖ := by
    have h_sq_a : ‖tdir v a‖ ^ 2 = ‖a‖ ^ 2 - ⟪v, a⟫ ^ 2 := norm_tdir_sq v a hv
    have h_sq_b : ‖tdir v b‖ ^ 2 = ‖b‖ ^ 2 - ⟪v, b⟫ ^ 2 := norm_tdir_sq v b hv
    rw [ha, hab] at h_sq_a
    rw [hb] at h_sq_b
    -- h_sq_a: ‖tdir v a‖ ^ 2 = 1 - ⟪v, b⟫ ^ 2
    -- h_sq_b: ‖tdir v b‖ ^ 2 = 1 - ⟪v, b⟫ ^ 2
    have h_sq_eq : ‖tdir v a‖ ^ 2 = ‖tdir v b‖ ^ 2 := by
      rw [h_sq_a, h_sq_b]
    have h_nonneg_a : 0 ≤ ‖tdir v a‖ := norm_nonneg _
    have h_nonneg_b : 0 ≤ ‖tdir v b‖ := norm_nonneg _
    nlinarith
  -- Set z = tcoord v e a, w = tcoord v e b
  set z := tcoord v e a with hz_def
  set w := tcoord v e b with hw_def
  have hz_ne_zero : z ≠ 0 := by
    rw [hz_def]
    have h_norm_eq : ‖tdir v a‖ = ‖tcoord v e a‖ := norm_tdir_eq_norm_tcoord v e a hv he hve
    intro hzero
    have h_norm_zero : ‖tdir v a‖ = 0 := by
      rw [h_norm_eq, hzero, norm_zero]
    have h_tdir_zero : tdir v a = 0 := norm_eq_zero.mp h_norm_zero
    exact hta h_tdir_zero
  have h_norm_z_eq_norm_w : ‖z‖ = ‖w‖ := by
    rw [hz_def, hw_def]
    calc
      ‖tcoord v e a‖ = ‖tdir v a‖ := (norm_tdir_eq_norm_tcoord v e a hv he hve).symm
      _ = ‖tdir v b‖ := h_norm_tdir_eq
      _ = ‖tcoord v e b‖ := norm_tdir_eq_norm_tcoord v e b hv he hve
  -- From ocorner_eq_arg, h gives us a condition on z and w
  have h_arg : toIcoMod two_pi_pos 0 (Complex.arg (conj z * w)) = 0 := by
    have h_ocorner_eq : ocorner v a b = toIcoMod two_pi_pos 0 (Complex.arg (conj (tcoord v e a) * tcoord v e b)) :=
      ocorner_eq_arg v e a b hv he hve
    rw [h_ocorner_eq] at h
    -- h: toIcoMod two_pi_pos 0 (Complex.arg (conj (tcoord v e a) * tcoord v e b)) = 0
    rw [← hz_def, ← hw_def] at h
    exact h
  -- Now use eq_of_toIcoMod_arg_conj_mul_eq_zero to get z = w
  have h_zw_eq : z = w :=
    eq_of_toIcoMod_arg_conj_mul_eq_zero z w hz_ne_zero h_norm_z_eq_norm_w h_arg
  -- From z = w, extract component equalities via Complex.ext_iff
  have h_components : ⟪a, e⟫ = ⟪b, e⟫ ∧ ⟪a, cross v e⟫ = ⟪b, cross v e⟫ := by
    rw [hz_def, hw_def] at h_zw_eq
    have h_ext := Complex.ext_iff.mp h_zw_eq
    -- h_ext: (tcoord v e a).re = (tcoord v e b).re ∧ (tcoord v e a).im = (tcoord v e b).im
    -- tcoord v e a = ⟨⟪a, e⟫, ⟪a, cross v e⟫⟩
    -- So re = ⟪a, e⟫, im = ⟪a, cross v e⟫
    simpa [tcoord] using h_ext
  -- Also have ⟪a, v⟫ = ⟪b, v⟫ from hab
  have h_inner_v_eq : ⟪a, v⟫ = ⟪b, v⟫ := by
    calc
      ⟪a, v⟫ = ⟪v, a⟫ := real_inner_comm _ _
      _ = ⟪v, b⟫ := by rw [hab]
      _ = ⟪b, v⟫ := (real_inner_comm _ _).symm
  -- Now use frame_expand to conclude a = b
  rcases h_components with ⟨h_e, h_cross⟩
  calc
    a = ⟪a, v⟫ • v + ⟪a, e⟫ • e + ⟪a, cross v e⟫ • cross v e :=
      frame_expand v e a hv he hve
    _ = ⟪b, v⟫ • v + ⟪b, e⟫ • e + ⟪b, cross v e⟫ • cross v e := by rw [h_inner_v_eq, h_e, h_cross]
    _ = b := (frame_expand v e b hv he hve).symm

/-- The corner from an arc to itself is `0`. -/
theorem ocorner_self (v a : E3) : ocorner v a a = 0 := by
  unfold ocorner
  rw [cross_self_eq_zero, inner_zero_right]
  have h2 : (0 : ℝ) ≤ ⟪tdir v a, tdir v a⟫ := real_inner_self_nonneg
  rw [show (⟨⟪tdir v a, tdir v a⟫, 0⟩ : ℂ) = ((⟪tdir v a, tdir v a⟫ : ℝ) : ℂ) from
    Complex.ext rfl rfl, Complex.arg_ofReal_of_nonneg h2]
  exact (toIcoMod_eq_self two_pi_pos).mpr ⟨le_refl 0, by linarith [Real.pi_pos]⟩

/-- A corner from an arc of zero tangent direction is `0`. -/
theorem ocorner_of_tdir_eq_zero (v a b : E3) (h : tdir v a = 0) : ocorner v a b = 0 := by
  unfold ocorner
  rw [h, inner_zero_left]
  have h0 : cross 0 (tdir v b) = 0 := by
    ext i; fin_cases i <;> simp [cross, crossProduct]
  rw [h0, inner_zero_right, show (⟨0, 0⟩ : ℂ) = 0 from rfl, Complex.arg_zero]
  exact (toIcoMod_eq_self two_pi_pos).mpr ⟨le_refl 0, by linarith [Real.pi_pos]⟩

end Tammes15
