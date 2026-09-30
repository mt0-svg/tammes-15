import Tammes15.Challenge.Statement

/-!
# Gluing: rotation matrices and the enclosure bound

The frames of Section 5.4 are products `F(v) R_z(φ) R_y(d) Z`; the enclosure
`|Y(w) - Y_c(w)| ≤ ϱ(w)` rests on `|R_z(φ) v - R_z(ψ) v| ≤ |φ - ψ| |v|` (the same for `R_y`) and
on the telescoping bound for products of isometries, stated here on vectors (no operator norm).
-/

open Real Matrix

namespace Tammes15

/-- Rotation by `φ` about the third axis. -/
noncomputable def rotZ (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos φ, -sin φ, 0; sin φ, cos φ, 0; 0, 0, 1]

/-- Rotation by `θ` about the second axis. -/
noncomputable def rotY (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, 0, sin θ; 0, 1, 0; -sin θ, 0, cos θ]

/-- `Z = diag(-1, -1, 1)`. -/
def flipZ : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

theorem norm_rotZ_apply (φ : ℝ) (v : E3) : ‖toEuclideanLin (rotZ φ) v‖ = ‖v‖ := by
  have hsq : ‖toEuclideanLin (rotZ φ) v‖ ^ 2 = ‖v‖ ^ 2 := by
    calc
      ‖toEuclideanLin (rotZ φ) v‖ ^ 2 = ∑ i : Fin 3, ((toEuclideanLin (rotZ φ) v).ofLp i) ^ 2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq (x := toEuclideanLin (rotZ φ) v))
      _ = ∑ i : Fin 3, (((rotZ φ).mulVec v.ofLp) i) ^ 2 := by
        have h : ((toEuclideanLin (rotZ φ)) v).ofLp = (rotZ φ).mulVec v.ofLp := by
          calc
            ((toEuclideanLin (rotZ φ)) v).ofLp = ((toLpLin 2 2 (rotZ φ)) v).ofLp := rfl
            _ = ((WithLp.toLp 2 ((rotZ φ).mulVec v.ofLp))).ofLp := by simp [Matrix.toLpLin_apply]
            _ = (rotZ φ).mulVec v.ofLp := by simp
        simp [h]
      _ = (((rotZ φ).mulVec v.ofLp) 0) ^ 2 + (((rotZ φ).mulVec v.ofLp) 1) ^ 2 + (((rotZ φ).mulVec v.ofLp) 2) ^ 2 := by
        simp [Fin.sum_univ_three]
      _ = (cos φ * v.ofLp 0 - sin φ * v.ofLp 1) ^ 2 + (sin φ * v.ofLp 0 + cos φ * v.ofLp 1) ^ 2 + (v.ofLp 2) ^ 2 := by
        have h0 : ((rotZ φ).mulVec v.ofLp) 0 = cos φ * v.ofLp 0 - sin φ * v.ofLp 1 := by
          simp [rotZ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, sub_eq_add_neg]
        have h1 : ((rotZ φ).mulVec v.ofLp) 1 = sin φ * v.ofLp 0 + cos φ * v.ofLp 1 := by
          simp [rotZ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
        have h2 : ((rotZ φ).mulVec v.ofLp) 2 = v.ofLp 2 := by
          simp [rotZ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three]
        simp [h0, h1, h2]
      _ = (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2 + (v.ofLp 2) ^ 2 := by
        nlinarith [Real.cos_sq_add_sin_sq φ]
      _ = ∑ i : Fin 3, (v.ofLp i) ^ 2 := by
        simp [Fin.sum_univ_three]
      _ = ‖v‖ ^ 2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq (x := v)).symm
  have hpos1 : 0 ≤ ‖toEuclideanLin (rotZ φ) v‖ := norm_nonneg _
  have hpos2 : 0 ≤ ‖v‖ := norm_nonneg _
  exact (sq_eq_sq₀ hpos1 hpos2).mp hsq

theorem norm_rotY_apply (θ : ℝ) (v : E3) : ‖toEuclideanLin (rotY θ) v‖ = ‖v‖ := by
  have h_sq : ‖toEuclideanLin (rotY θ) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [Matrix.toEuclideanLin, ofLp_toLpLin, Matrix.toLin'_apply]
    simp [rotY, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
    ring_nf
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have h_nonneg : 0 ≤ ‖toEuclideanLin (rotY θ) v‖ := norm_nonneg _
  have h_nonneg' : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith

theorem norm_flipZ_apply (v : E3) : ‖toEuclideanLin flipZ v‖ = ‖v‖ := by
  rw [toEuclideanLin, toLpLin_apply]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [flipZ, Matrix.mulVec_apply, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]

theorem rotZ_sub_apply_le (φ ψ : ℝ) (v : E3) :
    ‖toEuclideanLin (rotZ φ) v - toEuclideanLin (rotZ ψ) v‖ ≤ |φ - ψ| * ‖v‖ := by
  -- Write v in coordinates
  let x := v 0
  let y := v 1
  let z := v 2
  have hv : v = WithLp.toLp 2 ![x, y, z] := by
    ext i; fin_cases i <;> simp [x, y, z]
  rw [hv]
  -- Now v is WithLp.toLp 2 ![x, y, z]
  -- Compute the difference
  have hrotZ_apply (θ : ℝ) : toEuclideanLin (rotZ θ) (WithLp.toLp 2 ![x, y, z]) =
      WithLp.toLp 2 ![cos θ * x - sin θ * y, sin θ * x + cos θ * y, z] := by
    ext i; fin_cases i <;> simp [rotZ, Matrix.toEuclideanLin] <;> ring
  rw [hrotZ_apply φ, hrotZ_apply ψ]
  -- The difference is WithLp.toLp 2 ![a*x - b*y, b*x + a*y, 0] where a = cos φ - cos ψ, b = sin φ - sin ψ
  set a := cos φ - cos ψ with ha
  set b := sin φ - sin ψ with hb
  -- Compute the difference explicitly
  have hdiff : WithLp.toLp 2 ![cos φ * x - sin φ * y, sin φ * x + cos φ * y, z] -
      WithLp.toLp 2 ![cos ψ * x - sin ψ * y, sin ψ * x + cos ψ * y, z] =
      WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0] := by
    ext i; fin_cases i <;> dsimp [a, b] <;> ring
  rw [hdiff]
  -- Now we need to show ‖WithLp.toLp 2 ![a*x - b*y, b*x + a*y, 0]‖ ≤ |φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖
  -- Compute norm squared of the difference
  have hnorm_sq_diff : ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ ^ 2 = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    ring
  -- Compute norm squared of v
  have hnorm_sq_v : ‖WithLp.toLp 2 ![x, y, z]‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  -- Compute a^2 + b^2 = 2*(1 - cos(φ-ψ))
  have ha_sq_add_b_sq' : a ^ 2 + b ^ 2 = 2 * (1 - cos (φ - ψ)) := by
    dsimp [a, b]
    rw [Real.cos_sub]
    have h1 : cos φ ^ 2 + sin φ ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq φ]
    have h2 : cos ψ ^ 2 + sin ψ ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq ψ]
    nlinarith
  -- Use the identity: 1 - cos θ = 2*sin^2(θ/2)
  have hhalf : 1 - cos (φ - ψ) = 2 * (Real.sin ((φ - ψ) / 2)) ^ 2 := by
    have := Real.sin_sq_eq_half_sub ((φ - ψ) / 2)
    rw [this]
    ring_nf
  -- Now: a^2 + b^2 = 2*(1 - cos(φ-ψ)) = 4*sin^2((φ-ψ)/2) ≤ (φ-ψ)^2
  have hbound : a ^ 2 + b ^ 2 ≤ (φ - ψ) ^ 2 := by
    rw [ha_sq_add_b_sq', hhalf]
    have hsin : (Real.sin ((φ - ψ) / 2)) ^ 2 ≤ ((φ - ψ) / 2) ^ 2 := Real.sin_sq_le_sq
    nlinarith
  -- Now we have: ‖diff‖^2 = (a^2+b^2)*(x^2+y^2) ≤ (φ-ψ)^2*(x^2+y^2) ≤ (φ-ψ)^2*(x^2+y^2+z^2) = (φ-ψ)^2*‖v‖^2
  have h_sq_le : ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ ^ 2 ≤ ((φ - ψ) * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by
    rw [hnorm_sq_diff]
    have hxysq : x ^ 2 + y ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by nlinarith [sq_nonneg z]
    have hnorm_sq_v' : ‖WithLp.toLp 2 ![x, y, z]‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := hnorm_sq_v
    nlinarith
  -- Take square root (all nonnegative)
  have h_nonneg_norm : 0 ≤ ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ := norm_nonneg _
  have h_nonneg_rhs : 0 ≤ |φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖ := by
    apply mul_nonneg (abs_nonneg _) (norm_nonneg _)
  -- Using the lemma: if a^2 ≤ b^2 and 0 ≤ b, then a ≤ b
  have h_final : ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ ≤ |φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖ := by
    have h_sq : ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ ^ 2 ≤ (|φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by
      calc
        ‖WithLp.toLp 2 ![a * x - b * y, b * x + a * y, 0]‖ ^ 2 ≤ ((φ - ψ) * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := h_sq_le
        _ = (|φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by
          calc
            ((φ - ψ) * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 = (φ - ψ) ^ 2 * (‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by ring
            _ = |φ - ψ| ^ 2 * (‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by rw [sq_abs]
            _ = (|φ - ψ| * ‖WithLp.toLp 2 ![x, y, z]‖) ^ 2 := by ring
    exact le_of_sq_le_sq h_sq h_nonneg_rhs
  exact h_final

theorem rotY_sub_apply_le (θ η : ℝ) (v : E3) :
    ‖toEuclideanLin (rotY θ) v - toEuclideanLin (rotY η) v‖ ≤ |θ - η| * ‖v‖ := by
  have h_sq : ‖toEuclideanLin (rotY θ) v - toEuclideanLin (rotY η) v‖ ^ 2 ≤ (|θ - η| * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq (x := toEuclideanLin (rotY θ) v - toEuclideanLin (rotY η) v)]
    have hsum : (∑ i : Fin 3, ‖((toEuclideanLin (rotY θ) v - toEuclideanLin (rotY η) v)).ofLp i‖ ^ 2)
        = (v 0 * (cos θ - cos η) + v 2 * (sin θ - sin η)) ^ 2
        + (-v 0 * (sin θ - sin η) + v 2 * (cos θ - cos η)) ^ 2 := by
      simp [rotY, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.sub_apply, Fin.sum_univ_three,
        Matrix.vecHead, Matrix.vecTail]
      ring
    rw [hsum]
    rw [mul_pow, sq_abs, EuclideanSpace.norm_sq_eq (x := v)]
    have h_norm_sq_real : ∀ x : ℝ, ‖x‖ ^ 2 = x ^ 2 := by
      intro x; simp
    simp_rw [h_norm_sq_real]
    calc
      (v 0 * (cos θ - cos η) + v 2 * (sin θ - sin η)) ^ 2
          + (-v 0 * (sin θ - sin η) + v 2 * (cos θ - cos η)) ^ 2
          = (v 0 ^ 2 + v 2 ^ 2) * ((cos θ - cos η) ^ 2 + (sin θ - sin η) ^ 2) := by
        ring
      _ = (v 0 ^ 2 + v 2 ^ 2) * (2 - 2 * cos (θ - η)) := by
        have hcos : cos θ * cos η + sin θ * sin η = cos (θ - η) := by
          rw [Real.cos_sub]
        nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq η]
      _ = (v 0 ^ 2 + v 2 ^ 2) * (4 * sin ((θ - η) / 2) ^ 2) := by
        have h : 2 - 2 * cos (θ - η) = 4 * sin ((θ - η) / 2) ^ 2 := by
          have hcos2 := Real.cos_two_mul ((θ - η) / 2)
          have h' : 2 * ((θ - η) / 2) = θ - η := by ring
          rw [h'] at hcos2
          nlinarith [Real.sin_sq_add_cos_sq ((θ - η) / 2)]
        rw [h]
      _ ≤ (v 0 ^ 2 + v 2 ^ 2) * ((θ - η) ^ 2) := by
        have hsq : sin ((θ - η) / 2) ^ 2 ≤ ((θ - η) / 2) ^ 2 := by
          simpa using Real.sin_sq_le_sq (x := (θ - η) / 2)
        nlinarith
      _ = (θ - η) ^ 2 * (v 0 ^ 2 + v 2 ^ 2) := by ring
      _ ≤ (θ - η) ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
        have h : v 0 ^ 2 + v 2 ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
          nlinarith [sq_nonneg (v 1)]
        nlinarith
      _ = (θ - η) ^ 2 * (∑ i : Fin 3, (v i) ^ 2) := by
        simp [Fin.sum_univ_three]
  have h_nonneg_left : 0 ≤ ‖toEuclideanLin (rotY θ) v - toEuclideanLin (rotY η) v‖ := norm_nonneg _
  have h_nonneg_right : 0 ≤ |θ - η| * ‖v‖ := by
    have h1 : 0 ≤ |θ - η| := abs_nonneg _
    have h2 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  nlinarith

/-- A product of norm-preserving maps preserves norms (a step of `prod_sub_apply_le`). -/
theorem norm_prod_apply_eq_norm {m : ℕ} (f : Fin m → (E3 →ₗ[ℝ] E3))
    (hf : ∀ i v, ‖f i v‖ = ‖v‖) (w : E3) :
    ‖((List.ofFn f).prod : E3 →ₗ[ℝ] E3) w‖ = ‖w‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      rw [hf 0, ih (fun i => f i.succ) (fun i v => hf i.succ v)]

/-- Telescoping: two products of norm-preserving maps, factor by factor within `δ i`. -/
theorem prod_sub_apply_le (n : ℕ) (A B : Fin n → (E3 →ₗ[ℝ] E3)) (δ : Fin n → ℝ)
    (hA : ∀ i v, ‖A i v‖ = ‖v‖) (hB : ∀ i v, ‖B i v‖ = ‖v‖)
    (hδ : ∀ i v, ‖A i v - B i v‖ ≤ δ i * ‖v‖) (v : E3) :
    ‖(List.ofFn A).prod v - (List.ofFn B).prod v‖ ≤ (∑ i, δ i) * ‖v‖ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
        Module.End.mul_apply, Module.End.mul_apply]
      set P := (List.ofFn (fun i => A i.succ)).prod with hP
      set Q := (List.ofFn (fun i => B i.succ)).prod with hQ
      have hQv : ‖Q v‖ = ‖v‖ :=
        norm_prod_apply_eq_norm (fun i => B i.succ) (fun i v => hB i.succ v) v
      have h_diff : ‖A 0 (P v) - B 0 (Q v)‖ ≤ ‖A 0 (P v - Q v)‖ + ‖A 0 (Q v) - B 0 (Q v)‖ := by
        calc
          ‖A 0 (P v) - B 0 (Q v)‖ = ‖(A 0 (P v) - A 0 (Q v)) + (A 0 (Q v) - B 0 (Q v))‖ := by abel
          _ ≤ ‖A 0 (P v) - A 0 (Q v)‖ + ‖A 0 (Q v) - B 0 (Q v)‖ := norm_add_le _ _
          _ = ‖A 0 (P v - Q v)‖ + ‖A 0 (Q v) - B 0 (Q v)‖ := by rw [map_sub]
      have h1 : ‖A 0 (P v - Q v)‖ = ‖P v - Q v‖ := hA 0 (P v - Q v)
      have h2 : ‖A 0 (Q v) - B 0 (Q v)‖ ≤ δ 0 * ‖Q v‖ := hδ 0 (Q v)
      have h_ih : ‖P v - Q v‖ ≤ (∑ i : Fin n, δ i.succ) * ‖v‖ := by
        simpa [hP, hQ] using
          ih (fun i => A i.succ) (fun i => B i.succ) (fun i => δ i.succ)
            (fun i v => hA i.succ v) (fun i v => hB i.succ v) (fun i v => hδ i.succ v)
      calc
        ‖A 0 (P v) - B 0 (Q v)‖ ≤ ‖A 0 (P v - Q v)‖ + ‖A 0 (Q v) - B 0 (Q v)‖ := h_diff
        _ = ‖P v - Q v‖ + ‖A 0 (Q v) - B 0 (Q v)‖ := by rw [h1]
        _ ≤ ‖P v - Q v‖ + (δ 0 * ‖Q v‖) := by gcongr
        _ = ‖P v - Q v‖ + (δ 0 * ‖v‖) := by rw [hQv]
        _ ≤ ((∑ i : Fin n, δ i.succ) * ‖v‖) + (δ 0 * ‖v‖) := by gcongr
        _ = ((∑ i : Fin n, δ i.succ) + δ 0) * ‖v‖ := by ring
        _ = (∑ i : Fin (n + 1), δ i) * ‖v‖ := by
          rw [add_comm, Fin.sum_univ_succ]
        _ = (∑ i, δ i) * ‖v‖ := by simp

end Tammes15
