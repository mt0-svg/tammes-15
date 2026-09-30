import Tammes15.Geom.Wheel
import Tammes15.Geom.Crofton
import Tammes15.Draw.FaceWalk
import Tammes15.Fans.Corners
import Tammes15.Rattlers.Hex
import Tammes15.Trigrows.Margins

/-!
# Relation (T8): the wheel of a free point in its hexagon

`wheel_of_realisation_proof` has the statement of `wheel_of_realisation`
(`Tammes15.Hyps.Interfaces`). The face of the base dart of the `m`-th hexagon is a convex walk with
six sides `d` (`FaceWalk.walk_of_realisation`), hence a polygon in cone form (`isCPoly_of_walk`),
and the free point `p` lies inside it. `wheelRel_of_walk` gives the five parts of `WheelRel`:

* `d ≤ r j` is the separation, and `r j ≤ 3 d` is `sdist_le_half_perim`: `p` lies in the cone of
  a fan triangle `A₀ A_j A_{j+1}` (`IsCPoly.cone_of_inClosed`), so the arc from `A₀` through `p`
  meets the side `A_j A_{j+1}` at a point `q` farther from `A₀` (`arc_add`), and the two ways
  round the boundary from `A₀` to `q` have lengths summing to the perimeter;
* the cosines `η` lie in `[-1, 1]` (`eta_mem_Icc`);
* the six angles at `p` sum to `2π` (`wheel_sum`, `angle_tdir_eq_gam`);
* each corner splits at the direction of `p` (`T8_corner`, with the cone of `FaceWalk.exists_cone`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.Geom

/-- A convex walk is a polygon in cone form. -/
theorem isCPoly_of_walk {m : ℕ} {d : ℝ} {X : ℕ → E3} (hW : FaceWalk.Walk m d X) :
    IsCPoly m X := by
  refine ⟨hW.three, hW.unit, hW.periodic, ?_⟩
  intro i k hk2 hkm
  have hk_mod_eq : k % m = k := Nat.mod_eq_of_lt hkm
  have hk_mod_ne_zero : k % m ≠ 0 := by
    rw [hk_mod_eq]
    omega
  have hk_mod_ne_one : k % m ≠ 1 := by
    rw [hk_mod_eq]
    omega
  exact hW.support i k hk_mod_ne_zero hk_mod_ne_one

/-- Every vertex lies in the closed face. -/
theorem IsCPoly.inClosed_vertex {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (j : ℕ) :
    InClosed A (A j) := by
  intro i
  by_cases h0 : j % m = i % m
  · have hAj : A j = A i := by
      calc
        A j = A (j % m) := hA.mod j
        _ = A (i % m) := by rw [h0]
        _ = A i := (hA.mod i).symm
    rw [hAj]
    have hzero : ⟪cross (A i) (A (i + 1)), A i⟫ = 0 := by
      simp [PiLp.inner_apply, cross, cross_apply, Fin.sum_univ_three]
      ring
    rw [hzero]
  · by_cases h1 : j % m = (i + 1) % m
    · have hAj : A j = A (i + 1) := by
        calc
          A j = A (j % m) := hA.mod j
          _ = A ((i + 1) % m) := by rw [h1]
          _ = A (i + 1) := (hA.mod (i + 1)).symm
      rw [hAj]
      rw [inner_cross_right_zero]
    · have hpos := hA.support_of_ne i j h0 h1
      exact le_of_lt hpos

theorem Inside.inClosed {A : ℕ → E3} {x : E3} (h : Inside A x) : InClosed A x :=
  fun i => (h i).le

/-- A point of the closed face is not antipodal to the first vertex. -/
theorem IsCPoly.ne_neg_of_inClosed {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (q : E3)
    (hq : InClosed A q) : q ≠ -A 0 := by
  intro h_eq
  have hq1 : 0 ≤ ⟪cross (A 1) (A (1 + 1)), q⟫ := hq 1
  have hpos_support : 2 ≤ m - 1 := by
    have hm : 3 ≤ m := hA.three
    omega
  have hlt_support : m - 1 < m := by
    have hm : 3 ≤ m := hA.three
    omega
  have hpos_inner : 0 < ⟪cross (A 1) (A (1 + 1)), A (1 + (m - 1))⟫ :=
    hA.support 1 (m - 1) hpos_support hlt_support
  have h_eq_idx : 1 + (m - 1) = 0 + m := by omega
  have h_periodic : A (0 + m) = A 0 := hA.periodic 0
  have h_idx_eq : A (1 + (m - 1)) = A 0 := by
    calc
      A (1 + (m - 1)) = A (0 + m) := by rw [h_eq_idx]
      _ = A 0 := h_periodic
  rw [h_idx_eq] at hpos_inner
  rw [h_eq, inner_neg_right] at hq1
  linarith

/-- Along a chain of sides of length `d`, the distance grows by at most `d` per side. -/
theorem sdist_chain {A : ℕ → E3} (hunit : ∀ i, ‖A i‖ = 1) (d : ℝ)
    (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (i k : ℕ) : sdist (A i) (A (i + k)) ≤ k * d := by
  induction' k with k ih
  · -- k = 0
    have h0 : sdist (A i) (A i) = 0 := by
      rw [sdist]
      have hinner : ⟪A i, A i⟫ = 1 := by
        calc
          ⟪A i, A i⟫ = ‖A i‖ ^ 2 := by simp
          _ = 1 ^ 2 := by rw [hunit i]
          _ = 1 := by norm_num
      rw [hinner, Real.arccos_one]
    simpa [add_zero] using h0.le
  · -- k → k + 1
    have h_tri := sdist_triangle (A i) (A (i + k)) (A (i + k + 1)) (hunit i) (hunit (i + k)) (hunit (i + k + 1))
    have h_side_eq : sdist (A (i + k)) (A (i + k + 1)) = d := hside (i + k)
    have h_add : i + (k + 1) = i + k + 1 := by omega
    rw [h_add]
    have h_sum : sdist (A i) (A (i + k)) + sdist (A (i + k)) (A (i + k + 1)) ≤ k * d + d :=
      add_le_add ih (by rw [h_side_eq])
    have h_eq : k * d + d = ((k + 1 : ℕ) : ℝ) * d := by
      push_cast
      ring
    rw [h_eq] at h_sum
    exact le_trans h_tri h_sum

/-- A unit vector in the cone of two non-antipodal unit vectors lies on the arc between them. -/
theorem arc_add (u w p : E3) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hp : ‖p‖ = 1) (_hne : u ≠ -w)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hpuw : p = a • u + b • w) :
    sdist u p + sdist p w = sdist u w := by
  have hbd : ∀ x y : E3, ‖x‖ = 1 → ‖y‖ = 1 → -1 ≤ ⟪x, y⟫ ∧ ⟪x, y⟫ ≤ 1 := by
    intro x y hx hy
    have := abs_real_inner_le_norm x y
    rw [hx, hy, mul_one] at this
    exact abs_le.mp this
  obtain ⟨hc0, hc1⟩ := hbd u w hu hw
  obtain ⟨hx0, hx1⟩ := hbd u p hu hp
  obtain ⟨hy0, hy1⟩ := hbd p w hp hw
  set c := ⟪u, w⟫ with hc
  have hx : ⟪u, p⟫ = a + b * c := by
    rw [hpuw, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu]; ring
  have hy : ⟪p, w⟫ = a * c + b := by
    rw [hpuw, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hw]; ring
  have hN : a ^ 2 + b ^ 2 + 2 * a * b * c = 1 := by
    have h2 : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
    have e : ⟪p, p⟫ = a * ⟪u, p⟫ + b * ⟪p, w⟫ := by
      nth_rewrite 1 [hpuw]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm p w]
    rw [e, hx, hy] at h2
    linear_combination h2
  rw [hx] at hx0 hx1
  rw [hy] at hy0 hy1
  unfold sdist
  rw [hx, hy]
  have hs : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hsA : sin (arccos (a + b * c)) = b * √(1 - c ^ 2) := by
    rw [sin_arccos, show 1 - (a + b * c) ^ 2 = b ^ 2 * (1 - c ^ 2) by
      linear_combination (-1 : ℝ) * hN, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]
  have hsB : sin (arccos (a * c + b)) = a * √(1 - c ^ 2) := by
    rw [sin_arccos, show 1 - (a * c + b) ^ 2 = a ^ 2 * (1 - c ^ 2) by
      linear_combination (-1 : ℝ) * hN, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  have hle : arccos (a + b * c) + arccos (a * c + b) ≤ π := by
    have h1 : arccos (a + b * c) ≤ arccos (-(a * c + b)) :=
      arccos_le_arccos (by nlinarith)
    rw [arccos_neg] at h1
    linarith
  apply injOn_cos ⟨add_nonneg (arccos_nonneg _) (arccos_nonneg _), hle⟩
    ⟨arccos_nonneg _, arccos_le_pi _⟩
  rw [cos_add, hsA, hsB, cos_arccos hx0 hx1, cos_arccos hy0 hy1, cos_arccos hc0 hc1]
  have hsq := Real.sq_sqrt hs
  linear_combination (-(a * b)) * hsq + c * hN

/-- A point of the closed face of a polygon with sides `d` is within half the perimeter of the
first vertex. -/
theorem sdist_le_half_perim {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (d : ℝ)
    (hside : ∀ i, sdist (A i) (A (i + 1)) = d) (p : E3) (hp : ‖p‖ = 1) (hin : InClosed A p) :
    2 * sdist (A 0) p ≤ m * d := by
  have hm3 := hA.three
  have hd0 : 0 ≤ d := by rw [← hside 0]; exact (sdist_mem_Icc _ _).1
  obtain ⟨j, a, b, c, hj1, hjm, ha, hb, hc, hpe⟩ := hA.cone_of_inClosed p hin
  set s := b • A j + c • A (j + 1) with hs_def
  by_cases hs : s = 0
  · have hpa : p = a • A 0 := by rw [hpe, add_assoc, ← hs_def, hs, add_zero]
    have ha1 : a = 1 := by
      have h := congrArg norm hpa
      rw [hp, norm_smul, hA.unit 0, mul_one, Real.norm_of_nonneg ha] at h
      exact h.symm
    rw [hpa, ha1, one_smul]
    have h0 : sdist (A 0) (A 0) = 0 := by
      unfold sdist
      rw [real_inner_self_eq_norm_sq, hA.unit 0, one_pow, arccos_one]
    rw [h0, mul_zero]
    positivity
  set μ := ‖s‖ with hμ_def
  have hμ : 0 < μ := norm_pos_iff.mpr hs
  set q := μ⁻¹ • s with hq_def
  have hq1 : ‖q‖ = 1 := by
    rw [hq_def, norm_smul, norm_inv, Real.norm_of_nonneg hμ.le, ← hμ_def, inv_mul_cancel₀ hμ.ne']
  have hqc : q = (b / μ) • A j + (c / μ) • A (j + 1) := by
    rw [hq_def, hs_def, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  have hqin : InClosed A q := by
    intro i
    rw [hqc, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 := hA.inClosed_vertex j i
    have h2 := hA.inClosed_vertex (j + 1) i
    have hbμ : 0 ≤ b / μ := div_nonneg hb hμ.le
    have hcμ : 0 ≤ c / μ := div_nonneg hc hμ.le
    positivity
  have hpq : p = a • A 0 + μ • q := by
    rw [hq_def, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, hpe, add_assoc]
  have hne0 : A 0 ≠ -q := by
    intro h
    apply hA.ne_neg_of_inClosed q hqin
    rw [h, neg_neg]
  have harc1 := arc_add (A 0) q p (hA.unit 0) hq1 hp hne0 a μ ha hμ.le hpq
  have hjj : A j ≠ -A (j + 1) := by
    intro h
    have hB := (hA.shift j).ne_neg_of_inClosed (A (j + 1))
      (by simpa using (hA.shift j).inClosed_vertex 1)
    apply hB
    simp [h]
  have harc2 := arc_add (A j) (A (j + 1)) q (hA.unit j) (hA.unit (j + 1)) hq1 hjj (b / μ) (c / μ)
    (div_nonneg hb hμ.le) (div_nonneg hc hμ.le) hqc
  rw [hside j] at harc2
  have ht1 := sdist_triangle (A 0) (A j) q (hA.unit 0) (hA.unit j) hq1
  have ht2 := sdist_triangle (A 0) (A (j + 1)) q (hA.unit 0) (hA.unit (j + 1)) hq1
  have hc1 : sdist (A 0) (A j) ≤ j * d := by simpa using sdist_chain hA.unit d hside 0 j
  have hc2 : sdist (A 0) (A (j + 1)) ≤ ((m - (j + 1) : ℕ) : ℝ) * d := by
    have h := sdist_chain hA.unit d hside (j + 1) (m - (j + 1))
    rw [show j + 1 + (m - (j + 1)) = 0 + m by omega, hA.periodic 0] at h
    rwa [sdist_comm]
  have hcast : ((m - (j + 1) : ℕ) : ℝ) = (m : ℝ) - j - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hc2
  have hpA := (sdist_mem_Icc p q).1
  rw [sdist_comm (A (j + 1)) q] at ht2
  nlinarith

/-- Index of `j + 1` in `Fin 6` on a walk of period six. -/
theorem walk_fin_succ {d : ℝ} {X : ℕ → E3} (hW : FaceWalk.Walk 6 d X) (j : Fin 6) :
    X ((j + 1 : Fin 6) : ℕ) = X (j + 1) := by
  fin_cases j <;> simp [hW.periodic 0]

/-- Index of `j - 1` in `Fin 6` on a walk of period six. -/
theorem walk_fin_pred {d : ℝ} {X : ℕ → E3} (hW : FaceWalk.Walk 6 d X) (j : Fin 6) :
    X ((j - 1 : Fin 6) : ℕ) = X (j + 5) := by
  have hper : Function.Periodic X 6 := hW.periodic
  have hmod_eq : ∀ j : Fin 6, ((j - 1 : Fin 6) : ℕ) % 6 = ((j : ℕ) + 5) % 6 := by decide
  calc
    X ((j - 1 : Fin 6) : ℕ) = X (((j - 1 : Fin 6) : ℕ) % 6) := by
      symm; exact hper.map_mod_nat _
    _ = X (((j : ℕ) + 5) % 6) := by rw [hmod_eq j]
    _ = X ((j : ℕ) + 5) := hper.map_mod_nat _

/-- The relation (T8) for a point inside a convex walk with six sides `d`. -/
theorem wheelRel_of_walk {d : ℝ} (hd : dlo ≤ d ∧ d ≤ dhi) {X : ℕ → E3}
    (hW : FaceWalk.Walk 6 d X) (p : E3) (hp : ‖p‖ = 1) (hin : Inside X p)
    (hsep : ∀ j, d ≤ sdist p (X j)) :
    WheelRel d (fun j : Fin 6 => FaceWalk.wangle 6 X j) (fun j : Fin 6 => sdist p (X j)) := by
  have hA := isCPoly_of_walk hW
  have hunit := hW.unit
  have hdpos : 0 < d := by linarith [pi_div_four_lt_dlo, pi_pos, hd.1]
  have h3d : 3 * d < π := by linarith [three_dhi_lt_pi, hd.2]
  have hdpi : d < π := by linarith
  have hX6 : ∀ j : ℕ, X (j + 5 + 1) = X j := fun j => hW.periodic j
  have hle : ∀ j : ℕ, sdist p (X j) ≤ 3 * d := by
    intro j
    have h := sdist_le_half_perim (hA.shift j) d
      (fun i => by simpa [add_assoc] using hW.side (j + i)) p hp (hin.shift j).inClosed
    rw [sdist_comm]
    simp only [add_zero] at h
    push_cast at h
    linarith
  have hr : ∀ j : ℕ, 0 < sdist p (X j) ∧ sdist p (X j) < π :=
    fun j => ⟨by linarith [hsep j], by linarith [hle j]⟩
  have hr' : ∀ j : ℕ, 0 < sdist (X j) p ∧ sdist (X j) p < π := fun j => by
    rw [sdist_comm]; exact hr j
  have hside : ∀ j, sdist (X j) (X (j + 1)) = d := hW.side
  have hside' : ∀ j, sdist (X j) (X (j + 5)) = d := fun j => by
    rw [sdist_comm, ← hW.side (j + 5), hX6]
  have hsd : ∀ j, 0 < sdist (X j) (X (j + 1)) ∧ sdist (X j) (X (j + 1)) < π := fun j => by
    rw [hside]; exact ⟨hdpos, hdpi⟩
  have hsd' : ∀ j, 0 < sdist (X j) (X (j + 5)) ∧ sdist (X j) (X (j + 5)) < π := fun j => by
    rw [hside']; exact ⟨hdpos, hdpi⟩
  refine ⟨fun j => ⟨hsep j, hle j⟩, fun j => ?_, ?_, fun j => ⟨?_, ?_⟩, fun j => ?_⟩
  · simp only [walk_fin_succ hW]
    have h := eta_mem_Icc p (X j) (X (j + 1)) hp (hunit _) (hunit _) (hr j) (hr (j + 1))
    rw [hside] at h
    exact Set.mem_Icc.mpr h
  · have hw := wheel_sum hA p hp hin
    rw [← Fin.sum_univ_eq_sum_range (fun i => angle (tdir p (X i)) (tdir p (X (i + 1)))) 6] at hw
    rw [← hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [walk_fin_succ hW]
    rw [angle_tdir_eq_gam p (X j) (X (j + 1)) hp (hunit _) (hunit _) (hr j) (hr (j + 1)), hside]
  · simp only [walk_fin_succ hW]
    have h := eta_mem_Icc (X j) p (X (j + 1)) (hunit _) hp (hunit _) (hr' j) (hsd j)
    rw [hside, sdist_comm (X j) p] at h
    exact Set.mem_Icc.mpr h
  · simp only [walk_fin_pred hW]
    have h := eta_mem_Icc (X j) p (X (j + 5)) (hunit _) hp (hunit _) (hr' j) (hsd' j)
    rw [hside', sdist_comm (X j) p] at h
    exact Set.mem_Icc.mpr h
  · simp only [walk_fin_succ hW, walk_fin_pred hW]
    unfold FaceWalk.wangle
    rw [show (j : ℕ) + 6 - 1 = j + 5 by omega]
    have hq : 0 < ⟪cross (X j) (X (j + 1)), X (j + 5)⟫ := hA.support j 5 (by norm_num) (by norm_num)
    have hqw : 0 < ⟪cross (X (j + 5)) (X j), p⟫ := by
      have h := hin (j + 5)
      rwa [hX6] at h
    obtain ⟨l, l', hl, hl', hcone⟩ :=
      FaceWalk.exists_cone (X j) (X (j + 1)) (X (j + 5)) p (hunit _) hq (hin j) hqw
    rw [T8_corner d ⟨hdpos, hdpi⟩ (X j) (X (j + 1)) (X (j + 5)) p (hunit _) (hunit _) (hunit _) hp
      (hside j) (hside' j) (hr' j) l l' hl.le hl'.le hcone,
      sdist_comm (X (j + 1)) p, sdist_comm (X j) p, FaceWalk.gam_comm (sdist p (X (j + 1))) d]
section Realisation

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

/-- The free point of a hexagon is inside its face walk. -/
theorem inside_of_realisation (hx : Realisation P H d x) (m : Fin k) :
    Inside (fun i => x (.inl (FaceWalk.fv P (H.base m) i))) (x (.inr m)) := by
  intro j
  have h := hx.inside m j
  rwa [FaceWalk.face_pow_snd] at h

/-- (T8), with the statement of `wheel_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem wheel_of_realisation_proof (hP : InClass P) (hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (m : Fin k) :
    WheelRel d (fun j => (assignOf P H d x).fc (H.base m) j) ((assignOf P H d x).r m) := by
  have h6 : fsize P (H.base m) = 6 := H.hex m
  have hW : FaceWalk.Walk 6 d (fun i => x (.inl (FaceWalk.fv P (H.base m) i))) :=
    h6 ▸ FaceWalk.walk_of_realisation hP hx (H.base m)
  have hfc : (fun j : Fin 6 => (assignOf P H d x).fc (H.base m) j) =
      fun j : Fin 6 => FaceWalk.wangle 6 (fun i => x (.inl (FaceWalk.fv P (H.base m) i))) j := by
    funext j
    rw [FaceWalk.fc_eq_wangle hP hx, h6]
  rw [hfc]
  exact wheelRel_of_walk hd hW (x (.inr m)) (hx.unit _) (inside_of_realisation hx m)
    (fun j => hx.sep _ _ (by simp))

end Realisation

end Tammes15.Geom
