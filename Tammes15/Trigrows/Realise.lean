import Tammes15.Draw.FaceWalk

/-!
# (T3), (T4), (T7) for a realisation

The interfaces `tri_of_realisation`, `rhombus_of_realisation` and `hexDiag_of_realisation` of
`Tammes15.Hyps.Interfaces`, stated word for word as `tri_of_realisation_proof`,
`rhombus_of_realisation_proof` and `hexDiag_of_realisation_proof` (the unused range hypothesis is
named `_hd`); the interface file closes each interface with its theorem. A face of the realisation is a convex
walk (`FaceWalk.walk_of_realisation`) whose angles are the corners of `assignOf`
(`FaceWalk.fc_eq_wangle`). The relations are proved for convex walks, from the cores of Trigrows:
`equilateral_angle` (T3); `rhombus_opposite_angle`, the split of the corner at `X 1` by the
diagonal to `X 3`, `T1_isosceles_angle` and `rho_eq_two_bangle` (T4); the split of a corner by the
diagonal to the opposite side, `T1_isosceles_base`, `slc_tangent` in the triangle of the diagonal
`X 2`, `X 5` and `T7_iff` (T7).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

namespace FaceWalk.Walk

variable {d : ℝ} {X : ℕ → E3}

/-- (T3) for a triangular walk. -/
theorem tri (hW : Walk 3 d X) : wangle 3 X 0 = alpha d := by
  unfold wangle
  have hd' : 0 < d ∧ d < π := by
    rcases hW.d_mem with ⟨hd_pos, hd_lt⟩
    have hpi : 0 < π := Real.pi_pos
    exact ⟨hd_pos, hd_lt.trans (by linarith)⟩
  apply Tammes15.equilateral_angle d hd' (X 0) (X 1) (X 2) (hW.unit 0) (hW.unit 1) (hW.unit 2)
  · exact hW.side 0
  · simpa using hW.side_pred 0
  · simpa using hW.side 1

/-- (T4) for a quadrilateral walk: opposite angles equal, `y = ρ_d(x)`. -/
theorem rhombus (hW : Walk 4 d X) :
    wangle 4 X 2 = wangle 4 X 0 ∧ wangle 4 X 1 = rho d (wangle 4 X 0) := by
  have hperiod0 : X 4 = X 0 := by simpa using hW.periodic 0
  have hperiod1 : X 5 = X 1 := by simpa using hW.periodic 1
  have hd_pi : 0 < d ∧ d < π := by
    rcases hW.d_mem with ⟨hdpos, hdlt⟩
    exact ⟨hdpos, by linarith⟩
  have halpha_pos : 0 < alpha d := by
    have hbounds := alpha_bounds d hW.d_mem
    rcases hbounds with ⟨hlo, hhi⟩
    linarith
  have h2mod0 : (2 : ℕ) % 4 ≠ 0 := by norm_num
  have h2mod1 : (2 : ℕ) % 4 ≠ 1 := by norm_num
  have h2mod3 : (2 : ℕ) % 4 ≠ 3 := by norm_num
  -- Part 1: wangle 4 X 2 = wangle 4 X 0
  have h_rhombus : angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) = angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := by
    apply rhombus_opposite_angle d hd_pi (X 0) (X 1) (X 2) (X 3)
    · exact hW.unit 0
    · exact hW.unit 1
    · exact hW.unit 2
    · exact hW.unit 3
    · exact hW.side 0
    · simpa using hW.side_pred 0
    · simpa [hperiod1] using hW.side_pred 2
    · exact hW.side 2
  have h_wangle0 : wangle 4 X 0 = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) := by
    simp [wangle]
  have h_wangle2 : wangle 4 X 2 = angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := by
    simp [wangle, hperiod1]
  have h_part1 : wangle 4 X 2 = wangle 4 X 0 := by
    calc
      wangle 4 X 2 = angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := h_wangle2
      _ = angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := by rw [InnerProductGeometry.angle_comm]
      _ = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) := by rw [← h_rhombus]
      _ = wangle 4 X 0 := by rw [h_wangle0]
  -- Part 2: wangle 4 X 1 = rho d (wangle 4 X 0)
  have h_angle_split : wangle 4 X 1 = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 3)) + angle (tdir (X 1) (X 3)) (tdir (X 1) (X 0)) := by
    have h := hW.angle_split 1 2 h2mod0 h2mod1 h2mod3
    simpa [hperiod0, wangle] using h.symm
  have h_corner0_pos : 0 < angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) := by
    have hcorner := hW.corner 0
    rcases hcorner with ⟨hle, hlt⟩
    linarith
  have h_corner2_pos : 0 < angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := by
    have hcorner := hW.corner 2
    rcases hcorner with ⟨hle, hlt⟩
    have hcorner' : alpha d ≤ angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := by
      simpa [hperiod1] using hle
    have hpos : 0 < angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := by linarith
    rw [InnerProductGeometry.angle_comm]
    exact hpos
  have h_apex2 : angle (tdir (X 1) (X 2)) (tdir (X 1) (X 3)) = bangle d (angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3))) := by
    apply T1_isosceles_angle d hW.d_mem (X 2) (X 1) (X 3)
    · exact hW.unit 2
    · exact hW.unit 1
    · exact hW.unit 3
    · simpa [hperiod1] using hW.side_pred 2
    · exact hW.side 2
    · exact h_corner2_pos
  have h_apex0 : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 3)) = bangle d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3))) := by
    apply T1_isosceles_angle d hW.d_mem (X 0) (X 1) (X 3)
    · exact hW.unit 0
    · exact hW.unit 1
    · exact hW.unit 3
    · exact hW.side 0
    · simpa using hW.side_pred 0
    · exact h_corner0_pos
  have h_eq_angles : angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) := by
    calc
      angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) = angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := by rw [InnerProductGeometry.angle_comm]
      _ = wangle 4 X 2 := by rw [h_wangle2]
      _ = wangle 4 X 0 := h_part1
      _ = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3)) := by rw [h_wangle0]
  have h_angle1 : wangle 4 X 1 = 2 * bangle d (wangle 4 X 0) := by
    calc
      wangle 4 X 1 = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 3)) + angle (tdir (X 1) (X 3)) (tdir (X 1) (X 0)) := h_angle_split
      _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 3)) + angle (tdir (X 1) (X 0)) (tdir (X 1) (X 3)) := by rw [InnerProductGeometry.angle_comm (tdir (X 1) (X 3)) (tdir (X 1) (X 0))]
      _ = bangle d (angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3))) + bangle d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3))) := by rw [h_apex2, h_apex0]
      _ = bangle d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3))) + bangle d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 3))) := by rw [h_eq_angles]
      _ = 2 * bangle d (wangle 4 X 0) := by rw [h_wangle0]; ring
  have h_wangle0_range : 0 < wangle 4 X 0 ∧ wangle 4 X 0 < π := by
    rw [h_wangle0]
    have hcorner := hW.corner 0
    rcases hcorner with ⟨hle, hlt⟩
    exact ⟨by linarith, hlt⟩
  have h_rho : rho d (wangle 4 X 0) = 2 * bangle d (wangle 4 X 0) :=
    rho_eq_two_bangle d (wangle 4 X 0) hW.d_mem h_wangle0_range
  have h_part2 : wangle 4 X 1 = rho d (wangle 4 X 0) := by
    rw [h_angle1, h_rho]
  exact And.intro h_part1 h_part2

/-- (T7) at `X 1` for a hexagonal walk whose diagonal `X 2`, `X 5` is at least `d`. -/
theorem hexDiag_left (hW : Walk 6 d X) (hsep : d ≤ sdist (X 2) (X 5)) :
    longDiag d (wangle 6 X 0) ≤ wangle 6 X 1 := by
  -- u0 = wangle 6 X 0, u1 = wangle 6 X 1
  have hd_pos : 0 < d := hW.d_mem.1
  have hd_lt_pi_div_two : d < π / 2 := hW.d_mem.2
  -- Step 1: angle_split at vertex 1 with n=4
  have h4mod6_ne_0 : 4 % 6 ≠ 0 := by norm_num
  have h4mod6_ne_1 : 4 % 6 ≠ 1 := by norm_num
  have h4mod6_ne_5 : 4 % 6 ≠ 5 := by norm_num
  have h_periodic_0 : X 6 = X 0 := by simpa using hW.periodic 0
  have h_angle_split := hW.angle_split 1 4 h4mod6_ne_0 h4mod6_ne_1 h4mod6_ne_5
  -- h_angle_split : angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 6)) = wangle 6 X 1
  have h_angle_split' : angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) = wangle 6 X 1 := by
    simpa [h_periodic_0] using h_angle_split
  -- Step 2: angle (tdir X1 X5) (tdir X1 X0) = bangle d (wangle 6 X 0)
  have h_wangle0 : wangle 6 X 0 = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)) := by
    simp [wangle]
  have h_corner0_pos : 0 < wangle 6 X 0 := by
    rw [h_wangle0]
    have hcorner := hW.corner 0
    have h_alpha_pos : 0 < alpha d := by
      have h_alpha_bounds := alpha_bounds d hW.d_mem
      linarith
    linarith
  have h_T1_angle := T1_isosceles_angle d hW.d_mem (X 0) (X 1) (X 5)
    (hW.unit 0) (hW.unit 1) (hW.unit 5) (hW.side 0) (hW.side_pred 0) h_corner0_pos
  -- h_T1_angle : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 5)) = bangle d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)))
  have h_angle_comm : angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) = angle (tdir (X 1) (X 0)) (tdir (X 1) (X 5)) :=
    InnerProductGeometry.angle_comm _ _
  have h_step2 : angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) = bangle d (wangle 6 X 0) := by
    rw [h_angle_comm, h_T1_angle, h_wangle0]
  -- Step 3: e := sdist X1 X5 = ebase d (wangle 6 X 0)
  have h_T1_base := T1_isosceles_base d hW.d_mem (X 0) (X 1) (X 5)
    (hW.unit 0) (hW.unit 1) (hW.unit 5) (hW.side 0) (hW.side_pred 0)
  -- h_T1_base : sdist (X 1) (X 5) = ebase d (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)))
  have h_e : sdist (X 1) (X 5) = ebase d (wangle 6 X 0) := by
    rw [h_T1_base, h_wangle0]
  have h_sdist_pos : 0 < sdist (X 1) (X 5) := by
    have h_mem := hW.sdist_mem 1 4 (by norm_num : 4 % 6 ≠ 0)
    -- h_mem : 0 < sdist (X 1) (X (1+4)) ∧ sdist (X 1) (X (1+4)) < π
    simpa [show X (1 + 4) = X 5 by norm_num] using h_mem.1
  have h_sdist_lt_pi : sdist (X 1) (X 5) < π := by
    have h_mem := hW.sdist_mem 1 4 (by norm_num : 4 % 6 ≠ 0)
    simpa [show X (1 + 4) = X 5 by norm_num] using h_mem.2
  -- Step 4: θ := angle (tdir X1 X5) (tdir X1 X2)
  set θ := angle (tdir (X 1) (X 5)) (tdir (X 1) (X 2)) with hθ_def
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθ_le_pi : θ ≤ π := InnerProductGeometry.angle_le_pi _ _
  -- slc_tangent at X1 for X5, X2
  have h_slc := slc_tangent (X 1) (X 5) (X 2) (hW.unit 1) (hW.unit 5) (hW.unit 2)
  -- h_slc : cos (sdist (X 5) (X 2)) = cos (sdist (X 1) (X 5)) * cos (sdist (X 1) (X 2)) + sin (sdist (X 1) (X 5)) * sin (sdist (X 1) (X 2)) * cos (angle (tdir (X 1) (X 5)) (tdir (X 1) (X 2)))
  have h_sdist_X1X2 : sdist (X 1) (X 2) = d := hW.side 1
  have h_sdist_X5X2_le_pi : sdist (X 5) (X 2) ≤ π := by
    have h_mem := hW.sdist_mem 2 3 (by norm_num : 3 % 6 ≠ 0)
    have h_eq : X (2 + 3) = X 5 := by norm_num
    simpa [h_eq, sdist_comm] using h_mem.2.le
  have h_sdist_X5X2_ge_d : d ≤ sdist (X 5) (X 2) := by
    simpa [sdist_comm] using hsep
  have h_cos_ineq : cos (sdist (X 5) (X 2)) ≤ cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h_sdist_X5X2_le_pi h_sdist_X5X2_ge_d
  -- Rewrite slc using the known distances
  have h_slc' : cos (sdist (X 5) (X 2)) = cos (sdist (X 1) (X 5)) * cos d + sin (sdist (X 1) (X 5)) * sin d * cos θ := by
    rw [h_slc, h_sdist_X1X2, hθ_def]
  -- From h_slc' and h_cos_ineq: cos e * cos d + sin e * sin d * cos θ ≤ cos d
  have h_cos_ineq2 : cos (sdist (X 1) (X 5)) * cos d + sin (sdist (X 1) (X 5)) * sin d * cos θ ≤ cos d := by
    linarith
  have h_e_pos : 0 < sdist (X 1) (X 5) := h_sdist_pos
  have h_e_lt_pi : sdist (X 1) (X 5) < π := h_sdist_lt_pi
  have h_T7 := (T7_iff d (sdist (X 1) (X 5)) θ hW.d_mem ⟨h_e_pos, h_e_lt_pi⟩ ⟨hθ_nonneg, hθ_le_pi⟩).mp h_cos_ineq2
  -- h_T7 : arccos (min 1 (cot d * tan (sdist (X 1) (X 5) / 2))) ≤ θ
  -- Step 5: chain the inequalities
  have h_longDiag_eq : longDiag d (wangle 6 X 0) = bangle d (wangle 6 X 0) + arccos (min 1 (cot d * tan (sdist (X 1) (X 5) / 2))) := by
    rw [longDiag, h_e]
  have h_mid : bangle d (wangle 6 X 0) + arccos (min 1 (cot d * tan (sdist (X 1) (X 5) / 2))) ≤
      angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) := by
    calc
      bangle d (wangle 6 X 0) + arccos (min 1 (cot d * tan (sdist (X 1) (X 5) / 2))) ≤
          bangle d (wangle 6 X 0) + θ := by gcongr
      _ = angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) + θ := by rw [h_step2]
      _ = angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 2)) := by rw [hθ_def]
      _ = angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) + angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) := by rw [InnerProductGeometry.angle_comm (tdir (X 1) (X 5)) (tdir (X 1) (X 2))]
      _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) := by rw [add_comm]
  have h_target : angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) + angle (tdir (X 1) (X 5)) (tdir (X 1) (X 0)) = wangle 6 X 1 := by
    rw [h_angle_split']
  -- Combine
  linarith

/-- (T7) at `X 0` for a hexagonal walk whose diagonal `X 2`, `X 5` is at least `d`. -/
theorem hexDiag_right (hW : Walk 6 d X) (hsep : d ≤ sdist (X 2) (X 5)) :
    longDiag d (wangle 6 X 1) ≤ wangle 6 X 0 := by
  set u0 := wangle 6 X 0
  set u1 := wangle 6 X 1
  have hd := hW.d_mem
  rcases hd with ⟨hd_pos, hd_lt⟩
  have hcos_pos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd_lt⟩
  -- u1 > 0
  have hu1_pos : 0 < u1 := by
    have h_alpha_pos : 0 < Tammes15.alpha d := by
      rw [Tammes15.alpha]
      refine (Real.arccos_pos.mpr ?_)
      have hdiv : cos d / (1 + cos d) < 1 := by
        refine (div_lt_one ?_).mpr ?_
        · linarith
        · linarith
      exact hdiv
    have h_alpha_le_u1 : Tammes15.alpha d ≤ u1 := (hW.corner 1).1
    linarith
  have hX6 : X 6 = X 0 := by
    simpa using hW.periodic 0
  -- angle_split at i=0, n=2
  have h_angle_split : angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)) + angle (tdir (X 0) (X 2)) (tdir (X 0) (X 5)) = u0 := by
    have h0 : 2 % 6 ≠ 0 := by norm_num
    have h1 : 2 % 6 ≠ 1 := by norm_num
    have h2 : 2 % 6 ≠ 6 - 1 := by norm_num
    have hsplit := hW.angle_split 0 2 h0 h1 h2
    simpa [u0, wangle, show (0:ℕ)+1 = 1 by norm_num, show (0:ℕ)+2 = 2 by norm_num,
      show (0:ℕ)+6-1 = 5 by norm_num] using hsplit
  -- T1_isosceles_angle at A=X1, B=X0, C=X2
  have h_t1_angle : angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)) = Tammes15.bangle d u1 := by
    have hAB : sdist (X 1) (X 0) = d := by
      rw [Tammes15.sdist_comm, hW.side 0]
    have hAC : sdist (X 1) (X 2) = d := hW.side 1
    have h_angle_pos : 0 < angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) := by
      calc
        0 < u1 := hu1_pos
        _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X (1+6-1))) := by
          simp [u1, wangle]
        _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 6)) := by norm_num
        _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by rw [hX6]
        _ = angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) := by rw [InnerProductGeometry.angle_comm]
    have h_t1 := Tammes15.T1_isosceles_angle d ⟨hd_pos, hd_lt⟩ (X 1) (X 0) (X 2)
      (hW.unit 1) (hW.unit 0) (hW.unit 2) hAB hAC h_angle_pos
    simpa [u1, wangle, hX6, show (1:ℕ)+1 = 2 by norm_num, show (1:ℕ)+6-1 = 6 by norm_num,
      InnerProductGeometry.angle_comm] using h_t1
  -- T1_isosceles_base at A=X1, B=X0, C=X2
  set e := sdist (X 0) (X 2)
  have he_def : e = Tammes15.ebase d u1 := by
    have hAB : sdist (X 1) (X 0) = d := by
      rw [Tammes15.sdist_comm, hW.side 0]
    have hAC : sdist (X 1) (X 2) = d := hW.side 1
    have h_base := Tammes15.T1_isosceles_base d ⟨hd_pos, hd_lt⟩ (X 1) (X 0) (X 2)
      (hW.unit 1) (hW.unit 0) (hW.unit 2) hAB hAC
    simpa [u1, wangle, hX6, show (1:ℕ)+1 = 2 by norm_num, show (1:ℕ)+6-1 = 6 by norm_num,
      InnerProductGeometry.angle_comm, e] using h_base
  have h_e_pos_lt : 0 < e ∧ e < π := by
    have h0 : 2 % 6 ≠ 0 := by norm_num
    have hmem := hW.sdist_mem 0 2 h0
    simpa [e] using hmem
  rcases h_e_pos_lt with ⟨he_pos, he_lt⟩
  -- slc_tangent at A=X0, B=X2, C=X5
  set θ := angle (tdir (X 0) (X 2)) (tdir (X 0) (X 5))
  have h_slc : cos (sdist (X 2) (X 5)) = cos e * cos d + sin e * sin d * cos θ := by
    have h_slc_raw := Tammes15.slc_tangent (X 0) (X 2) (X 5)
      (hW.unit 0) (hW.unit 2) (hW.unit 5)
    have h_side_pred : sdist (X 0) (X 5) = d := by
      have h := hW.side_pred 0
      simpa [show (0:ℕ)+6-1 = 5 by norm_num] using h
    simpa [e, h_side_pred, θ] using h_slc_raw
  -- cos inequality from hsep
  have h_cos_ineq : cos e * cos d + sin e * sin d * cos θ ≤ cos d := by
    rw [← h_slc]
    have h_sdist_nonneg : 0 ≤ sdist (X 2) (X 5) := by
      rw [Tammes15.sdist]
      exact Real.arccos_nonneg _
    have h_sdist_le_pi : sdist (X 2) (X 5) ≤ π := by
      rw [Tammes15.sdist]
      exact Real.arccos_le_pi _
    have hd_nonneg : 0 ≤ d := by linarith
    have hd_le_pi : d ≤ π := by
      have : d < π / 2 := hd_lt
      linarith
    exact Real.cos_le_cos_of_nonneg_of_le_pi hd_nonneg h_sdist_le_pi hsep
  -- T7_iff
  have h_θ_range : 0 ≤ θ ∧ θ ≤ π := by
    dsimp [θ]
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  rcases h_θ_range with ⟨hθ_nonneg, hθ_le⟩
  have h_T7 := (Tammes15.T7_iff d e θ ⟨hd_pos, hd_lt⟩ ⟨he_pos, he_lt⟩ ⟨hθ_nonneg, hθ_le⟩).mp h_cos_ineq
  -- final inequality
  -- longDiag d u1 = bangle d u1 + arccos (min 1 (cot d * tan (ebase d u1 / 2)))
  -- = bangle d u1 + arccos (min 1 (cot d * tan (e / 2)))  (by he_def)
  -- = angle (tdir X0 X1) (tdir X0 X2) + arccos (min 1 (cot d * tan (e / 2)))  (by ← h_t1_angle)
  -- ≤ angle (tdir X0 X1) (tdir X0 X2) + θ  (by h_T7)
  -- = u0  (by h_angle_split)
  rw [Tammes15.longDiag, ← he_def, ← h_t1_angle]
  -- Goal: angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)) + arccos (min 1 (cot d * tan (e / 2))) ≤ u0
  -- Using h_angle_split: angle (tdir X0 X1) (tdir X0 X2) + θ = u0
  -- So it suffices to show: arccos (min 1 (cot d * tan (e / 2))) ≤ θ
  -- which is exactly h_T7
  -- So we need to show: A + arccos(...) ≤ A + θ, which follows from arccos(...) ≤ θ
  -- Using h_angle_split to rewrite u0
  rw [← h_angle_split]
  -- Goal: angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)) + arccos (min 1 (cot d * tan (e / 2))) ≤
  --       angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)) + θ
  -- This follows from arccos(...) ≤ θ
  have h_add := add_le_add_right h_T7 (angle (tdir (X 0) (X 1)) (tdir (X 0) (X 2)))
  -- h_add : arccos ... + angle ... ≤ θ + angle ...
  -- Goal: angle ... + arccos ... ≤ angle ... + θ
  simpa [add_comm] using h_add

end FaceWalk.Walk

open scoped Classical

section Relations

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

/-- `tri_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem tri_of_realisation_proof (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 3) :
    (assignOf P H d x).corner e = alpha d := by
  have hW := FaceWalk.walk_of_realisation hP hx e
  rw [he] at hW
  have h := FaceWalk.fc_eq_wangle hP hx e 0
  rw [he, Assign.fc, pow_zero, Equiv.Perm.one_apply] at h
  rw [h]
  exact hW.tri

/-- `rhombus_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem rhombus_of_realisation_proof (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 4) :
    (assignOf P H d x).fc e 2 = (assignOf P H d x).fc e 0 ∧
      (assignOf P H d x).fc e 1 = rho d ((assignOf P H d x).fc e 0) := by
  have hW := FaceWalk.walk_of_realisation hP hx e
  rw [he] at hW
  simp only [FaceWalk.fc_eq_wangle hP hx e, he]
  exact hW.rhombus

/-- `hexDiag_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem hexDiag_of_realisation_proof (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 6) :
    HexDiagRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1) := by
  have hW := FaceWalk.walk_of_realisation hP hx e
  rw [he] at hW
  have hsep : d ≤ sdist (x (.inl (FaceWalk.fv P e 2))) (x (.inl (FaceWalk.fv P e 5))) := by
    apply hx.sep
    intro h
    have hs := (hW.sdist_mem 2 3 (by norm_num)).1
    simp only [show 2 + 3 = 5 by norm_num, h, sdist_self _ (hx.unit _), lt_irrefl] at hs
  simp only [FaceWalk.fc_eq_wangle hP hx e, he]
  exact ⟨hW.hexDiag_left hsep, hW.hexDiag_right hsep⟩

end Relations

end Tammes15
