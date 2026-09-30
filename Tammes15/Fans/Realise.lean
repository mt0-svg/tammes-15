import Tammes15.Draw.FaceWalk

/-!
# (T5), (T6) for a realisation

The interfaces `pent_of_realisation` and `hex_of_realisation` of `Tammes15.Hyps.Interfaces`, stated
word for word as `pent_of_realisation_proof` and `hex_of_realisation_proof` (the unused range
hypothesis is named `_hd`); the interface file closes each interface with its theorem. A face of the
realisation is a convex walk (`FaceWalk.walk_of_realisation`) whose angles are the corners of
`assignOf` (`FaceWalk.fc_eq_wangle`). The relations are proved for convex walks from the cores
`T5_corner`, `T5_side_corner`, `T6_corner` (fans of a corner), `T1_isosceles_base` (the diagonals
as bases of isosceles triangles) and `eta_mem_Icc`; the cone hypotheses of the cores are the cones
of the corners (`FaceWalk.Walk.exists_cone`, and `FaceWalk.hex_triple` for the alternate triple of a
hexagon).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15

namespace FaceWalk.Walk

variable {d : ℝ} {X : ℕ → E3}

/-- (T5), the corner at `X 0` of a pentagonal walk: `T5_corner` on `X 0, …, X 4`. -/
theorem pent_u0 (hW : Walk 5 d X) :
    wangle 5 X 0 = bangle d (wangle 5 X 1) +
      gam d (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) + bangle d (wangle 5 X 4) := by
  have hd := hW.d_mem
  have hu0 := hW.unit 0
  have hu1 := hW.unit 1
  have hu2 := hW.unit 2
  have hu3 := hW.unit 3
  have hu4 := hW.unit 4
  have hper0 : X 5 = X 0 := by simpa using hW.periodic 0
  have hper2 : X 7 = X 2 := by simpa using hW.periodic 2
  have hper3 : X 8 = X 3 := by simpa using hW.periodic 3
  have h2mod0 : 2 % 5 ≠ 0 := by norm_num
  have h2mod1 : 2 % 5 ≠ 1 := by norm_num
  have h2mod4 : 2 % 5 ≠ 4 := by norm_num
  have h3mod0 : 3 % 5 ≠ 0 := by norm_num
  have he := hW.sdist_mem 0 2 h2mod0
  have hf := hW.sdist_mem 0 3 h3mod0
  have hsup23 : 0 < ⟪cross (X 2) (X 3), X 0⟫ := by
    simpa [hper0] using hW.support 2 3 (by norm_num) (by norm_num)
  have hsup43 : 0 < ⟪cross (X 4) (X 0), X 2⟫ := by
    simpa [hper0, hper2] using hW.support 4 3 (by norm_num) (by norm_num)
  have hsup44 : 0 < ⟪cross (X 4) (X 0), X 3⟫ := by
    simpa [hper0, hper3] using hW.support 4 4 (by norm_num) (by norm_num)
  have hpq : 0 < ⟪cross (X 0) (X 2), X 4⟫ := by
    calc
      0 < ⟪cross (X 4) (X 0), X 2⟫ := hsup43
      _ = ⟪cross (X 0) (X 2), X 4⟫ := by
        rw [inner_cross_cycle, inner_cross_cycle]
  have hpw : 0 < ⟪cross (X 0) (X 2), X 3⟫ := by
    rw [inner_cross_cycle]
    exact hsup23
  have hqw : 0 < ⟪cross (X 4) (X 0), X 3⟫ := hsup44
  have hu₁ : 0 < angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) := by
    have hcorner1 : alpha d ≤ wangle 5 X 1 := by
      simpa [wangle, hper0] using (hW.corner 1).1
    have hpos_alpha : 0 < alpha d := by
      have h := (alpha_bounds d hd).1
      linarith [pi_pos]
    have hwpos : 0 < wangle 5 X 1 := by linarith
    have hw1_eq : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) = wangle 5 X 1 := by
      calc
        angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) =
            angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by rw [InnerProductGeometry.angle_comm]
        _ = wangle 5 X 1 := by simp [wangle, hper0]
    rw [hw1_eq]
    exact hwpos
  have hu₄ : 0 < angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) := by
    have hcorner4 : alpha d ≤ wangle 5 X 4 := by
      simpa [wangle, hper0, hper3] using (hW.corner 4).1
    have hpos_alpha : 0 < alpha d := by
      have h := (alpha_bounds d hd).1
      linarith [pi_pos]
    have hwpos : 0 < wangle 5 X 4 := by linarith
    have hw4_eq : angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) = wangle 5 X 4 := by
      calc
        angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) =
            angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) := by rw [InnerProductGeometry.angle_comm]
        _ = wangle 5 X 4 := by simp [wangle, hper0, hper3]
    rw [hw4_eq]
    exact hwpos
  have hsdist02 : sdist (X 0) (X 2) = ebase d (wangle 5 X 1) := by
    have hT1 := T1_isosceles_base d hd (X 1) (X 0) (X 2) hu1 hu0 hu2
      (by rw [sdist_comm, hW.side 0]) (hW.side 1)
    have hangle : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) = wangle 5 X 1 := by
      calc
        angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) =
            angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by rw [InnerProductGeometry.angle_comm]
        _ = wangle 5 X 1 := by simp [wangle, hper0]
    rw [hT1, hangle]
  have hsdist03 : sdist (X 0) (X 3) = ebase d (wangle 5 X 4) := by
    have hT1 := T1_isosceles_base d hd (X 4) (X 0) (X 3) hu4 hu0 hu3
      (by simpa [hper0] using hW.side 4) (by rw [sdist_comm, hW.side 3])
    have hangle : angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) = wangle 5 X 4 := by
      calc
        angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) =
            angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) := by rw [InnerProductGeometry.angle_comm]
        _ = wangle 5 X 4 := by rw [wangle, hper0, hper3, InnerProductGeometry.angle_comm]
    rw [hT1, hangle]
  have hw1_eq : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) = wangle 5 X 1 := by
    calc
      angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) =
          angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by rw [InnerProductGeometry.angle_comm]
      _ = wangle 5 X 1 := by simp [wangle, hper0]
  have hw4_eq : angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) = wangle 5 X 4 := by
    calc
      angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) =
          angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) := by rw [InnerProductGeometry.angle_comm]
      _ = wangle 5 X 4 := by simp [wangle, hper0, hper3]
  obtain ⟨l₁, m₁, hl₁pos, hm₁pos, hc₁⟩ := hW.exists_cone 0 2 h2mod0 h2mod1 h2mod4
  obtain ⟨l₂, m₂, hl₂pos, hm₂pos, hc₂⟩ :=
    Tammes15.FaceWalk.exists_cone (X 0) (X 2) (X 4) (X 3) hu0 hpq hpw hqw
  have hT5 := T5_corner d hd (X 0) (X 1) (X 2) (X 3) (X 4)
    hu0 hu1 hu2 hu3 hu4
    (hW.side 0) (hW.side 1) (hW.side 2) (hW.side 3)
    (by simpa [hper0] using hW.side 4)
    hu₁ hu₄ he hf
    l₁ m₁ l₂ m₂
    (le_of_lt hl₁pos) (le_of_lt hm₁pos)
    (le_of_lt hl₂pos) (le_of_lt hm₂pos)
    hc₁ hc₂
  calc
    wangle 5 X 0 = angle (tdir (X 0) (X 1)) (tdir (X 0) (X 4)) := by simp [wangle]
    _ = bangle d (angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2))) +
        gam d (sdist (X 0) (X 2)) (sdist (X 0) (X 3)) +
        bangle d (angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0))) := by rw [hT5]
    _ = bangle d (wangle 5 X 1) + gam d (sdist (X 0) (X 2)) (sdist (X 0) (X 3)) +
        bangle d (wangle 5 X 4) := by
      rw [hw1_eq, hw4_eq]
    _ = bangle d (wangle 5 X 1) + gam d (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) +
        bangle d (wangle 5 X 4) := by rw [hsdist02, hsdist03]

/-- (T5), the corner at `X 2`: `T5_side_corner` on `X 0, X 1, X 2, X 3`. -/
theorem pent_u2 (hW : Walk 5 d X) :
    wangle 5 X 2 =
      bangle d (wangle 5 X 1) + gam (ebase d (wangle 5 X 4)) (ebase d (wangle 5 X 1)) d := by
  have hd : 0 < d ∧ d < π / 2 := hW.d_mem
  have hX5 : X 5 = X 0 := by
    simpa [add_comm] using hW.periodic 0
  have hX6 : X 6 = X 1 := by
    simpa [add_comm] using hW.periodic 1
  have hX8 : X 8 = X 3 := by
    simpa [add_comm] using hW.periodic 3
  -- 0 < angle (tdir X1 X2) (tdir X1 X0) needed for T5_side_corner
  have hu1 : 0 < angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
    have hcorner := hW.corner 1
    have halpha_pos : 0 < alpha d := by
      have := (alpha_bounds d hd).1
      linarith
    have hangle_ge : alpha d ≤ angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
      -- hcorner.1 : alpha d ≤ angle (tdir (X 1) (X (1+1))) (tdir (X 1) (X (1+5-1)))
      simpa [hX5, show (1:ℕ)+1 = 2 by norm_num, show (1:ℕ)+5-1 = 5 by norm_num] using hcorner.1
    linarith
  have hcone := hW.exists_cone 2 3 (by norm_num) (by norm_num) (by norm_num)
  rcases hcone with ⟨l₁, l₂, hl₁pos, hl₂pos, hcone_eq⟩
  have hcone_eq' : tdir (X 2) (X 0) = l₂ • tdir (X 2) (X 1) + l₁ • tdir (X 2) (X 3) := by
    simpa [hX5, hX6, show (2:ℕ)+3 = 5 by norm_num, show (2:ℕ)+1 = 3 by norm_num,
      show (2:ℕ)+5-1 = 6 by norm_num, add_comm] using hcone_eq
  have hsdist_mem := hW.sdist_mem 0 2 (by norm_num)
  have hsdist_X0X2 : 0 < sdist (X 0) (X 2) ∧ sdist (X 0) (X 2) < π := by
    simpa [show (0:ℕ)+2 = 2 by norm_num] using hsdist_mem
  have hT5 := Tammes15.T5_side_corner d hd (X 0) (X 1) (X 2) (X 3)
    (hW.unit 0) (hW.unit 1) (hW.unit 2) (hW.unit 3)
    (hW.side 0) (hW.side 1) (hW.side 2)
    hu1 hsdist_X0X2 l₂ l₁ (by linarith) (by linarith) hcone_eq'
  -- hT5 : angle (tdir X2 X1) (tdir X2 X3) = bangle d (angle (tdir X1 X2) (tdir X1 X0)) + gam (sdist X0 X3) (sdist X0 X2) d
  have hwangle2_eq : wangle 5 X 2 = angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := by
    calc
      wangle 5 X 2 = angle (tdir (X 2) (X (2 + 1))) (tdir (X 2) (X (2 + 5 - 1))) := rfl
      _ = angle (tdir (X 2) (X 3)) (tdir (X 2) (X 6)) := by norm_num
      _ = angle (tdir (X 2) (X 3)) (tdir (X 2) (X 1)) := by simp [hX6]
      _ = angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := by rw [InnerProductGeometry.angle_comm]
  have hwangle1_eq : wangle 5 X 1 = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
    calc
      wangle 5 X 1 = angle (tdir (X 1) (X (1 + 1))) (tdir (X 1) (X (1 + 5 - 1))) := rfl
      _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 5)) := by norm_num
      _ = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by simp [hX5]
  have hsdist03_eq : sdist (X 0) (X 3) = ebase d (wangle 5 X 4) := by
    have hT1 := Tammes15.T1_isosceles_base d hd (X 4) (X 0) (X 3)
      (hW.unit 4) (hW.unit 0) (hW.unit 3)
      (by simpa [hX5, sdist_comm] using hW.side 4)
      (by simpa [sdist_comm] using hW.side 3)
    have hwangle4_eq : wangle 5 X 4 = angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) := by
      calc
        wangle 5 X 4 = angle (tdir (X 4) (X (4 + 1))) (tdir (X 4) (X (4 + 5 - 1))) := rfl
        _ = angle (tdir (X 4) (X 5)) (tdir (X 4) (X 8)) := by norm_num
        _ = angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) := by simp [hX5, hX8]
    rw [hT1, hwangle4_eq]
  have hsdist02_eq : sdist (X 0) (X 2) = ebase d (wangle 5 X 1) := by
    have hT1 := Tammes15.T1_isosceles_base d hd (X 1) (X 0) (X 2)
      (hW.unit 1) (hW.unit 0) (hW.unit 2)
      (by simpa [sdist_comm] using hW.side 0)
      (hW.side 1)
    rw [hT1, angle_comm, ← hwangle1_eq]
  calc
    wangle 5 X 2 = angle (tdir (X 2) (X 1)) (tdir (X 2) (X 3)) := hwangle2_eq
    _ = bangle d (angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0))) + gam (sdist (X 0) (X 3)) (sdist (X 0) (X 2)) d := hT5
    _ = bangle d (wangle 5 X 1) + gam (sdist (X 0) (X 3)) (sdist (X 0) (X 2)) d := by rw [hwangle1_eq]
    _ = bangle d (wangle 5 X 1) + gam (ebase d (wangle 5 X 4)) (sdist (X 0) (X 2)) d := by rw [hsdist03_eq]
    _ = bangle d (wangle 5 X 1) + gam (ebase d (wangle 5 X 4)) (ebase d (wangle 5 X 1)) d := by rw [hsdist02_eq]

/-- (T5), the corner at `X 3`: `T5_side_corner` on `X 0, X 4, X 3, X 2`. -/
theorem pent_u3 (hW : Walk 5 d X) :
    wangle 5 X 3 =
      bangle d (wangle 5 X 4) + gam (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) d := by
  have hd := hW.d_mem
  have h50 : X 5 = X 0 := by simpa using hW.periodic 0
  have h51 : X 6 = X 1 := by simpa using hW.periodic 1
  have h52 : X 7 = X 2 := by simpa using hW.periodic 2
  have h53 : X 8 = X 3 := by simpa using hW.periodic 3
  have hw3 : wangle 5 X 3 = angle (tdir (X 3) (X 4)) (tdir (X 3) (X 2)) := by
    simp [wangle, h52]
  have hw4 : wangle 5 X 4 = angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) := by
    simp [wangle, h50, h53]
  have hw1 : wangle 5 X 1 = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
    simp [wangle, h50]
  rw [hw3, hw4, hw1]
  -- Get positivity of angles from corner bounds
  have h_alpha_pos : 0 < alpha d := by
    have h_alpha_bounds := alpha_bounds d hd
    rcases h_alpha_bounds with ⟨h_left, h_right⟩
    linarith
  have hw4_pos' : 0 < wangle 5 X 4 := by
    have hcorner := hW.corner 4
    rcases hcorner with ⟨hle, _⟩
    have hle' : alpha d ≤ wangle 5 X 4 := by simpa [wangle] using hle
    linarith
  have hw4_pos : 0 < angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) := by
    have : wangle 5 X 4 = angle (tdir (X 4) (X 3)) (tdir (X 4) (X 0)) := by
      simp [wangle, angle_comm, h50, h53]
    rwa [← this]
  have hw1_pos : 0 < angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
    have hcorner := hW.corner 1
    rcases hcorner with ⟨hle, _⟩
    have hle' : alpha d ≤ wangle 5 X 1 := by simpa [wangle] using hle
    have : wangle 5 X 1 = angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) := by
      simp [wangle, angle_comm, h50]
    rw [← this]
    linarith
  -- Get the cone decomposition at vertex 3, skipping vertex 2
  have h_cone := hW.exists_cone 3 2 (by norm_num) (by norm_num) (by norm_num)
  rcases h_cone with ⟨l, l', hl_pos, hl'_pos, h_cone_eq⟩
  have h_cone_eq' : tdir (X 3) (X 0) = l • tdir (X 3) (X 4) + l' • tdir (X 3) (X 2) := by
    simpa [h50, h52] using h_cone_eq
  -- Get sdist X0 X3 bounds
  have h_sdist_03 := hW.sdist_mem 0 3 (by norm_num : 3 % 5 ≠ 0)
  rcases h_sdist_03 with ⟨h_sdist_03_pos, h_sdist_03_lt_pi⟩
  -- Get sdist equalities
  have h_sdist_04 : sdist (X 0) (X 4) = d := by
    simpa using hW.side_pred 0
  have h_sdist_34 : sdist (X 3) (X 4) = d := by
    simpa [sdist_comm] using hW.side 3
  have h_sdist_23 : sdist (X 2) (X 3) = d := by
    simpa [sdist_comm] using hW.side 2
  have h_sdist_10 : sdist (X 1) (X 0) = d := by
    simpa [h50] using hW.side_pred 1
  have h_sdist_12 : sdist (X 1) (X 2) = d := by
    simpa using hW.side 1
  have h_sdist_40 : sdist (X 4) (X 0) = d := by
    rw [sdist_comm]
    simpa [h50] using hW.side_pred 0
  have h_sdist_43 : sdist (X 4) (X 3) = d := by
    rw [sdist_comm]
    simpa [h53] using hW.side 3
  -- T1_isosceles_base for X1: sdist X0 X2 = ebase d (angle (tdir X1 X2) (tdir X1 X0))
  have h_iso1 : sdist (X 0) (X 2) = ebase d (angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2))) :=
    T1_isosceles_base d hd (X 1) (X 0) (X 2) (hW.unit 1) (hW.unit 0) (hW.unit 2)
      h_sdist_10 h_sdist_12
  have h_iso1' : sdist (X 0) (X 2) = ebase d (angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0))) := by
    rw [h_iso1, angle_comm]
  -- T1_isosceles_base for X4: sdist X0 X3 = ebase d (angle (tdir X4 X0) (tdir X4 X3))
  have h_iso4 : sdist (X 0) (X 3) = ebase d (angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3))) :=
    T1_isosceles_base d hd (X 4) (X 0) (X 3) (hW.unit 4) (hW.unit 0) (hW.unit 3)
      h_sdist_40 h_sdist_43
  -- Apply T5_side_corner to (X0, X4, X3, X2)
  have h_t5 := T5_side_corner d hd (X 0) (X 4) (X 3) (X 2)
    (hW.unit 0) (hW.unit 4) (hW.unit 3) (hW.unit 2)
    h_sdist_04
    h_sdist_43
    (by rw [sdist_comm]; exact h_sdist_23)
    hw4_pos
    ⟨h_sdist_03_pos, h_sdist_03_lt_pi⟩
    l l'
    (by linarith)
    (by linarith)
    h_cone_eq'
  simpa [angle_comm, h_iso1', h_iso4] using h_t5

/-- (T5), the three triangle inequalities of the fan at `X 0`. -/
theorem pent_eta (hW : Walk 5 d X) :
    eta d (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) ∈ Set.Icc (-1 : ℝ) 1 ∧
      eta (ebase d (wangle 5 X 4)) (ebase d (wangle 5 X 1)) d ∈ Set.Icc (-1 : ℝ) 1 ∧
      eta (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) d ∈ Set.Icc (-1 : ℝ) 1 := by
  have hd := hW.d_mem
  rcases hd with ⟨hd_pos, hd_lt⟩
  have h0 : ‖X 0‖ = 1 := hW.unit 0
  have h1 : ‖X 1‖ = 1 := hW.unit 1
  have h2 : ‖X 2‖ = 1 := hW.unit 2
  have h3 : ‖X 3‖ = 1 := hW.unit 3
  have h4 : ‖X 4‖ = 1 := hW.unit 4
  -- sdist X2 X3 = d from side adjacency
  have h_sdist_23 : sdist (X 2) (X 3) = d := by
    simpa using hW.side 2
  -- sdist X0 X2 = ebase d (wangle 5 X 1) via T1_isosceles_base with A=X1, B=X0, C=X2
  have h_sdist_02 : sdist (X 0) (X 2) = ebase d (wangle 5 X 1) := by
    have hAB : sdist (X 1) (X 0) = d := by
      simpa [sdist_comm] using hW.side 0
    have hAC : sdist (X 1) (X 2) = d := by
      simpa using hW.side 1
    have h_angle : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) = wangle 5 X 1 := by
      dsimp [wangle]
      have h5 : X 5 = X 0 := by simpa using hW.periodic 0
      simp [h5, InnerProductGeometry.angle_comm]
    simpa [h_angle] using T1_isosceles_base d ⟨hd_pos, hd_lt⟩ (X 1) (X 0) (X 2) h1 h0 h2 hAB hAC
  -- sdist X0 X3 = ebase d (wangle 5 X 4) via T1_isosceles_base with A=X4, B=X0, C=X3
  have h_sdist_03 : sdist (X 0) (X 3) = ebase d (wangle 5 X 4) := by
    have hAB : sdist (X 4) (X 0) = d := by
      have h5 : X 5 = X 0 := by simpa using hW.periodic 0
      simpa [h5, sdist_comm] using hW.side 4
    have hAC : sdist (X 4) (X 3) = d := by
      simpa [sdist_comm] using hW.side 3
    have h_angle : angle (tdir (X 4) (X 0)) (tdir (X 4) (X 3)) = wangle 5 X 4 := by
      dsimp [wangle]
      have h5 : X 5 = X 0 := by simpa using hW.periodic 0
      have h8 : X 8 = X 3 := by
        calc
          X 8 = X (3 + 5) := by ring
          _ = X 3 := by simpa using hW.periodic 3
      simp [h5, h8]
    simpa [h_angle] using T1_isosceles_base d ⟨hd_pos, hd_lt⟩ (X 4) (X 0) (X 3) h4 h0 h3 hAB hAC
  -- sdist equalities via sdist_comm
  have h_sdist_20_eq : sdist (X 2) (X 0) = sdist (X 0) (X 2) := sdist_comm _ _
  have h_sdist_30_eq : sdist (X 3) (X 0) = sdist (X 0) (X 3) := sdist_comm _ _
  have h_sdist_32_eq : sdist (X 3) (X 2) = sdist (X 2) (X 3) := sdist_comm _ _
  -- distance bounds from hW.sdist_mem
  have h_sdist_02_bound : 0 < sdist (X 0) (X 2) ∧ sdist (X 0) (X 2) < π := by
    have h := hW.sdist_mem 0 2 (by norm_num)
    simpa using h
  have h_sdist_03_bound : 0 < sdist (X 0) (X 3) ∧ sdist (X 0) (X 3) < π := by
    have h := hW.sdist_mem 0 3 (by norm_num)
    simpa using h
  have h_sdist_23_bound : 0 < sdist (X 2) (X 3) ∧ sdist (X 2) (X 3) < π := by
    have h := hW.sdist_mem 2 1 (by norm_num)
    simpa using h
  have h_sdist_20_bound : 0 < sdist (X 2) (X 0) ∧ sdist (X 2) (X 0) < π := by
    have h := hW.sdist_mem 0 2 (by norm_num)
    simpa [sdist_comm] using h
  have h_sdist_30_bound : 0 < sdist (X 3) (X 0) ∧ sdist (X 3) (X 0) < π := by
    have h := hW.sdist_mem 0 3 (by norm_num)
    simpa [sdist_comm] using h
  have h_sdist_32_bound : 0 < sdist (X 3) (X 2) ∧ sdist (X 3) (X 2) < π := by
    have h := hW.sdist_mem 2 1 (by norm_num)
    simpa [sdist_comm] using h
  -- first eta: eta (sdist X2 X3) (sdist X0 X2) (sdist X0 X3) = eta d (ebase d u1) (ebase d u4)
  have h_eta1 : eta d (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := eta_mem_Icc (X 0) (X 2) (X 3) h0 h2 h3 h_sdist_02_bound h_sdist_03_bound
    rw [h_sdist_23, h_sdist_02, h_sdist_03] at h
    exact h
  -- second eta: eta (sdist X0 X3) (sdist X2 X0) (sdist X2 X3) = eta (ebase d u4) (ebase d u1) d
  have h_eta2 : eta (ebase d (wangle 5 X 4)) (ebase d (wangle 5 X 1)) d ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := eta_mem_Icc (X 2) (X 0) (X 3) h2 h0 h3 h_sdist_20_bound h_sdist_23_bound
    rw [h_sdist_03, h_sdist_20_eq, h_sdist_02, h_sdist_23] at h
    exact h
  -- third eta: eta (sdist X0 X2) (sdist X3 X0) (sdist X3 X2) = eta (ebase d u1) (ebase d u4) d
  have h_eta3 : eta (ebase d (wangle 5 X 1)) (ebase d (wangle 5 X 4)) d ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := eta_mem_Icc (X 3) (X 0) (X 2) h3 h0 h2 h_sdist_30_bound h_sdist_32_bound
    rw [h_sdist_02, h_sdist_30_eq, h_sdist_03, h_sdist_32_eq, h_sdist_23] at h
    exact h
  exact ⟨h_eta1, h_eta2, h_eta3⟩

theorem pent (hW : Walk 5 d X) :
    PentRel d (wangle 5 X 0) (wangle 5 X 1) (wangle 5 X 2) (wangle 5 X 3) (wangle 5 X 4) := by
  obtain ⟨h1, h2, h3⟩ := hW.pent_eta
  exact ⟨h1, h2, h3, hW.pent_u0, hW.pent_u2, hW.pent_u3⟩

/-- (T6) at `X 0` of a hexagonal walk: `T6_corner` on `X 0, X 1, X 2, X 4, X 5`, with the
triangle inequality of the triangle `X 0, X 2, X 4`. -/
theorem hex_base (hW : Walk 6 d X) :
    eta (ebase d (wangle 6 X 3)) (ebase d (wangle 6 X 1)) (ebase d (wangle 6 X 5)) ∈
        Set.Icc (-1 : ℝ) 1 ∧
      wangle 6 X 0 = bangle d (wangle 6 X 5) +
        gam (ebase d (wangle 6 X 3)) (ebase d (wangle 6 X 1)) (ebase d (wangle 6 X 5)) +
          bangle d (wangle 6 X 1) := by
  have hd_mem : 0 < d ∧ d < π / 2 := hW.d_mem
  have hd_pos : 0 < d := hd_mem.1
  have hd_lt_pi2 : d < π / 2 := hd_mem.2
  have halpha_pos : 0 < alpha d := by
    have h := (alpha_bounds d hd_mem).1
    have hpi : 0 < π / 3 := by positivity
    linarith
  -- periodicity simplifications
  have hX6 : X 6 = X 0 := by simpa using hW.periodic 0
  have hX7 : X 7 = X 1 := by
    calc
      X 7 = X (1 + 6) := by norm_num
      _ = X 1 := by simpa using hW.periodic 1
  have hX8 : X 8 = X 2 := by
    calc
      X 8 = X (2 + 6) := by norm_num
      _ = X 2 := by simpa using hW.periodic 2
  have hX9 : X 9 = X 3 := by
    calc
      X 9 = X (3 + 6) := by norm_num
      _ = X 3 := by simpa using hW.periodic 3
  have hX10 : X 10 = X 4 := by
    calc
      X 10 = X (4 + 6) := by norm_num
      _ = X 4 := by simpa using hW.periodic 4
  -- side equalities
  have h01 : sdist (X 0) (X 1) = d := hW.side 0
  have h12 : sdist (X 1) (X 2) = d := hW.side 1
  have h23 : sdist (X 2) (X 3) = d := hW.side 2
  have h34 : sdist (X 3) (X 4) = d := hW.side 3
  have h45 : sdist (X 4) (X 5) = d := hW.side 4
  have h50 : sdist (X 5) (X 0) = d := by simpa [hX6] using hW.side 5
  -- modular arithmetic facts
  have hmod2_0 : 2 % 6 ≠ 0 := by norm_num
  have hmod2_1 : 2 % 6 ≠ 1 := by norm_num
  have hmod2_5 : 2 % 6 ≠ 5 := by norm_num
  have hmod3_0 : 3 % 6 ≠ 0 := by norm_num
  have hmod3_1 : 3 % 6 ≠ 1 := by norm_num
  have hmod4_0 : 4 % 6 ≠ 0 := by norm_num
  have hmod4_1 : 4 % 6 ≠ 1 := by norm_num
  have hmod5_0 : 5 % 6 ≠ 0 := by norm_num
  have hmod5_1 : 5 % 6 ≠ 1 := by norm_num
  -- sdist_mem for indices 2 and 4
  have hmem2 := Walk.sdist_mem hW 0 2 hmod2_0
  have hmem4 := Walk.sdist_mem hW 0 4 hmod4_0
  -- corner simplifications
  have hcorner1 := hW.corner 1
  have hcorner5 := hW.corner 5
  have hcorner1_simp : alpha d ≤ angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) ∧
      angle (tdir (X 1) (X 2)) (tdir (X 1) (X 0)) < π := by
    simpa [hX6] using hcorner1
  have hcorner5_simp : alpha d ≤ angle (tdir (X 5) (X 0)) (tdir (X 5) (X 4)) ∧
      angle (tdir (X 5) (X 0)) (tdir (X 5) (X 4)) < π := by
    simpa [hX6, hX10] using hcorner5
  -- angle positivity using angle_comm
  have hu1 : 0 < angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) := by
    rw [InnerProductGeometry.angle_comm]
    exact lt_of_lt_of_le halpha_pos hcorner1_simp.1
  have hu5 : 0 < angle (tdir (X 5) (X 4)) (tdir (X 5) (X 0)) := by
    rw [InnerProductGeometry.angle_comm]
    exact lt_of_lt_of_le halpha_pos hcorner5_simp.1
  -- inner product conditions for generic exists_cone (hc₂)
  have hpq : 0 < ⟪cross (X 0) (X 2), X 5⟫ := by
    have h := hW.support 5 3 hmod3_0 hmod3_1
    -- h : 0 < ⟪cross (X 5) (X 6), X 8⟫
    -- goal : 0 < ⟪cross (X 0) (X 2), X 5⟫
    -- ⟪cross (X 5) (X 0), X 2⟫ = ⟪cross (X 0) (X 2), X 5⟫ by inner_cross_cycle
    simpa [hX6, hX8, Tammes15.FaceWalk.inner_cross_cycle] using h
  have hpw : 0 < ⟪cross (X 0) (X 2), X 4⟫ := by
    have h014 : 0 < ⟪cross (X 0) (X 1), X 4⟫ := by
      have h := hW.support 0 4 hmod4_0 hmod4_1
      simpa using h
    have h124 : 0 < ⟪cross (X 1) (X 2), X 4⟫ := by
      have h := hW.support 1 3 hmod3_0 hmod3_1
      simpa using h
    have h340 : 0 < ⟪cross (X 3) (X 4), X 0⟫ := by
      have h := hW.support 3 3 hmod3_0 hmod3_1
      simpa [hX6] using h
    have h341 : 0 < ⟪cross (X 3) (X 4), X 1⟫ := by
      have h := hW.support 3 4 hmod4_0 hmod4_1
      simpa [hX7] using h
    have h342 : 0 < ⟪cross (X 3) (X 4), X 2⟫ := by
      have h := hW.support 3 5 hmod5_0 hmod5_1
      simpa [hX8] using h
    exact Tammes15.FaceWalk.hex_triple (X 0) (X 1) (X 2) (X 3) (X 4) h014 h124 h340 h341 h342
  have hqw : 0 < ⟪cross (X 5) (X 0), X 4⟫ := by
    have h := hW.support 5 5 hmod5_0 hmod5_1
    simpa [hX6, hX10] using h
  -- get l₁, m₁ for hc₁ from Walk.exists_cone
  obtain ⟨l₁, m₁, hl₁_pos, hm₁_pos, hc₁⟩ := hW.exists_cone 0 2 hmod2_0 hmod2_1 hmod2_5
  have hl₁ : 0 ≤ l₁ := le_of_lt hl₁_pos
  have hm₁ : 0 ≤ m₁ := le_of_lt hm₁_pos
  -- get l₂, m₂ for hc₂ from generic exists_cone
  obtain ⟨l₂, m₂, hl₂_pos, hm₂_pos, hc₂⟩ :=
    Tammes15.FaceWalk.exists_cone (X 0) (X 2) (X 5) (X 4) (hW.unit 0) hpq hpw hqw
  have hl₂ : 0 ≤ l₂ := le_of_lt hl₂_pos
  have hm₂ : 0 ≤ m₂ := le_of_lt hm₂_pos
  -- simplify hc₁ and hc₂ using index arithmetic
  have hc₁_simp : tdir (X 0) (X 2) = l₁ • tdir (X 0) (X 1) + m₁ • tdir (X 0) (X 5) := by
    simpa using hc₁
  have hc₂_simp : tdir (X 0) (X 4) = l₂ • tdir (X 0) (X 2) + m₂ • tdir (X 0) (X 5) := by
    simpa using hc₂
  -- apply T6_corner
  have hT6 := Tammes15.T6_corner d hd_mem (X 0) (X 1) (X 2) (X 4) (X 5)
    (hW.unit 0) (hW.unit 1) (hW.unit 2) (hW.unit 4) (hW.unit 5)
    h01 h12 h45 h50 hu1 hu5 hmem2 hmem4 l₁ m₁ l₂ m₂ hl₁ hm₁ hl₂ hm₂ hc₁_simp hc₂_simp
  -- hT6 : angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)) = ...
  -- simplify LHS: angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)) = wangle 6 X 0
  have hLHS : angle (tdir (X 0) (X 1)) (tdir (X 0) (X 5)) = wangle 6 X 0 := by
    simp [wangle]
  rw [hLHS] at hT6
  -- simplify RHS angles using angle_comm and periodicity
  have hRHS1 : angle (tdir (X 1) (X 0)) (tdir (X 1) (X 2)) = wangle 6 X 1 := by
    simp [wangle, hX6, InnerProductGeometry.angle_comm]
  have hRHS5 : angle (tdir (X 5) (X 4)) (tdir (X 5) (X 0)) = wangle 6 X 5 := by
    simp [wangle, hX6, hX10, InnerProductGeometry.angle_comm]
  rw [hRHS1, hRHS5] at hT6
  -- now hT6 : wangle 6 X 0 = bangle d (wangle 6 X 1) + gam (sdist (X 2) (X 4)) (sdist (X 0) (X 2)) (sdist (X 0) (X 4)) + bangle d (wangle 6 X 5)
  -- convert sdist to ebase using T1_isosceles_base
  have hbase02 : sdist (X 0) (X 2) = ebase d (wangle 6 X 1) := by
    have h := Tammes15.T1_isosceles_base d hd_mem (X 1) (X 0) (X 2) (hW.unit 1) (hW.unit 0) (hW.unit 2)
      (by rw [sdist_comm]; exact h01) h12
    rw [hRHS1] at h
    exact h
  have hbase04 : sdist (X 0) (X 4) = ebase d (wangle 6 X 5) := by
    have h := Tammes15.T1_isosceles_base d hd_mem (X 5) (X 0) (X 4) (hW.unit 5) (hW.unit 0) (hW.unit 4)
      h50 (by rw [sdist_comm]; exact h45)
    have h_angle : angle (tdir (X 5) (X 0)) (tdir (X 5) (X 4)) = wangle 6 X 5 := by
      rw [InnerProductGeometry.angle_comm]
      exact hRHS5
    rw [h_angle] at h
    exact h
  have hbase24 : sdist (X 2) (X 4) = ebase d (wangle 6 X 3) := by
    have h := Tammes15.T1_isosceles_base d hd_mem (X 3) (X 2) (X 4) (hW.unit 3) (hW.unit 2) (hW.unit 4)
      (by rw [sdist_comm]; exact h23) h34
    have hw3 : angle (tdir (X 3) (X 2)) (tdir (X 3) (X 4)) = wangle 6 X 3 := by
      simp [wangle, hX8, InnerProductGeometry.angle_comm]
    rw [hw3] at h
    exact h
  -- rewrite sdist to ebase in hT6
  rw [hbase24, hbase02, hbase04] at hT6
  -- now hT6 : wangle 6 X 0 = bangle d (wangle 6 X 1) + gam (ebase d (wangle 6 X 3)) (ebase d (wangle 6 X 1)) (ebase d (wangle 6 X 5)) + bangle d (wangle 6 X 5)
  -- reorder to match target
  have hangle_eq : wangle 6 X 0 = bangle d (wangle 6 X 5) +
      gam (ebase d (wangle 6 X 3)) (ebase d (wangle 6 X 1)) (ebase d (wangle 6 X 5)) +
        bangle d (wangle 6 X 1) := by
    linarith [hT6]
  -- eta part
  have heta_mem : eta (ebase d (wangle 6 X 3)) (ebase d (wangle 6 X 1)) (ebase d (wangle 6 X 5)) ∈
      Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc]
    have h := Tammes15.eta_mem_Icc (X 0) (X 2) (X 4) (hW.unit 0) (hW.unit 2) (hW.unit 4) hmem2 hmem4
    rcases h with ⟨hle1, hle2⟩
    simpa [hbase24, hbase02, hbase04] using And.intro hle1 hle2
  exact And.intro heta_mem hangle_eq

theorem hex (hW : Walk 6 d X) :
    HexRel d (wangle 6 X 0) (wangle 6 X 1) (wangle 6 X 2) (wangle 6 X 3) (wangle 6 X 4)
      (wangle 6 X 5) := by
  have h0 := hW.hex_base
  have h2 := (hW.shift 2).hex_base
  have h4 := (hW.shift 4).hex_base
  simp only [wangle_shift 6 _ _ X (by norm_num)] at h2 h4
  have h7 : wangle 6 X 7 = wangle 6 X 1 := hW.wangle_add 1
  have h9 : wangle 6 X 9 = wangle 6 X 3 := hW.wangle_add 3
  norm_num only [h7, h9] at h2 h4
  refine ⟨h0.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eta_comm]
    exact h2.1
  · rw [eta_comm]
    exact h4.1
  · rw [h0.2]
  · rw [h2.2, gam_comm]
  · rw [h4.2, gam_comm]

end FaceWalk.Walk

open scoped Classical

section Relations

variable {P : PlaneGraph} {k : ℕ} {H : HexChoice P k} {d : ℝ} {x : Pts P k → E3}

/-- `pent_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem pent_of_realisation_proof (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 5) :
    PentRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1)
      ((assignOf P H d x).fc e 2) ((assignOf P H d x).fc e 3) ((assignOf P H d x).fc e 4) := by
  have hW := FaceWalk.walk_of_realisation hP hx e
  rw [he] at hW
  simp only [FaceWalk.fc_eq_wangle hP hx e, he]
  exact hW.pent

/-- `hex_of_realisation` of `Tammes15.Hyps.Interfaces`. -/
theorem hex_of_realisation_proof (hP : InClass P) (_hd : dlo ≤ d ∧ d ≤ dhi)
    (hx : Realisation P H d x) (e : P.G.Dart) (he : fsize P e = 6) :
    HexRel d ((assignOf P H d x).fc e 0) ((assignOf P H d x).fc e 1)
      ((assignOf P H d x).fc e 2) ((assignOf P H d x).fc e 3) ((assignOf P H d x).fc e 4)
      ((assignOf P H d x).fc e 5) := by
  have hW := FaceWalk.walk_of_realisation hP hx e
  rw [he] at hW
  simp only [FaceWalk.fc_eq_wangle hP hx e, he]
  exact hW.hex

end Relations

end Tammes15
