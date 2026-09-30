import Tammes15.Geom.Frame
import Tammes15.Geom.Lune

/-!
# Perimeter monotonicity by a lune count

For unit `a`, `b` the half-open lune `lune a b` (points `n` of the open unit ball with
`0 < ⟪n, a⟫` and `⟪n, b⟫ ≤ 0`) has volume `2/3 · sdist a b` (`volume_lune`: in a frame with `a`
first and `b` in the first two coordinates it is the part of the ball over a planar sector of angle
`sdist a b`). Summing over the sides of a closed walk, `∫⁻ cnt m A = 4/3 · perim m A`
(`lintegral_cnt`), where `cnt m A n` counts, for `n` in the ball, the sides whose ends lie on
different sides of the plane `n^⊥` (`cnt_eq`).

For a polygon in cone form the count is at most two (`IsCPoly.chg_le_two`: four alternating signs
contradict `cramer4` with `IsCPoly.triple_pos`), and a point of the closed face is a nonnegative
combination of three vertices (`IsCPoly.cone_of_inClosed`). So if every vertex of `B` lies in the
closed face of `A`, then `cnt m' B ≤ cnt m A` pointwise and `perim m' B ≤ perim m A`
(`perim_mono`).
-/

open Real InnerProductGeometry MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Tammes15.Geom

/-- The half-open lune of `a` and `b` in the open unit ball. -/
def lune (a b : E3) : Set E3 := {n | ‖n‖ < 1 ∧ 0 < ⟪n, a⟫ ∧ ⟪n, b⟫ ≤ 0}

theorem measurableSet_lune (a b : E3) : MeasurableSet (lune a b) := by
  dsimp [lune]
  have h_norm : MeasurableSet {n : E3 | ‖n‖ < 1} := by
    have hball : Metric.ball (0 : E3) 1 = {n : E3 | ‖n‖ < 1} := by
      ext n; simp [Metric.mem_ball, dist_eq_norm]
    rw [← hball]
    exact measurableSet_ball
  have h_inner_a_pos : MeasurableSet {n : E3 | 0 < ⟪n, a⟫} := by
    have h_meas : Measurable (fun n : E3 => ⟪n, a⟫) :=
      Measurable.inner measurable_id measurable_const
    exact measurableSet_lt measurable_const h_meas
  have h_inner_b_nonpos : MeasurableSet {n : E3 | ⟪n, b⟫ ≤ 0} := by
    have h_meas : Measurable (fun n : E3 => ⟪n, b⟫) :=
      Measurable.inner measurable_id measurable_const
    exact measurableSet_le h_meas measurable_const
  have h_eq : ({n : E3 | ‖n‖ < 1 ∧ 0 < ⟪n, a⟫ ∧ ⟪n, b⟫ ≤ 0} : Set E3) =
      ({n : E3 | ‖n‖ < 1} ∩ {n : E3 | 0 < ⟪n, a⟫} ∩ {n : E3 | ⟪n, b⟫ ≤ 0}) := by
    ext n; simp [and_assoc]
  rw [h_eq]
  exact (h_norm.inter h_inner_a_pos).inter h_inner_b_nonpos

/-- A frame with `a` as first axis and `b` in the plane of the first two axes. -/
theorem exists_lune_frame (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ f : E3 ≃ₗᵢ[ℝ] E3, ∀ n : E3, f n 0 = ⟪n, a⟫ ∧
      ⟪n, b⟫ = cos (sdist a b) * f n 0 + sin (sdist a b) * f n 1 := by
  obtain ⟨u, hu, hau, hb'⟩ := exists_tangent_unit a b ha hb
  obtain ⟨O, hex, hey, -, -⟩ := frame_isometry a u (cross a u) (frame_of_orth a u ha hu hau)
  refine ⟨O.symm, fun n => ?_⟩
  have h0 : O.symm n 0 = ⟪n, a⟫ := by
    have : O.symm n 0 = ⟪ex, O.symm n⟫ := by rw [inner_coords]; simp [ex]
    rw [this, ← LinearIsometryEquiv.inner_map_eq_flip, hex, real_inner_comm]
  have h1 : O.symm n 1 = ⟪n, u⟫ := by
    have : O.symm n 1 = ⟪ey, O.symm n⟫ := by rw [inner_coords]; simp [ey]
    rw [this, ← LinearIsometryEquiv.inner_map_eq_flip, hey, real_inner_comm]
  refine ⟨h0, ?_⟩
  have hnb := congrArg (fun v => ⟪n, v⟫) hb'
  simp only [inner_add_right, real_inner_smul_right] at hnb
  rw [h0, h1, hnb]

theorem lune_eq_preimage (a b : E3) (θ : ℝ) (f : E3 ≃ₗᵢ[ℝ] E3)
    (hf : ∀ n : E3, f n 0 = ⟪n, a⟫ ∧ ⟪n, b⟫ = cos θ * f n 0 + sin θ * f n 1) :
    lune a b = f ⁻¹' csect θ := by
  ext n
  simp only [lune, csect, Set.mem_preimage]
  have hf_n := hf n
  rcases hf_n with ⟨hf0, hf1⟩
  have hnorm := LinearIsometryEquiv.norm_map f n
  simp [hf0, hf1, hnorm, mul_comm]

theorem sdist_mem_Icc (a b : E3) : 0 ≤ sdist a b ∧ sdist a b ≤ π :=
  ⟨arccos_nonneg _, arccos_le_pi _⟩

theorem sdist_comm (a b : E3) : sdist a b = sdist b a := by
  unfold sdist; rw [real_inner_comm]

theorem volume_lune (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    volume (lune a b) = ENNReal.ofReal (2 / 3 * sdist a b) := by
  obtain ⟨f, hf⟩ := exists_lune_frame a b ha hb
  rw [lune_eq_preimage a b (sdist a b) f hf,
    (LinearIsometryEquiv.measurePreserving f).measure_preimage
      (measurableSet_csect _).nullMeasurableSet,
    volume_csect _ (sdist_mem_Icc a b).1 (sdist_mem_Icc a b).2]

/-- The lune count of a closed walk: for each side, the indicators of its two lunes. -/
noncomputable def cnt (m : ℕ) (A : ℕ → E3) (n : E3) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range m,
    ((lune (A i) (A (i + 1))).indicator 1 n + (lune (A (i + 1)) (A i)).indicator 1 n)

theorem lintegral_cnt (m : ℕ) (A : ℕ → E3) (hA : ∀ i, ‖A i‖ = 1) :
    ∫⁻ n, cnt m A n = ENNReal.ofReal (4 / 3 * perim m A) := by
  unfold cnt perim
  have hmeas : ∀ i ∈ Finset.range m, Measurable fun (n : E3) =>
      (((lune (A i) (A (i + 1))).indicator (1 : E3 → ℝ≥0∞)) n + ((lune (A (i + 1)) (A i)).indicator (1 : E3 → ℝ≥0∞)) n) := by
    intro i hi
    refine Measurable.add ?_ ?_
    · exact (measurable_const (β := E3) (a := (1 : ℝ≥0∞))).indicator (measurableSet_lune _ _)
    · exact (measurable_const (β := E3) (a := (1 : ℝ≥0∞))).indicator (measurableSet_lune _ _)
  rw [lintegral_finsetSum _ hmeas]
  have hsummand (i : ℕ) : ∫⁻ (a : E3), ((lune (A i) (A (i + 1))).indicator 1 a + (lune (A (i + 1)) (A i)).indicator 1 a) =
      ENNReal.ofReal (4 / 3 * sdist (A i) (A (i + 1))) := by
    have h_indicator1 : Measurable fun (a : E3) => (lune (A i) (A (i + 1))).indicator (1 : E3 → ℝ≥0∞) a :=
      (measurable_const (β := E3) (a := (1 : ℝ≥0∞))).indicator (measurableSet_lune _ _)
    have h_indicator2 : Measurable fun (a : E3) => (lune (A (i + 1)) (A i)).indicator (1 : E3 → ℝ≥0∞) a :=
      (measurable_const (β := E3) (a := (1 : ℝ≥0∞))).indicator (measurableSet_lune _ _)
    have h_add := lintegral_add_left (μ := volume) h_indicator1 (fun a => (lune (A (i + 1)) (A i)).indicator (1 : E3 → ℝ≥0∞) a)
    rw [h_add]
    rw [lintegral_indicator_one (measurableSet_lune _ _)]
    rw [lintegral_indicator_one (measurableSet_lune _ _)]
    rw [volume_lune (A i) (A (i + 1)) (hA i) (hA (i + 1)),
      volume_lune (A (i + 1)) (A i) (hA (i + 1)) (hA i),
      sdist_comm (A (i + 1)) (A i)]
    have hs := sdist_mem_Icc (A i) (A (i + 1))
    have hnonneg : 0 ≤ 2 / 3 * sdist (A i) (A (i + 1)) := by nlinarith
    rw [← ENNReal.ofReal_add hnonneg hnonneg]
    ring_nf
  calc
    (∑ i ∈ Finset.range m, ∫⁻ (a : E3), ((lune (A i) (A (i + 1))).indicator 1 a + (lune (A (i + 1)) (A i)).indicator 1 a))
        = (∑ i ∈ Finset.range m, ENNReal.ofReal (4 / 3 * sdist (A i) (A (i + 1)))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hsummand i]
    _ = ENNReal.ofReal (∑ i ∈ Finset.range m, (4 / 3 * sdist (A i) (A (i + 1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      have hs := sdist_mem_Icc (A i) (A (i + 1))
      nlinarith
    _ = ENNReal.ofReal ((4 / 3) * (∑ i ∈ Finset.range m, sdist (A i) (A (i + 1)))) := by
      simp_rw [Finset.mul_sum]

/-- Sign changes of a Boolean sequence along `range m`. -/
def bchg (m : ℕ) (s : ℕ → Bool) : ℕ := ((Finset.range m).filter fun i => s i ≠ s (i + 1)).card

/-- Sign changes of `0 < ⟪n, A i⟫` along one period. -/
noncomputable def chg (m : ℕ) (A : ℕ → E3) (n : E3) : ℕ :=
  bchg m fun i => decide (0 < ⟪n, A i⟫)

theorem cnt_eq (m : ℕ) (A : ℕ → E3) (n : E3) :
    cnt m A n = if ‖n‖ < 1 then (chg m A n : ℝ≥0∞) else 0 := by
  by_cases h : ‖n‖ < 1
  · have h_indicator (a b : E3) : (lune a b).indicator 1 n + (lune b a).indicator 1 n =
      if decide (0 < ⟪n, a⟫) ≠ decide (0 < ⟪n, b⟫) then (1 : ℝ≥0∞) else 0 := by
      have mem_lune (x y : E3) : (lune x y).indicator 1 n =
          if 0 < ⟪n, x⟫ ∧ ⟪n, y⟫ ≤ 0 then (1 : ℝ≥0∞) else 0 := by
        simp [lune, Set.indicator_apply, h]
      simp [mem_lune]
      by_cases ha : 0 < ⟪n, a⟫
      · by_cases hb : 0 < ⟪n, b⟫
        · simp [ha, hb, not_le.mpr ha]
        · have hb' : ⟪n, b⟫ ≤ 0 := by linarith
          simp [ha, hb, hb']
      · have ha' : ⟪n, a⟫ ≤ 0 := by linarith
        by_cases hb : 0 < ⟪n, b⟫
        · simp [ha, hb, ha']
        · have hb' : ⟪n, b⟫ ≤ 0 := by linarith
          simp [ha, hb, ha', hb']
    calc
      cnt m A n = ∑ i ∈ Finset.range m,
        ((lune (A i) (A (i + 1))).indicator 1 n + (lune (A (i + 1)) (A i)).indicator 1 n) := rfl
      _ = ∑ i ∈ Finset.range m,
        (if decide (0 < ⟪n, A i⟫) ≠ decide (0 < ⟪n, A (i + 1)⟫) then (1 : ℝ≥0∞) else 0) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [h_indicator (A i) (A (i + 1))]
      _ = ((Finset.range m).filter fun i => decide (0 < ⟪n, A i⟫) ≠ decide (0 < ⟪n, A (i + 1)⟫)).card := by
        simp [Finset.card_filter]
      _ = (chg m A n : ℝ≥0∞) := by
        simp [chg, bchg]
      _ = if ‖n‖ < 1 then (chg m A n : ℝ≥0∞) else 0 := by simp [h]
  · simp [cnt, lune, h]

/-- A periodic Boolean sequence with no cyclically ordered pattern `true, false, true, false`
changes at most twice along a period. -/
theorem bchg_le_two (m : ℕ) (s : ℕ → Bool) (hper : ∀ i, s (i + m) = s i)
    (hno : ∀ i j k l, i < j → j < k → k < l → l < i + m →
      ¬ (s i = true ∧ s j = false ∧ s k = true ∧ s l = false)) :
    bchg m s ≤ 2 := by
  by_contra! h
  unfold bchg at h
  rcases Finset.two_lt_card_iff.mp h with ⟨c1, c2, c3, hc1, hc2, hc3, hc1c2, hc1c3, hc2c3⟩
  have hc1_mem : c1 ∈ Finset.range m := (Finset.mem_filter.mp hc1).1
  have hc1_ne : s c1 ≠ s (c1 + 1) := (Finset.mem_filter.mp hc1).2
  have hc2_mem : c2 ∈ Finset.range m := (Finset.mem_filter.mp hc2).1
  have hc2_ne : s c2 ≠ s (c2 + 1) := (Finset.mem_filter.mp hc2).2
  have hc3_mem : c3 ∈ Finset.range m := (Finset.mem_filter.mp hc3).1
  have hc3_ne : s c3 ≠ s (c3 + 1) := (Finset.mem_filter.mp hc3).2
  have hc1_range : c1 < m := Finset.mem_range.mp hc1_mem
  have hc2_range : c2 < m := Finset.mem_range.mp hc2_mem
  have hc3_range : c3 < m := Finset.mem_range.mp hc3_mem
  -- get a sorted triple from {c1, c2, c3}
  have h12 := Nat.lt_or_gt_of_ne hc1c2
  have h13 := Nat.lt_or_gt_of_ne hc1c3
  have h23 := Nat.lt_or_gt_of_ne hc2c3
  rcases h12 with (hc1_lt_c2 | hc2_lt_c1)
  · -- c1 < c2
    rcases h13 with (hc1_lt_c3 | hc3_lt_c1)
    · -- c1 < c2, c1 < c3
      rcases h23 with (hc2_lt_c3 | hc3_lt_c2)
      · -- c1 < c2 < c3
        exact aux c1 c2 c3 hc1_lt_c2 hc2_lt_c3 hc1_ne hc2_ne hc3_ne hc1_range hc2_range hc3_range
      · -- c1 < c3 < c2
        exact aux c1 c3 c2 hc1_lt_c3 hc3_lt_c2 hc1_ne hc3_ne hc2_ne hc1_range hc3_range hc2_range
    · -- c1 < c2, c3 < c1: so c3 < c1 < c2
      rcases h23 with (hc2_lt_c3 | hc3_lt_c2)
      · -- c2 < c3 < c1, but c1 < c2, contradiction
        omega
      · -- c3 < c2, and c3 < c1 < c2
        exact aux c3 c1 c2 hc3_lt_c1 hc1_lt_c2 hc3_ne hc1_ne hc2_ne hc3_range hc1_range hc2_range
  · -- c2 < c1
    rcases h13 with (hc1_lt_c3 | hc3_lt_c1)
    · -- c2 < c1 < c3
      exact aux c2 c1 c3 hc2_lt_c1 hc1_lt_c3 hc2_ne hc1_ne hc3_ne hc2_range hc1_range hc3_range
    · -- c2 < c1, c3 < c1
      rcases h23 with (hc2_lt_c3 | hc3_lt_c2)
      · -- c2 < c3 < c1
        exact aux c2 c3 c1 hc2_lt_c3 hc3_lt_c1 hc2_ne hc3_ne hc1_ne hc2_range hc3_range hc1_range
      · -- c3 < c2 < c1
        exact aux c3 c2 c1 hc3_lt_c2 hc2_lt_c1 hc3_ne hc2_ne hc1_ne hc3_range hc2_range hc1_range
where
  aux (a b c : ℕ) (ha_lt_b : a < b) (hb_lt_c : b < c)
      (ha_ne : s a ≠ s (a + 1)) (hb_ne : s b ≠ s (b + 1)) (hc_ne : s c ≠ s (c + 1))
      (ha_range : a < m) (hb_range : b < m) (hc_range : c < m) : False := by
    set x1 := s a with hx1
    set y1 := s (a + 1) with hy1
    set x2 := s b with hx2
    set y2 := s (b + 1) with hy2
    set x3 := s c with hx3
    set y3 := s (c + 1) with hy3
    have hx1_ne_y1 : x1 ≠ y1 := ha_ne
    have hx2_ne_y2 : x2 ≠ y2 := hb_ne
    have hx3_ne_y3 : x3 ≠ y3 := hc_ne
    -- helper: from ¬(b = true) deduce b = false
    have opposite' {b : Bool} (hb : ¬ b) : b = false := (Bool.not_eq_true b).mp hb
    by_cases hy1_ne_x2 : y1 ≠ x2
    · -- Case 1: y1 ≠ x2, use a, a+1, b, b+1
      have ha1_lt_b : a + 1 < b := by
        by_contra! hle
        have hbeq : b = a + 1 := by omega
        have : y1 = x2 := by
          rw [hbeq] at hx2
          rw [hy1, hx2]
        exact hy1_ne_x2 this
      have hb1_lt_am : b + 1 < a + m := by
        have : b + 1 ≤ c := by omega
        have : c < m := hc_range
        omega
      -- From x1 ≠ y1 and y1 ≠ x2, we get x1 = x2 (Bool has only two values)
      have hx1_eq_x2 : x1 = x2 := by
        by_cases hx1_true : x1 = true
        · have hy1_false : y1 = false := by
            by_cases hy1 : y1
            · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
            · exact opposite' hy1
          have hx2_true : x2 = true := by
            by_cases hx2 : x2
            · exact hx2
            · exfalso; apply hy1_ne_x2; rw [hy1_false, opposite' hx2]
          rw [hx1_true, hx2_true]
        · have hx1_false : x1 = false := opposite' hx1_true
          have hy1_true : y1 = true := by
            by_cases hy1 : y1
            · exact hy1
            · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
          have hx2_false : x2 = false := by
            by_cases hx2 : x2
            · exfalso; apply hy1_ne_x2; rw [hy1_true, hx2]
            · exact opposite' hx2
          rw [hx1_false, hx2_false]
      -- From x2 ≠ y2 and x1 = x2, we get y2 ≠ x1, so y2 = y1 (Bool)
      have hy2_eq_y1 : y2 = y1 := by
        by_cases hy2_true : y2 = true
        · have hx1_false : x1 = false := by
            by_cases hx1 : x1
            · exfalso; apply hx2_ne_y2; rw [← hx1_eq_x2, hx1, hy2_true]
            · exact opposite' hx1
          have hy1_true : y1 = true := by
            by_cases hy1 : y1
            · exact hy1
            · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
          rw [hy2_true, hy1_true]
        · have hy2_false : y2 = false := opposite' hy2_true
          have hx1_true : x1 = true := by
            by_cases hx1 : x1
            · exact hx1
            · exfalso; apply hx2_ne_y2; rw [← hx1_eq_x2, opposite' hx1, hy2_false]
          have hy1_false : y1 = false := by
            by_cases hy1 : y1
            · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
            · exact opposite' hy1
          rw [hy2_false, hy1_false]
      by_cases hx1_true : x1 = true
      · -- x1 = true, y1 = false, x2 = true, y2 = false: pattern T,F,T,F
        have hy1_false : y1 = false := by
          by_cases hy1 : y1
          · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
          · exact opposite' hy1
        have hy2_false : y2 = false := by rw [hy2_eq_y1, hy1_false]
        have hx2_true' : x2 = true := by
          rw [← hx1_eq_x2]
          exact hx1_true
        apply hno a (a + 1) b (b + 1) (by omega) ha1_lt_b (by omega) hb1_lt_am
        exact ⟨hx1_true, hy1_false, hx2_true', hy2_false⟩
      · -- x1 = false, y1 = true, x2 = false, y2 = true: pattern F,T,F,T
        -- Use periodicity: apply hno to (a+1, b, b+1, a+m)
        have hx1_false : x1 = false := opposite' hx1_true
        have hy1_true : y1 = true := by
          by_cases hy1 : y1
          · exact hy1
          · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
        have hy2_true : y2 = true := by rw [hy2_eq_y1, hy1_true]
        have hx2_false' : x2 = false := by
          rw [← hx1_eq_x2]
          exact hx1_false
        have ha1_lt_b' : a + 1 < b := by omega
        have hb1_lt_am' : b + 1 < a + m := by
          have : b + 1 ≤ c := by omega
          have : c < m := hc_range
          omega
        have h := hno (a + 1) b (b + 1) (a + m) ha1_lt_b' (by omega) hb1_lt_am' (by omega)
        apply h
        rw [hper a]
        exact ⟨hy1_true, hx2_false', hy2_true, hx1_false⟩
    · -- y1 = x2
      have hy1_eq_x2 : y1 = x2 := by
        by_contra! hne; exact hy1_ne_x2 hne
      by_cases hy2_ne_x3 : y2 ≠ x3
      · -- Case 2: y1 = x2 and y2 ≠ x3, use a, a+1, b+1, c
        have hb1_lt_c : b + 1 < c := by
          by_contra! hle
          have hbeq : c = b + 1 := by omega
          have : y2 = x3 := by
            rw [hbeq] at hx3
            rw [hy2, hx3]
          exact hy2_ne_x3 this
        have hc_lt_am : c < a + m := by
          have : c < m := hc_range
          omega
        by_cases hx1_true : x1 = true
        · -- x1=true, y1=false, y2=true, x3=false: pattern T,F,T,F
          have hy1_false : y1 = false := by
            by_cases hy1 : y1
            · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
            · exact opposite' hy1
          have hy2_true : y2 = true := by
            by_cases hy2 : y2
            · exact hy2
            · exfalso; apply hx2_ne_y2; rw [← hy1_eq_x2, hy1_false, opposite' hy2]
          have hx3_false : x3 = false := by
            by_cases hx3 : x3
            · exfalso; apply hy2_ne_x3; rw [hy2_true, hx3]
            · exact opposite' hx3
          apply hno a (a + 1) (b + 1) c (by omega) (by omega) hb1_lt_c hc_lt_am
          exact ⟨hx1_true, hy1_false, hy2_true, hx3_false⟩
        · -- x1=false, y1=true, y2=false, x3=true: pattern F,T,F,T
          -- Use periodicity: apply hno to (a+1, b+1, c, a+m)
          have hx1_false : x1 = false := opposite' hx1_true
          have hy1_true : y1 = true := by
            by_cases hy1 : y1
            · exact hy1
            · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
          have hy2_false : y2 = false := by
            by_cases hy2 : y2
            · exfalso; apply hx2_ne_y2; rw [← hy1_eq_x2, hy1_true, hy2]
            · exact opposite' hy2
          have hx3_true : x3 = true := by
            by_cases hx3 : x3
            · exact hx3
            · exfalso; apply hy2_ne_x3; rw [hy2_false, opposite' hx3]
          have ha1_lt_b1 : a + 1 < b + 1 := by omega
          have hc_lt_am' : c < a + m := by
            have : c < m := hc_range
            omega
          have h := hno (a + 1) (b + 1) c (a + m) ha1_lt_b1 (by omega) hc_lt_am' (by omega)
          apply h
          rw [hper a]
          exact ⟨hy1_true, hy2_false, hx3_true, hx1_false⟩
      · -- y1 = x2 and y2 = x3, use a, a+1, b+1, c+1
        have hy2_eq_x3 : y2 = x3 := by
          by_contra! hne; exact hy2_ne_x3 hne
        by_cases h_bound : c + 1 < a + m
        · -- c+1 < a+m, apply hno directly
          by_cases hx1_true : x1 = true
          · -- x1=true, y1=false, y2=true, y3=false: pattern T,F,T,F
            have hy1_false : y1 = false := by
              by_cases hy1 : y1
              · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
              · exact opposite' hy1
            have hy2_true : y2 = true := by
              by_cases hy2 : y2
              · exact hy2
              · exfalso; apply hx2_ne_y2; rw [← hy1_eq_x2, hy1_false, opposite' hy2]
            have hy3_false : y3 = false := by
              by_cases hy3 : y3
              · exfalso; apply hx3_ne_y3; rw [← hy2_eq_x3, hy2_true, hy3]
              · exact opposite' hy3
            apply hno a (a + 1) (b + 1) (c + 1) (by omega) (by omega) (by omega) h_bound
            exact ⟨hx1_true, hy1_false, hy2_true, hy3_false⟩
          · -- x1=false, y1=true, y2=false, y3=true: pattern F,T,F,T
            -- Use periodicity: apply hno to (a+1, b+1, c+1, a+m)
            have hx1_false : x1 = false := opposite' hx1_true
            have hy1_true : y1 = true := by
              by_cases hy1 : y1
              · exact hy1
              · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
            have hy2_false : y2 = false := by
              by_cases hy2 : y2
              · exfalso; apply hx2_ne_y2; rw [← hy1_eq_x2, hy1_true, hy2]
              · exact opposite' hy2
            have hy3_true : y3 = true := by
              by_cases hy3 : y3
              · exact hy3
              · exfalso; apply hx3_ne_y3; rw [← hy2_eq_x3, hy2_false, opposite' hy3]
            have ha1_lt_b1 : a + 1 < b + 1 := by omega
            have hc1_lt_am : c + 1 < a + m := by
              have : c + 1 ≤ m := by omega
              omega
            have h := hno (a + 1) (b + 1) (c + 1) (a + m) ha1_lt_b1 (by omega) hc1_lt_am (by omega)
            apply h
            rw [hper a]
            exact ⟨hy1_true, hy2_false, hy3_true, hx1_false⟩
        · -- c+1 ≥ a+m, so c+1 = a+m (since c < m ≤ a+m)
          have h_eq : c + 1 = a + m := by
            have hge : c + 1 ≤ a + m := by
              have : c < m := hc_range
              omega
            have hle : a + m ≤ c + 1 := by omega
            omega
          -- s (c+1) = s m = s 0 = s a (by hper)
          have hy3_eq_x1 : y3 = x1 := by
            rw [hy3, h_eq, hper a, hx1]
          -- From the chain: x1 ≠ y1 = x2 ≠ y2 = x3 ≠ y3
          -- Since Bool has only two values, this forces y3 = y1
          have hy3_eq_y1 : y3 = y1 := by
            by_cases hx1_true : x1 = true
            · have hy1_false : y1 = false := by
                by_cases hy1 : y1
                · exfalso; apply hx1_ne_y1; rw [hx1_true, hy1]
                · exact opposite' hy1
              have hx2_false : x2 = false := by rw [← hy1_eq_x2, hy1_false]
              have hy2_true : y2 = true := by
                by_cases hy2 : y2
                · exact hy2
                · exfalso; apply hx2_ne_y2; rw [hx2_false, opposite' hy2]
              have hx3_true : x3 = true := by rw [← hy2_eq_x3, hy2_true]
              have hy3_false : y3 = false := by
                by_cases hy3 : y3
                · exfalso; apply hx3_ne_y3; rw [hx3_true, hy3]
                · exact opposite' hy3
              rw [hy3_false, hy1_false]
            · have hx1_false : x1 = false := opposite' hx1_true
              have hy1_true : y1 = true := by
                by_cases hy1 : y1
                · exact hy1
                · exfalso; apply hx1_ne_y1; rw [hx1_false, opposite' hy1]
              have hx2_true : x2 = true := by rw [← hy1_eq_x2, hy1_true]
              have hy2_false : y2 = false := by
                by_cases hy2 : y2
                · exfalso; apply hx2_ne_y2; rw [hx2_true, hy2]
                · exact opposite' hy2
              have hx3_false : x3 = false := by rw [← hy2_eq_x3, hy2_false]
              have hy3_true : y3 = true := by
                by_cases hy3 : y3
                · exact hy3
                · exfalso; apply hx3_ne_y3; rw [hx3_false, opposite' hy3]
              rw [hy3_true, hy1_true]
          have hx1_ne_y3 : x1 ≠ y3 := by
            rw [hy3_eq_y1]
            exact hx1_ne_y1
          exact hx1_ne_y3 hy3_eq_x1.symm

/-- A periodic Boolean sequence never changes exactly once along a period. -/
theorem bchg_ne_one (m : ℕ) (s : ℕ → Bool) (hper : ∀ i, s (i + m) = s i) : bchg m s ≠ 1 := by
  intro h
  have hcard : ((Finset.range m).filter fun i => s i ≠ s (i + 1)).card = 1 := by
    dsimp [bchg] at h
    exact h
  rcases Finset.card_eq_one.mp hcard with ⟨c, hc⟩
  have hc_mem_filter : c ∈ (Finset.range m).filter fun i => s i ≠ s (i + 1) := by
    rw [hc]
    exact Finset.mem_singleton.mpr rfl
  have hc_mem_range : c ∈ Finset.range m := Finset.mem_of_mem_filter c hc_mem_filter
  have hc_lt_m : c < m := Finset.mem_range.mp hc_mem_range
  have hc_neq : s c ≠ s (c + 1) :=
    (Finset.mem_filter.mp hc_mem_filter).2
  have h_others : ∀ i ∈ Finset.range m, i ≠ c → s i = s (i + 1) := by
    intro i hi hi_ne
    by_contra hneq
    have hi_mem_filter : i ∈ (Finset.range m).filter fun i => s i ≠ s (i + 1) :=
      Finset.mem_filter.mpr ⟨hi, hneq⟩
    rw [hc] at hi_mem_filter
    exact hi_ne (Finset.mem_singleton.mp hi_mem_filter)
  have h_le_c : ∀ i, i ≤ c → s i = s 0 := by
    intro i hi
    induction' i with k ih
    · rfl
    · have hk_lt_c : k < c := Nat.lt_of_succ_le hi
      have hk_mem_range : k ∈ Finset.range m :=
        Finset.mem_range.mpr (lt_trans hk_lt_c hc_lt_m)
      have hk_ne_c : k ≠ c := Nat.ne_of_lt hk_lt_c
      have hk_eq : s k = s (k + 1) := h_others k hk_mem_range hk_ne_c
      rw [← hk_eq, ih (Nat.le_of_lt hk_lt_c)]
  have h_gt_c : ∀ i, c < i → i ≤ m → s i = s (c + 1) := by
    intro i hi_low hi_high
    induction' i with k ih
    · exfalso; exact Nat.not_lt_zero _ hi_low
    · by_cases hk_eq_c : k = c
      · subst hk_eq_c; rfl
      · have hk_lt_m : k < m := Nat.lt_of_succ_le hi_high
        have hk_mem_range : k ∈ Finset.range m := Finset.mem_range.mpr hk_lt_m
        have hk_ne_c : k ≠ c := hk_eq_c
        have hk_eq : s k = s (k + 1) := h_others k hk_mem_range hk_ne_c
        have hc_lt_k : c < k := by
          by_cases hle : k ≤ c
          · exfalso
            exact hk_ne_c (Nat.le_antisymm hle (Nat.le_of_lt_succ hi_low))
          · exact Nat.lt_of_not_ge hle
        rw [← hk_eq, ih hc_lt_k (Nat.le_of_lt hk_lt_m)]
  have h0 : s 0 = s c := (h_le_c c (le_refl c)).symm
  have hm : s (c + 1) = s m :=
    (h_gt_c m hc_lt_m (le_refl m)).symm
  have h0_ne_hm : s 0 ≠ s m := by
    rw [h0, ← hm]
    exact hc_neq
  have h_eq : s 0 = s m := by
    calc
      s 0 = s (0 + m) := (hper 0).symm
      _ = s m := by simp
  exact h0_ne_hm h_eq

theorem bchg_eq_zero (m : ℕ) (hm : 0 < m) (s : ℕ → Bool) (hper : ∀ i, s (i + m) = s i)
    (h : bchg m s = 0) :
    ∀ i, s i = s 0 := by
  have hfilter : Finset.filter (fun i => s i ≠ s (i + 1)) (Finset.range m) = ∅ :=
    Finset.card_eq_zero.mp h
  have hstep : ∀ i, i < m → s i = s (i + 1) := by
    intro i hi
    have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
    have hnot : ¬ (s i ≠ s (i + 1)) := (Finset.filter_eq_empty_iff.mp hfilter) hmem
    exact not_not.mp hnot
  have h_lt_m : ∀ i, i < m → s i = s 0 := by
    intro i hi
    induction' i with k ih
    · rfl
    · have hk_lt_m : k < m := by omega
      have h_eq : s k = s (k + 1) := hstep k hk_lt_m
      rw [← h_eq, ih hk_lt_m]
  intro i
  induction' i using Nat.strong_induction_on with i ih
  by_cases hi : i < m
  · exact h_lt_m i hi
  · have hm_le_i : m ≤ i := Nat.le_of_not_lt hi
    have hsub_lt : i - m < i := Nat.sub_lt (Nat.lt_of_lt_of_le hm hm_le_i) hm
    have h_per : s (i - m) = s i := by
      have : (i - m) + m = i := Nat.sub_add_cancel hm_le_i
      simpa [this] using (hper (i - m)).symm
    rw [← h_per, ih (i - m) hsub_lt]

/-- Four cyclically ordered vertices of a polygon in cone form never alternate in sign against a
plane through the centre. -/
theorem IsCPoly.no_alt {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (n : E3) (i j k l : ℕ)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hli : l < i + m) :
    ¬ (0 < ⟪n, A i⟫ ∧ ⟪n, A j⟫ ≤ 0 ∧ 0 < ⟪n, A k⟫ ∧ ⟪n, A l⟫ ≤ 0) := by
  intro hsign
  rcases hsign with ⟨hni, hnj, hnk, hnl⟩
  have hcramer := cramer4 (A i) (A j) (A k) (A l) n
  have hpos_ijk : 0 < ⟪cross (A i) (A j), A k⟫ := by
    have ha : 0 < j - i := by omega
    have hab : j - i < k - i := by omega
    have hb : k - i < m := by
      have : l < i + m := hli
      omega
    have h := hA.triple_pos i (j - i) (k - i) ha hab hb
    have hi_j : i + (j - i) = j := by omega
    have hi_k : i + (k - i) = k := by omega
    simpa [hi_j, hi_k] using h
  have hpos_ijl : 0 < ⟪cross (A i) (A j), A l⟫ := by
    have ha : 0 < j - i := by omega
    have hab : j - i < l - i := by omega
    have hb : l - i < m := by
      have : l < i + m := hli
      omega
    have h := hA.triple_pos i (j - i) (l - i) ha hab hb
    have hi_j : i + (j - i) = j := by omega
    have hi_l : i + (l - i) = l := by omega
    simpa [hi_j, hi_l] using h
  have hpos_ikl : 0 < ⟪cross (A i) (A k), A l⟫ := by
    have ha : 0 < k - i := by omega
    have hab : k - i < l - i := by omega
    have hb : l - i < m := by
      have : l < i + m := hli
      omega
    have h := hA.triple_pos i (k - i) (l - i) ha hab hb
    have hi_k : i + (k - i) = k := by omega
    have hi_l : i + (l - i) = l := by omega
    simpa [hi_k, hi_l] using h
  have hpos_jkl : 0 < ⟪cross (A j) (A k), A l⟫ := by
    have ha : 0 < k - j := by omega
    have hab : k - j < l - j := by omega
    have hb : l - j < m := by
      have : l < i + m := hli
      omega
    have h := hA.triple_pos j (k - j) (l - j) ha hab hb
    have hj_k : j + (k - j) = k := by omega
    have hj_l : j + (l - j) = l := by omega
    simpa [hj_k, hj_l] using h
  -- Rewrite inner products using real_inner_comm
  have h_eq : ⟪cross (A j) (A k), A l⟫ * ⟪n, A i⟫ - ⟪cross (A i) (A k), A l⟫ * ⟪n, A j⟫
      + ⟪cross (A i) (A j), A l⟫ * ⟪n, A k⟫ - ⟪cross (A i) (A j), A k⟫ * ⟪n, A l⟫ = 0 := by
    simpa [real_inner_comm] using hcramer
  -- Rewrite as sum of nonnegative terms: (pos*pos) + (pos*(-nonpos)) + (pos*pos) + (pos*(-nonpos))
  -- = (pos*pos) + (-pos*nonpos) + (pos*pos) + (-pos*nonpos) > 0
  have hpos_sum : 0 < ⟪cross (A j) (A k), A l⟫ * ⟪n, A i⟫
      + (-⟪cross (A i) (A k), A l⟫) * ⟪n, A j⟫
      + ⟪cross (A i) (A j), A l⟫ * ⟪n, A k⟫
      + (-⟪cross (A i) (A j), A k⟫) * ⟪n, A l⟫ := by
    have h1 : 0 < ⟪cross (A j) (A k), A l⟫ * ⟪n, A i⟫ := mul_pos hpos_jkl hni
    have h2 : 0 ≤ (-⟪cross (A i) (A k), A l⟫) * ⟪n, A j⟫ := by
      have : ⟪n, A j⟫ ≤ 0 := hnj
      have : 0 ≤ -⟪n, A j⟫ := by linarith
      nlinarith [hpos_ikl]
    have h3 : 0 < ⟪cross (A i) (A j), A l⟫ * ⟪n, A k⟫ := mul_pos hpos_ijl hnk
    have h4 : 0 ≤ (-⟪cross (A i) (A j), A k⟫) * ⟪n, A l⟫ := by
      have : ⟪n, A l⟫ ≤ 0 := hnl
      have : 0 ≤ -⟪n, A l⟫ := by linarith
      nlinarith [hpos_ijk]
    nlinarith
  -- But h_eq says the same expression equals 0, contradiction
  have h_eq_sum : ⟪cross (A j) (A k), A l⟫ * ⟪n, A i⟫
      + (-⟪cross (A i) (A k), A l⟫) * ⟪n, A j⟫
      + ⟪cross (A i) (A j), A l⟫ * ⟪n, A k⟫
      + (-⟪cross (A i) (A j), A k⟫) * ⟪n, A l⟫ = 0 := by
    linarith
  linarith

theorem IsCPoly.chg_le_two {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (n : E3) :
    chg m A n ≤ 2 := by
  unfold chg
  apply bchg_le_two m (fun i => decide (0 < ⟪n, A i⟫))
  · intro i
    simp [hA.periodic i]
  · intro i j k l hij hjk hkl hli hpat
    rcases hpat with ⟨hi, hj, hk, hl⟩
    have hi' : 0 < ⟪n, A i⟫ := by
      simpa [decide_eq_true_iff] using hi
    have hj' : ⟪n, A j⟫ ≤ 0 := by
      have hnj : ¬ 0 < ⟪n, A j⟫ := by
        simpa [decide_eq_false_iff_not] using hj
      linarith
    have hk' : 0 < ⟪n, A k⟫ := by
      simpa [decide_eq_true_iff] using hk
    have hl' : ⟪n, A l⟫ ≤ 0 := by
      have hnl : ¬ 0 < ⟪n, A l⟫ := by
        simpa [decide_eq_false_iff_not] using hl
      linarith
    exact hA.no_alt n i j k l hij hjk hkl hli ⟨hi', hj', hk', hl'⟩

/-- Cramer's rule in `ℝ³`. -/
theorem cramer_decomp (a b c p : E3) :
    ⟪cross a b, c⟫ • p = ⟪cross b c, p⟫ • a + ⟪cross c a, p⟫ • b + ⟪cross a b, p⟫ • c := by
  ext i
  fin_cases i <;>
    simp [cross, PiLp.inner_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      cross_apply, Fin.sum_univ_three] <;> ring

/-- A point of the closed face lies in the cone of a fan triangle from the first vertex. -/
theorem IsCPoly.cone_of_inClosed {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (p : E3)
    (hp : InClosed A p) :
    ∃ (j : ℕ) (a b c : ℝ), 1 ≤ j ∧ j + 1 < m ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      p = a • A 0 + b • A (j) + c • A (j + 1) := by
  set f : ℕ → ℝ := fun k => ⟪cross (A 0) (A k), p⟫ with hf
  have hm3 : 3 ≤ m := hA.three
  have hf1 : 0 ≤ f 1 := by
    dsimp [f]
    simpa using hp 0
  have hfm1 : f (m - 1) ≤ 0 := by
    dsimp [f]
    have h0 : 0 ≤ ⟪cross (A (m - 1)) (A ((m - 1) + 1)), p⟫ := hp (m - 1)
    have h_add : (m - 1) + 1 = m := by omega
    rw [h_add] at h0
    have hm : A m = A 0 := by
      simpa using hA.periodic 0
    rw [hm] at h0
    have hswap := cross_swap (A (m - 1)) (A 0)
    rw [hswap, inner_neg_left]
    exact neg_nonpos.mpr h0
  have h_exists : ∃ k, 1 ≤ k ∧ f (k + 1) ≤ 0 := by
    have hm2 : 1 ≤ m - 2 := by omega
    have hm2_val : f ((m - 2) + 1) ≤ 0 := by
      have : (m - 2) + 1 = m - 1 := by omega
      rw [this]
      exact hfm1
    exact ⟨m - 2, hm2, hm2_val⟩
  let j := Nat.find h_exists
  have hj_spec : 1 ≤ j ∧ f (j + 1) ≤ 0 := Nat.find_spec h_exists
  have hj1 : 1 ≤ j := hj_spec.1
  have hj_f : f (j + 1) ≤ 0 := hj_spec.2
  have hj_min : ∀ k, 1 ≤ k → f (k + 1) ≤ 0 → j ≤ k := by
    intro k hk1 hk2
    exact Nat.find_min' h_exists ⟨hk1, hk2⟩
  have hj_lt_m : j + 1 < m := by
    have hj_le_m2 : j ≤ m - 2 := hj_min (m - 2) (by omega) (by
      have : (m - 2) + 1 = m - 1 := by omega
      rw [this]
      exact hfm1)
    have hle : j + 1 ≤ m - 1 :=
      le_trans (Nat.add_le_add_right hj_le_m2 1) (by omega)
    have hm1_lt_m : m - 1 < m := by omega
    exact lt_of_le_of_lt hle hm1_lt_m
  have hfj_nonneg : 0 ≤ f j := by
    by_cases hj1' : j = 1
    · dsimp [f]
      rw [hj1']
      simpa using hp 0
    · have hj_gt_1 : 1 < j := by omega
      have hj_pred : 1 ≤ j - 1 := by omega
      have h_not : ¬ (f ((j - 1) + 1) ≤ 0) := by
        intro hle
        have hle_j : j ≤ j - 1 := hj_min (j - 1) hj_pred hle
        omega
      have : (j - 1) + 1 = j := by omega
      rw [this] at h_not
      have hpos : 0 < f j := by
        by_contra! h
        apply h_not
        linarith
      exact hpos.le
  have hD_pos : 0 < ⟪cross (A 0) (A j), A (j + 1)⟫ := by
    have hj_pos : 0 < j := by omega
    have hab : j < j + 1 := by omega
    have h := hA.triple_pos 0 j (j + 1) hj_pos hab hj_lt_m
    simpa [zero_add] using h
  set D := ⟪cross (A 0) (A j), A (j + 1)⟫ with hD
  have hDpos : 0 < D := hD_pos
  have hD_ne_zero : D ≠ 0 := by linarith
  have h_cramer := cramer_decomp (A 0) (A j) (A (j + 1)) p
  -- h_cramer: ⟪cross (A 0) (A j), A (j+1)⟫ • p = ...
  -- which is D • p = X • A 0 + Y • A j + Z • A (j+1)
  set X := ⟪cross (A j) (A (j + 1)), p⟫ with hX
  set Y := ⟪cross (A (j + 1)) (A 0), p⟫ with hY
  set Z := f j with hZ
  have hX_nonneg : 0 ≤ X := by
    rw [hX]
    exact hp j
  have hY_nonneg : 0 ≤ Y := by
    rw [hY]
    have hswap := cross_swap (A (j + 1)) (A 0)
    have hswap' : cross (A (j + 1)) (A 0) = -cross (A 0) (A (j + 1)) := by
      calc
        cross (A (j + 1)) (A 0) = -(-cross (A (j + 1)) (A 0)) := by simp
        _ = -cross (A 0) (A (j + 1)) := by rw [← hswap]
    have hY_eq : ⟪cross (A (j + 1)) (A 0), p⟫ = -f (j + 1) := by
      rw [hswap', inner_neg_left]
    rw [hY_eq]
    linarith
  have hZ_nonneg : 0 ≤ Z := by
    rw [hZ]
    dsimp [f]
    exact hfj_nonneg
  have h_eq : D • p = X • A 0 + Y • A j + Z • A (j + 1) := by
    rw [hD]
    exact h_cramer
  refine ⟨j, X / D, Y / D, Z / D, hj1, hj_lt_m, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ X / D
    exact div_nonneg hX_nonneg hDpos.le
  · -- 0 ≤ Y / D
    exact div_nonneg hY_nonneg hDpos.le
  · -- 0 ≤ Z / D
    exact div_nonneg hZ_nonneg hDpos.le
  · -- p = (X/D) • A 0 + (Y/D) • A j + (Z/D) • A (j+1)
    have h_inv : D⁻¹ • (D • p) = p := by
      simp [hD_ne_zero, smul_smul]
    calc
      p = D⁻¹ • (D • p) := by rw [h_inv]
      _ = D⁻¹ • (X • A 0 + Y • A j + Z • A (j + 1)) := by rw [h_eq]
      _ = (D⁻¹ • (X • A 0)) + (D⁻¹ • (Y • A j)) + (D⁻¹ • (Z • A (j + 1))) := by
        simp [smul_add]
      _ = ((D⁻¹ * X) • A 0) + ((D⁻¹ * Y) • A j) + ((D⁻¹ * Z) • A (j + 1)) := by
        simp [smul_smul]
      _ = ((X / D) • A 0) + ((Y / D) • A j) + ((Z / D) • A (j + 1)) := by
        simp [div_eq_mul_inv, mul_comm]

theorem IsCPoly.pos_of_inClosed {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (p : E3)
    (hp : InClosed A p) (hp0 : p ≠ 0) (n : E3) (hn : ∀ i, 0 < ⟪n, A i⟫) : 0 < ⟪n, p⟫ := by
  rcases hA.cone_of_inClosed p hp with ⟨j, a, b, c, hj, hj1, ha, hb, hc, hp_eq⟩
  rw [hp_eq]
  rw [inner_add_right, inner_add_right]
  rw [inner_smul_right, inner_smul_right, inner_smul_right]
  by_cases ha_pos : 0 < a
  · have hpos : 0 < a * ⟪n, A 0⟫ := mul_pos ha_pos (hn 0)
    have hnonneg_b : 0 ≤ b * ⟪n, A j⟫ := mul_nonneg hb (by linarith [hn j])
    have hnonneg_c : 0 ≤ c * ⟪n, A (j + 1)⟫ := mul_nonneg hc (by linarith [hn (j + 1)])
    linarith
  · have ha_zero : a = 0 := by linarith
    by_cases hb_pos : 0 < b
    · have hpos : 0 < b * ⟪n, A j⟫ := mul_pos hb_pos (hn j)
      have hnonneg_a : 0 ≤ a * ⟪n, A 0⟫ := by rw [ha_zero]; simp
      have hnonneg_c : 0 ≤ c * ⟪n, A (j + 1)⟫ := mul_nonneg hc (by linarith [hn (j + 1)])
      linarith
    · have hb_zero : b = 0 := by linarith
      by_cases hc_pos : 0 < c
      · have hpos : 0 < c * ⟪n, A (j + 1)⟫ := mul_pos hc_pos (hn (j + 1))
        have hnonneg_a : 0 ≤ a * ⟪n, A 0⟫ := by rw [ha_zero]; simp
        have hnonneg_b : 0 ≤ b * ⟪n, A j⟫ := by rw [hb_zero]; simp
        linarith
      · have hc_zero : c = 0 := by linarith
        rw [ha_zero, hb_zero, hc_zero] at hp_eq
        simp at hp_eq
        exfalso; exact hp0 hp_eq

theorem IsCPoly.nonpos_of_inClosed {m : ℕ} {A : ℕ → E3} (hA : IsCPoly m A) (p : E3)
    (hp : InClosed A p) (n : E3) (hn : ∀ i, ⟪n, A i⟫ ≤ 0) : ⟪n, p⟫ ≤ 0 := by
  rcases hA.cone_of_inClosed p hp with ⟨j, a, b, c, hj, hj1, ha, hb, hc, hp_eq⟩
  rw [hp_eq]
  simp_rw [inner_add_right, inner_smul_right]
  have h0 : a * ⟪n, A 0⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (hn 0)
  have hj0 : b * ⟪n, A j⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hn j)
  have hj10 : c * ⟪n, A (j + 1)⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (hn (j + 1))
  linarith

theorem chg_mono {m m' : ℕ} {A B : ℕ → E3} (hA : IsCPoly m A) (hB : IsCPoly m' B)
    (hBA : ∀ j, InClosed A (B j)) (n : E3) : chg m' B n ≤ chg m A n := by
  have hmpos : 0 < m := by
    have h3 : 3 ≤ m := hA.three
    omega
  have hperA : ∀ i, (fun i => decide (0 < ⟪n, A i⟫)) (i + m) = (fun i => decide (0 < ⟪n, A i⟫)) i := by
    intro i
    simp [hA.periodic i]
  by_cases hz : chg m A n = 0
  · -- chg m A n = 0: all signs of A agree, propagate to B
    have hall_eq : ∀ i, decide (0 < ⟪n, A i⟫) = decide (0 < ⟪n, A 0⟫) := by
      have := bchg_eq_zero m hmpos (fun i => decide (0 < ⟪n, A i⟫)) hperA hz
      exact this
    by_cases hpos : 0 < ⟪n, A 0⟫
    · -- all ⟪n, A i⟫ > 0, so all ⟪n, B j⟫ > 0
      have hall_pos : ∀ i, 0 < ⟪n, A i⟫ := by
        intro i
        have hdec := hall_eq i
        have htrue : decide (0 < ⟪n, A 0⟫) = true := by exact decide_eq_true hpos
        rw [htrue] at hdec
        exact of_decide_eq_true hdec
      have h_all_B_pos : ∀ j, 0 < ⟪n, B j⟫ := by
        intro j
        have hBj_ne_zero : B j ≠ 0 := by
          have hnorm := hB.unit j
          intro hzero
          rw [hzero, norm_zero] at hnorm
          linarith
        exact hA.pos_of_inClosed (B j) (hBA j) hBj_ne_zero n hall_pos
      have h_all_B_sign_eq : ∀ j, decide (0 < ⟪n, B j⟫) = true := by
        intro j
        exact decide_eq_true (h_all_B_pos j)
      have h_chg_B_zero : chg m' B n = 0 := by
        unfold chg
        have h_bchg_zero : bchg m' (fun j => decide (0 < ⟪n, B j⟫)) = 0 := by
          unfold bchg
          have hfilter : ((Finset.range m').filter fun j => decide (0 < ⟪n, B j⟫) ≠ decide (0 < ⟪n, B (j + 1)⟫)) = ∅ := by
            apply (Finset.filter_eq_empty_iff.mpr ?_)
            intro j hj
            have h_eq : decide (0 < ⟪n, B j⟫) = decide (0 < ⟪n, B (j + 1)⟫) := by
              rw [h_all_B_sign_eq j, h_all_B_sign_eq (j + 1)]
            intro hne
            apply hne
            exact h_eq
          rw [hfilter, Finset.card_empty]
        exact h_bchg_zero
      rw [hz, h_chg_B_zero]
    · -- ⟪n, A 0⟫ ≤ 0, so all ⟪n, A i⟫ ≤ 0, so all ⟪n, B j⟫ ≤ 0
      have hall_nonpos : ∀ i, ⟪n, A i⟫ ≤ 0 := by
        intro i
        have hdec := hall_eq i
        have hfalse : decide (0 < ⟪n, A 0⟫) = false := by
          exact decide_eq_false hpos
        rw [hfalse] at hdec
        exact le_of_not_gt (of_decide_eq_false hdec)
      have h_all_B_nonpos : ∀ j, ⟪n, B j⟫ ≤ 0 := by
        intro j
        exact hA.nonpos_of_inClosed (B j) (hBA j) n hall_nonpos
      have h_all_B_sign_eq : ∀ j, decide (0 < ⟪n, B j⟫) = false := by
        intro j
        apply decide_eq_false
        exact not_lt.mpr (h_all_B_nonpos j)
      have h_chg_B_zero : chg m' B n = 0 := by
        unfold chg
        have h_bchg_zero : bchg m' (fun j => decide (0 < ⟪n, B j⟫)) = 0 := by
          unfold bchg
          have hfilter : ((Finset.range m').filter fun j => decide (0 < ⟪n, B j⟫) ≠ decide (0 < ⟪n, B (j + 1)⟫)) = ∅ := by
            apply (Finset.filter_eq_empty_iff.mpr ?_)
            intro j hj
            have h_eq : decide (0 < ⟪n, B j⟫) = decide (0 < ⟪n, B (j + 1)⟫) := by
              rw [h_all_B_sign_eq j, h_all_B_sign_eq (j + 1)]
            intro hne
            apply hne
            exact h_eq
          rw [hfilter, Finset.card_empty]
        exact h_bchg_zero
      rw [hz, h_chg_B_zero]
  · -- chg m A n ≠ 0, so chg m A n ≥ 2 (since ≠ 1) and chg m' B n ≤ 2
    have h_ne_one : chg m A n ≠ 1 := by
      have := bchg_ne_one m (fun i => decide (0 < ⟪n, A i⟫)) hperA
      exact this
    have h_ge_two : 2 ≤ chg m A n := by
      omega
    have h_B_le_two : chg m' B n ≤ 2 := hB.chg_le_two n
    exact Nat.le_trans h_B_le_two h_ge_two

theorem perim_nonneg (m : ℕ) (A : ℕ → E3) : 0 ≤ perim m A :=
  Finset.sum_nonneg fun _ _ => (sdist_mem_Icc _ _).1

/-- Perimeter monotonicity: a polygon in cone form whose vertices lie in the closed face of
another has at most its perimeter. -/
theorem perim_mono {m m' : ℕ} {A B : ℕ → E3} (hA : IsCPoly m A) (hB : IsCPoly m' B)
    (hBA : ∀ j, InClosed A (B j)) : perim m' B ≤ perim m A := by
  have hle : ∫⁻ n, cnt m' B n ≤ ∫⁻ n, cnt m A n := by
    refine lintegral_mono fun n => ?_
    rw [cnt_eq, cnt_eq]
    split_ifs
    · exact Nat.cast_le.mpr (chg_mono hA hB hBA n)
    · exact le_rfl
  rw [lintegral_cnt m' B hB.unit, lintegral_cnt m A hA.unit,
    ENNReal.ofReal_le_ofReal_iff (by have := perim_nonneg m A; positivity)] at hle
  linarith

end Tammes15.Geom
