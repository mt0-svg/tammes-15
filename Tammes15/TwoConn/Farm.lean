import Tammes15.TwoConn.Defs
import Tammes15.Draw.Frame
import Tammes15.Local41.Rotation
import Tammes15.Trigrows.Points
import Tammes15.Rattlers.Hex
import Tammes15.Fans.Cone

/-!
# Self-contained lemmas of Corollary twoconn by the convex hull

Self-contained statements of the proof (paper, Section 3, Corollary twoconn and Remark
routeC). Groups:

* corners and determinants at a vertex (`inner_cross_tdir` to `sameRay_of_ocorner_eq_zero`);
* Cramer's rule and strict convexity (`norm_lt_one_of_comb`, `cramer3`);
* the link of a vertex, a finite set of the plane `v⊥` with `0` strictly inside
  (`stereo_identity` to `gift_wrap`, with the cut of the gift wrapping step);
* vertex facts of an angular rotation system with corners in `(0, π)` (`contact_exposed` to
  `face_period_ge_three`);
* the hemisphere lemma for a walk turning left with total turning below `2π` (`pole_sdist` to
  `walk_axis`, with the cut of `polygon_hemisphere`);
* winding numbers of closed walks about an axis (`exists_generic` to `injective_of_winding_one`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical
open Fin.NatCast

/-! ## Corners and determinants at a vertex -/

theorem inner_cross_tdir (v a b : E3) :
    ⟪v, cross (tdir v a) (tdir v b)⟫ = ⟪cross v a, b⟫ := by
  set α := ⟪v, a⟫ with hα
  set β := ⟪v, b⟫ with hβ
  have htdir_a : tdir v a = a - α • v := rfl
  have htdir_b : tdir v b = b - β • v := rfl
  rw [htdir_a, htdir_b]
  have cross_add_left (a b c : E3) : cross (a + b) c = cross a c + cross b c := by
    dsimp [cross]
    simp [map_add]
  have cross_sub_left (a b c : E3) : cross (a - b) c = cross a c - cross b c := by
    dsimp [cross]
    simp [map_sub]
  have cross_sub_right (a b c : E3) : cross a (b - c) = cross a b - cross a c := by
    dsimp [cross]
    simp [map_sub]
  calc
    ⟪v, cross (a - α • v) (b - β • v)⟫
        = ⟪v, cross a (b - β • v) - cross (α • v) (b - β • v)⟫ := by rw [cross_sub_left]
    _ = ⟪v, (cross a b - cross a (β • v)) - (cross (α • v) b - cross (α • v) (β • v))⟫ := by
      rw [cross_sub_right, cross_sub_right]
    _ = ⟪v, cross a b - β • cross a v - α • cross v b + (α * β) • cross v v⟫ := by
      simp [cross_smul_left, cross_smul_right, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_smul]
    _ = ⟪v, cross a b⟫ - ⟪v, β • cross a v⟫ - ⟪v, α • cross v b⟫ + ⟪v, (α * β) • cross v v⟫ := by
      simp [inner_sub_right, inner_add_right]
    _ = ⟪v, cross a b⟫ - β * ⟪v, cross a v⟫ - α * ⟪v, cross v b⟫ + (α * β) * ⟪v, cross v v⟫ := by
      simp [inner_smul_right]
    _ = ⟪v, cross a b⟫ := by
      simp [inner_cross_self v v, inner_cross_self v b, inner_cross_right_self a v]
    _ = ⟪b, cross v a⟫ := by
      rw [inner_cross_perm v a b, inner_cross_perm a b v]
    _ = ⟪cross v a, b⟫ := by rw [real_inner_comm]

open Complex in
theorem ocorner_pos_lt_pi_iff (v a b : E3) :
    (0 < ocorner v a b ∧ ocorner v a b < π) ↔ 0 < ⟪cross v a, b⟫ := by
  set w : ℂ := ⟨⟪tdir v a, tdir v b⟫, ⟪v, cross (tdir v a) (tdir v b)⟫⟩ with hw_def
  have hw_im : w.im = ⟪cross v a, b⟫ := by
    rw [hw_def]
    simp [inner_cross_tdir]
  have h_arg_mem : arg w ∈ Set.Ioc (-π) π := arg_mem_Ioc w
  have h_neg_pi_lt : -π < arg w := h_arg_mem.1
  have h_le_pi : arg w ≤ π := h_arg_mem.2
  constructor
  · -- forward direction: (0 < ocorner v a b ∧ ocorner v a b < π) → 0 < ⟪cross v a, b⟫
    intro ⟨h_pos, h_lt_pi⟩
    rw [← hw_im]
    by_contra! h_notpos
    -- h_notpos : w.im ≤ 0
    have h_arg_nonpos : arg w ≤ 0 := by
      by_contra! h_pos_arg
      -- arg w > 0, so w.im ≥ 0 by arg_nonneg_iff
      have h_im_nonneg : 0 ≤ w.im := (arg_nonneg_iff.mp h_pos_arg.le)
      have h_im_zero : w.im = 0 := by linarith
      -- w.im = 0, so arg w ∈ {0, π}
      rcases em (0 ≤ w.re) with (h_re_nonneg | h_re_neg)
      · -- w.re ≥ 0 → arg w = 0
        have h_arg_zero : arg w = 0 := (arg_eq_zero_iff.mpr ⟨h_re_nonneg, h_im_zero⟩)
        have h_ocorner_zero : ocorner v a b = 0 := by
          dsimp [Tammes15.ocorner, w]
          rw [h_arg_zero]
          simp
        rw [h_ocorner_zero] at h_pos
        linarith
      · -- w.re < 0 → arg w = π
        have h_re_lt : w.re < 0 := by linarith
        have h_arg_pi : arg w = π := (arg_eq_pi_iff.mpr ⟨h_re_lt, h_im_zero⟩)
        have h_ocorner_pi : ocorner v a b = π := by
          dsimp [Tammes15.ocorner, w]
          rw [h_arg_pi]
          rw [toIcoMod_eq_self Real.two_pi_pos]
          constructor <;> linarith
        rw [h_ocorner_pi] at h_lt_pi
        linarith
    -- Now arg w ≤ 0. Either arg w = 0 or arg w < 0.
    rcases lt_or_eq_of_le h_arg_nonpos with (h_arg_neg | h_arg_zero)
    · -- arg w < 0, so toIcoMod two_pi_pos 0 (arg w) = arg w + 2π
      have h_ocorner_eq : ocorner v a b = arg w + 2 * π := by
        dsimp [Tammes15.ocorner, w]
        apply (toIcoMod_eq_iff Real.two_pi_pos).mpr
        constructor
        · -- arg w + 2π ∈ Set.Ico 0 (0 + 2π)
          constructor
          · linarith
          · linarith
        · -- ∃ z, arg w = (arg w + 2π) + z • (2π)
          use -1
          ring
      rw [h_ocorner_eq] at h_lt_pi
      -- h_lt_pi : arg w + 2π < π → arg w < -π, contradicting h_neg_pi_lt
      linarith
    · -- arg w = 0
      have h_ocorner_zero : ocorner v a b = 0 := by
        dsimp [Tammes15.ocorner, w]
        rw [h_arg_zero]
        simp
      rw [h_ocorner_zero] at h_pos
      linarith
  · -- reverse direction: 0 < ⟪cross v a, b⟫ → (0 < ocorner v a b ∧ ocorner v a b < π)
    intro h_pos_im
    rw [← hw_im] at h_pos_im
    have h_arg_pos : 0 < arg w := by
      by_contra! h_notpos
      -- h_notpos : arg w ≤ 0
      have h_im_zero : w.im = 0 := by
        have h_cases : arg w < 0 ∨ arg w = 0 := lt_or_eq_of_le h_notpos
        rcases h_cases with (h_lt | h_eq)
        · -- arg w < 0 → w.im < 0 (by arg_neg_iff)
          have h_im_neg : w.im < 0 := (arg_neg_iff.mp h_lt)
          linarith
        · -- arg w = 0 → w.im = 0 (by arg_eq_zero_iff)
          exact (arg_eq_zero_iff.mp h_eq).2
      rw [h_im_zero] at h_pos_im
      linarith
    have h_arg_lt_pi : arg w < π := by
      by_contra! h_not_lt
      -- h_not_lt : arg w ≥ π, but h_le_pi gives arg w ≤ π, so arg w = π
      have h_arg_pi : arg w = π := by linarith
      have h_im_zero : w.im = 0 := (arg_eq_pi_iff.mp h_arg_pi).2
      rw [h_im_zero] at h_pos_im
      linarith
    -- Now arg w ∈ (0, π) ⊂ [0, 2π), so toIcoMod ... = arg w
    have h_arg_mem_Ico : arg w ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      constructor
      · linarith
      · linarith
    have h_ocorner_eq : ocorner v a b = arg w := by
      dsimp [Tammes15.ocorner, w]
      exact (toIcoMod_eq_self Real.two_pi_pos).mpr h_arg_mem_Ico
    rw [h_ocorner_eq]
    exact ⟨h_arg_pos, h_arg_lt_pi⟩

theorem ocorner_add (v a b c : E3) (hv : ‖v‖ = 1) (ha : tdir v a ≠ 0) (hb : tdir v b ≠ 0)
    (hc : tdir v c ≠ 0) :
    ocorner v a c = toIcoMod two_pi_pos 0 (ocorner v a b + ocorner v b c) := by
  obtain ⟨e, he_norm, he_inner⟩ := exists_unit_orthogonal v
  have h_ab := ocorner_eq_fangle_sub v e a b hv he_norm he_inner ha hb
  have h_bc := ocorner_eq_fangle_sub v e b c hv he_norm he_inner hb hc
  have h_ac := ocorner_eq_fangle_sub v e a c hv he_norm he_inner ha hc
  rw [h_ab, h_bc, h_ac]
  set p := (2 * π : ℝ) with hp
  have hp_pos : 0 < p := by
    dsimp [p]
    exact Real.two_pi_pos
  set x := fangle v e c with hx
  set y := fangle v e b with hy
  set z := fangle v e a with hz
  have h_diff : (x - z) - (toIcoMod hp_pos 0 (y - z) + toIcoMod hp_pos 0 (x - y)) =
      (toIcoDiv hp_pos 0 (y - z) + toIcoDiv hp_pos 0 (x - y)) • p := by
    calc
      (x - z) - (toIcoMod hp_pos 0 (y - z) + toIcoMod hp_pos 0 (x - y))
          = ((y - z) - toIcoMod hp_pos 0 (y - z)) + ((x - y) - toIcoMod hp_pos 0 (x - y)) := by ring
      _ = (toIcoDiv hp_pos 0 (y - z)) • p + (toIcoDiv hp_pos 0 (x - y)) • p := by
        simp [self_sub_toIcoMod hp_pos]
      _ = (toIcoDiv hp_pos 0 (y - z) + toIcoDiv hp_pos 0 (x - y)) • p := by rw [add_smul]
  apply ((toIcoMod_inj (c := 0) hp_pos).mpr)
  rw [AddCommGroup.modEq_iff_zsmul']
  use -(toIcoDiv hp_pos 0 (y - z) + toIcoDiv hp_pos 0 (x - y))
  calc
    toIcoMod hp_pos 0 (y - z) + toIcoMod hp_pos 0 (x - y) - (x - z)
        = -((x - z) - (toIcoMod hp_pos 0 (y - z) + toIcoMod hp_pos 0 (x - y))) := by ring
    _ = -((toIcoDiv hp_pos 0 (y - z) + toIcoDiv hp_pos 0 (x - y)) • p) := by rw [h_diff]
    _ = (-(toIcoDiv hp_pos 0 (y - z) + toIcoDiv hp_pos 0 (x - y))) • p := by
      ring

theorem ocorner_eq_zero_of_sameRay (v a b : E3) (h : SameRay ℝ (tdir v a) (tdir v b)) :
    ocorner v a b = 0 := by
  rcases h with (hx | hy | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · -- tdir v a = 0
    have hx' : tdir v a = 0 := hx
    dsimp [ocorner]
    have hcross : cross (0 : E3) (tdir v b) = 0 := by
      simp [cross]
    rw [hx', hcross]
    simp
    have harg : ({ re := 0, im := 0 } : ℂ).arg = (0 : ℝ) :=
      Complex.arg_zero
    rw [harg]
    have hmem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      refine ⟨by norm_num, ?_⟩
      linarith [two_pi_pos]
    exact (toIcoMod_eq_self two_pi_pos).mpr hmem
  · -- tdir v b = 0
    have hy' : tdir v b = 0 := hy
    dsimp [ocorner]
    have hcross : cross (tdir v a) (0 : E3) = 0 := by
      simp [cross]
    rw [hy', hcross]
    simp
    have harg : ({ re := 0, im := 0 } : ℂ).arg = (0 : ℝ) :=
      Complex.arg_zero
    rw [harg]
    have hmem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      refine ⟨by norm_num, ?_⟩
      linarith [two_pi_pos]
    exact (toIcoMod_eq_self two_pi_pos).mpr hmem
  · -- r₁ • tdir v a = r₂ • tdir v b
    have h_ratio_pos : 0 ≤ r₁ / r₂ := by
      positivity
    have h_eq : tdir v b = (r₁ / r₂) • tdir v a := by
      calc
        tdir v b = (r₂⁻¹) • (r₂ • tdir v b) := by
          simp [hr₂.ne.symm]
        _ = (r₂⁻¹) • (r₁ • tdir v a) := by rw [← h]
        _ = ((r₂⁻¹) * r₁) • tdir v a := by simp [smul_smul]
        _ = (r₁ / r₂) • tdir v a := by ring_nf
    dsimp [ocorner]
    rw [h_eq]
    have hcross : cross (tdir v a) ((r₁ / r₂) • tdir v a) = 0 := by
      simp [cross]
    rw [hcross]
    have hinner_zero : ⟪v, (0 : E3)⟫ = (0 : ℝ) := by simp
    rw [hinner_zero]
    have hinner_nonneg : 0 ≤ ⟪tdir v a, (r₁ / r₂) • tdir v a⟫ := by
      have hinner_eq : ⟪tdir v a, (r₁ / r₂) • tdir v a⟫ = (r₁ / r₂) * ⟪tdir v a, tdir v a⟫ := by
        simp [inner_smul_right]
      rw [hinner_eq]
      have h_inner_nonneg' : 0 ≤ ⟪tdir v a, tdir v a⟫ :=
        inner_self_nonneg (𝕜 := ℝ) (x := tdir v a)
      nlinarith [h_ratio_pos, h_inner_nonneg']
    have h_complex_arg : Complex.arg (⟨⟪tdir v a, (r₁ / r₂) • tdir v a⟫, (0 : ℝ)⟩ : ℂ) = (0 : ℝ) := by
      rw [Complex.arg_eq_zero_iff]
      constructor
      · exact hinner_nonneg
      · simp
    rw [h_complex_arg]
    have hmem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by
      refine ⟨by norm_num, ?_⟩
      linarith [two_pi_pos]
    exact (toIcoMod_eq_self two_pi_pos).mpr hmem

open scoped Matrix in
/-- A vector with zero cross product with a unit vector `v` is a multiple of `v`. -/
theorem cross_eq_smul_of_cross_eq_zero (v w : E3) (hv : ‖v‖ = 1) (h_cross : cross v w = 0) :
    w = ⟪v, w⟫ • v := by
  -- First, from cross v w = 0, we get ofLp v ⨯₃ ofLp w = 0
  have h_cross_ofLp : WithLp.ofLp v ⨯₃ WithLp.ofLp w = 0 := by
    have h' := congrArg WithLp.ofLp h_cross
    simpa [cross] using h'
  -- Now use the vector triple product on the ofLp level
  have h_triple_raw := cross_cross_eq_smul_sub_smul' (WithLp.ofLp v) (WithLp.ofLp v) (WithLp.ofLp w)
  rw [h_cross_ofLp] at h_triple_raw
  simp at h_triple_raw
  -- Convert dot products to inner products
  have h_dot_vw : WithLp.ofLp v ⬝ᵥ WithLp.ofLp w = ⟪v, w⟫ := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := v) (y := w)
    rw [h]
    simp [dotProduct, mul_comm]
  have h_dot_vv : WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ⟪v, v⟫ := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := v) (y := v)
    rw [h]
    simp [dotProduct, sq]
  have h_inner_vv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hv, mul_one]
  rw [h_dot_vw, h_dot_vv, h_inner_vv] at h_triple_raw
  -- h_triple_raw : 0 = ⟪v, w⟫ • v.ofLp - 1 • w.ofLp
  have h_eq : WithLp.ofLp w = ⟪v, w⟫ • WithLp.ofLp v := by
    ext i
    have h := congrFun h_triple_raw i
    simp at h
    simp
    linarith
  apply_fun WithLp.toLp (p := 2) at h_eq
  simpa using h_eq

open scoped Matrix in
/-- The cross product of two vectors orthogonal to `v` is parallel to `v`. -/
theorem cross_cross_eq_zero_of_orthogonal (v ta tb : E3) (h_orth_ta : ⟪v, ta⟫ = 0)
    (h_orth_tb : ⟪v, tb⟫ = 0) : cross v (cross ta tb) = 0 := by
  have h_dot_vw_eq : WithLp.ofLp v ⬝ᵥ WithLp.ofLp tb = ⟪v, tb⟫ := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := v) (y := tb)
    rw [h]
    simp [dotProduct, mul_comm]
  have h_dot_tv_eq : WithLp.ofLp ta ⬝ᵥ WithLp.ofLp v = ⟪ta, v⟫ := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := ta) (y := v)
    rw [h]
    simp [dotProduct, mul_comm]
  have h_dot1 : WithLp.ofLp v ⬝ᵥ WithLp.ofLp tb = 0 := by
    rw [h_dot_vw_eq, h_orth_tb]
  have h_dot2 : WithLp.ofLp ta ⬝ᵥ WithLp.ofLp v = 0 := by
    rw [h_dot_tv_eq]
    rw [real_inner_comm]
    exact h_orth_ta
  have h_triple : WithLp.ofLp v ⨯₃ (WithLp.ofLp ta ⨯₃ WithLp.ofLp tb) = 0 := by
    rw [cross_cross_eq_smul_sub_smul' (WithLp.ofLp v) (WithLp.ofLp ta) (WithLp.ofLp tb)]
    rw [h_dot1, h_dot2]
    simp
  have h_ofLp : WithLp.ofLp (cross v (cross ta tb)) = WithLp.ofLp v ⨯₃ (WithLp.ofLp ta ⨯₃ WithLp.ofLp tb) := by
    simp [cross]
  have h_zero : WithLp.ofLp (cross v (cross ta tb)) = 0 := by
    rw [h_ofLp, h_triple]
  apply_fun WithLp.toLp (p := 2) at h_zero
  simpa using h_zero

theorem sameRay_of_ocorner_eq_zero (v a b : E3) (hv : ‖v‖ = 1) (h : ocorner v a b = 0) :
    SameRay ℝ (tdir v a) (tdir v b) := by
  let ta := tdir v a
  let tb := tdir v b
  have hta : ⟪v, ta⟫ = 0 := by
    dsimp [ta, tdir]
    rw [inner_sub_right, inner_smul_right]
    have hinner : ⟪v, v⟫ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hv, mul_one]
    rw [hinner, mul_one, sub_self]
  have htb : ⟪v, tb⟫ = 0 := by
    dsimp [tb, tdir]
    rw [inner_sub_right, inner_smul_right]
    have hinner : ⟪v, v⟫ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hv, mul_one]
    rw [hinner, mul_one, sub_self]
  -- from occurs = 0, deduce arg = 0
  have h_arg_zero : Complex.arg (⟨⟪ta, tb⟫, ⟪v, cross ta tb⟫⟩ : ℂ) = 0 := by
    dsimp [ocorner] at h
    set w := Complex.arg (⟨⟪ta, tb⟫, ⟪v, cross ta tb⟫⟩ : ℂ) with hw
    have hw_range : w ∈ Set.Ioc (-π) π := Complex.arg_mem_Ioc _
    have h_mod : toIcoMod two_pi_pos 0 w = 0 := h
    have hw_eq : w = 0 := by
      rcases (toIcoMod_eq_iff (p := 2*π) two_pi_pos (a := 0) (b := w) (c := 0)).mp h_mod with ⟨_, z, hz⟩
      have hw_eq' : w = (z : ℝ) * (2*π) := by
        simpa [add_comm] using hz
      rcases hw_range with ⟨hwl, hwr⟩
      rw [hw_eq'] at hwl hwr
      have h2π_pos : 0 < 2*π := two_pi_pos
      have hzl : -(1/2 : ℝ) < (z : ℝ) := by nlinarith
      have hzr : (z : ℝ) ≤ 1/2 := by nlinarith
      have hz0 : z = 0 := by
        by_contra! H
        by_cases hz_pos : (0 : ℤ) < z
        · have hz_ge_one : (1 : ℤ) ≤ z := by omega
          have hz_ge_one' : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge_one
          linarith
        · have hz_le_neg_one : z ≤ (-1 : ℤ) := by omega
          have hz_le_neg_one' : (z : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hz_le_neg_one
          linarith
      rw [hw_eq', hz0, Int.cast_zero, zero_mul]
    rw [hw_eq]
  -- Now from arg = 0, get conditions on inner products
  have h_arg_cond := (Complex.arg_eq_zero_iff).mp h_arg_zero
  rcases h_arg_cond with ⟨h_inner_nonneg, h_cross_zero⟩
  have h_inner_nonneg' : 0 ≤ ⟪ta, tb⟫ := by
    simpa using h_inner_nonneg
  have h_cross_zero' : ⟪v, cross ta tb⟫ = 0 := by
    simpa using h_cross_zero
  -- Now we need to show cross ta tb = 0
  have h_cross_v_zero : cross v (cross ta tb) = 0 :=
    cross_cross_eq_zero_of_orthogonal v ta tb hta htb
  -- From cross v (cross ta tb) = 0 and ‖v‖ = 1, deduce cross ta tb = ⟪v, cross ta tb⟫ • v
  have h_parallel : cross ta tb = ⟪v, cross ta tb⟫ • v :=
    cross_eq_smul_of_cross_eq_zero v (cross ta tb) hv h_cross_v_zero
  -- Since ⟪v, cross ta tb⟫ = 0, we get cross ta tb = 0
  have h_cross_zero_vec : cross ta tb = 0 := by
    rw [h_parallel, h_cross_zero', zero_smul]
  -- Now use norm_cross_sq
  have h_norm_cross : ‖cross ta tb‖ ^ 2 = ‖ta‖ ^ 2 * ‖tb‖ ^ 2 - ⟪ta, tb⟫ ^ 2 := by
    rw [norm_cross_sq]
  rw [h_cross_zero_vec] at h_norm_cross
  simp at h_norm_cross
  -- h_norm_cross : 0 = ‖ta‖ ^ 2 * ‖tb‖ ^ 2 - ⟪ta, tb⟫ ^ 2
  -- Hence ⟪ta, tb⟫ ^ 2 = ‖ta‖ ^ 2 * ‖tb‖ ^ 2
  have h_inner_sq_eq : ⟪ta, tb⟫ ^ 2 = ‖ta‖ ^ 2 * ‖tb‖ ^ 2 := by
    linarith
  -- Since ⟪ta, tb⟫ ≥ 0, we have ⟪ta, tb⟫ = ‖ta‖ * ‖tb‖
  have h_inner_eq : ⟪ta, tb⟫ = ‖ta‖ * ‖tb‖ := by
    have h_nonneg_norm : 0 ≤ ‖ta‖ * ‖tb‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  -- Now use inner_eq_norm_mul_iff_real to get ‖tb‖ • ta = ‖ta‖ • tb
  have h_smul_eq : ‖tb‖ • ta = ‖ta‖ • tb :=
    (inner_eq_norm_mul_iff_real (x := ta) (y := tb)).mp h_inner_eq
  -- Now use sameRay_iff_norm_smul_eq
  exact (sameRay_iff_norm_smul_eq (x := ta) (y := tb)).mpr h_smul_eq.symm

/-! ## Cramer's rule and strict convexity -/

theorem norm_lt_one_of_comb (p q r : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hpq : p ≠ q) (l m n : ℝ) (hl : 0 < l) (hm : 0 < m) (hn : 0 ≤ n) (hs : l + m + n = 1) :
    ‖l • p + m • q + n • r‖ < 1 := by
  have hpq_inner : ⟪p, q⟫ < 1 := by
    have := (inner_lt_one_iff_real_of_norm_eq_one hp hq).mpr hpq
    exact this
  have h_norm_sq_lt : ‖l • p + m • q‖ ^ 2 < (l + m) ^ 2 := by
    calc
      ‖l • p + m • q‖ ^ 2 = ‖l • p‖ ^ 2 + 2 * inner ℝ (l • p) (m • q) + ‖m • q‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = (|l| * ‖p‖) ^ 2 + 2 * (l * m * ⟪p, q⟫) + (|m| * ‖q‖) ^ 2 := by
        simp [norm_smul, inner_smul_left, inner_smul_right, mul_left_comm, mul_assoc]
      _ = (l * ‖p‖) ^ 2 + 2 * (l * m * ⟪p, q⟫) + (m * ‖q‖) ^ 2 := by
        simp [abs_of_pos hl, abs_of_pos hm]
      _ = (l ^ 2 * ‖p‖ ^ 2) + 2 * (l * m * ⟪p, q⟫) + (m ^ 2 * ‖q‖ ^ 2) := by ring
      _ = l ^ 2 + 2 * (l * m * ⟪p, q⟫) + m ^ 2 := by
        simp [hp, hq]
      _ = l ^ 2 + 2 * l * m * ⟪p, q⟫ + m ^ 2 := by ring
      _ < l ^ 2 + 2 * l * m * 1 + m ^ 2 := by
        have hpos_lm : 0 < l * m := mul_pos hl hm
        have h_mul : l * m * ⟪p, q⟫ < l * m * 1 :=
          mul_lt_mul_of_pos_left hpq_inner hpos_lm
        have hpos_2lm : 0 < 2 * (l * m) := by nlinarith
        have h_two_mul : 2 * (l * m) * ⟪p, q⟫ < 2 * (l * m) * 1 :=
          mul_lt_mul_of_pos_left hpq_inner hpos_2lm
        nlinarith
      _ = (l + m) ^ 2 := by ring
  have h_norm_lt : ‖l • p + m • q‖ < l + m := by
    have h_nonneg_norm : 0 ≤ ‖l • p + m • q‖ := norm_nonneg _
    have h_nonneg_sum : 0 ≤ l + m := by linarith
    have h_abs_lt : |‖l • p + m • q‖| < l + m :=
      abs_lt_of_sq_lt_sq h_norm_sq_lt h_nonneg_sum
    rwa [abs_of_nonneg h_nonneg_norm] at h_abs_lt
  calc
    ‖l • p + m • q + n • r‖ ≤ ‖l • p + m • q‖ + ‖n • r‖ := norm_add_le _ _
    _ < (l + m) + ‖n • r‖ := by
      nlinarith
    _ = (l + m) + (n * ‖r‖) := by
      rw [norm_smul_of_nonneg hn]
    _ = (l + m) + (n * 1) := by rw [hr]
    _ = (l + m) + n := by ring
    _ = 1 := by linarith

/-- Cramer's identity in `ℝ³`. -/
theorem cramer_smul (a b c y : E3) :
    ⟪cross a b, c⟫ • y = ⟪cross y b, c⟫ • a + ⟪cross a y, c⟫ • b + ⟪cross a b, y⟫ • c := by
  ext i
  fin_cases i <;> simp [cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

theorem cramer3 (a b c y : E3) (h : ⟪cross a b, c⟫ ≠ 0) :
    y = (⟪cross y b, c⟫ / ⟪cross a b, c⟫) • a + (⟪cross a y, c⟫ / ⟪cross a b, c⟫) • b +
      (⟪cross a b, y⟫ / ⟪cross a b, c⟫) • c := by
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, mul_smul, ← smul_add,
    ← smul_add, ← cramer_smul a b c y, smul_smul, inv_mul_cancel₀ h, one_smul]

/-! ## The link of a vertex: a finite set of the plane `v⊥` with `0` strictly inside -/

theorem stereo_identity (v y N : E3) (hy : ⟪v, y⟫ ≠ 1) :
    ⟪y, N⟫ - ⟪v, N⟫ = (1 - ⟪v, y⟫) * (⟪(1 - ⟪v, y⟫)⁻¹ • tdir v y, N⟫ - ⟪v, N⟫) := by
  set u := 1 - ⟪v, y⟫ with hu
  have hu_ne_zero : u ≠ 0 := sub_ne_zero.mpr hy.symm
  calc
    ⟪y, N⟫ - ⟪v, N⟫ = u * (u⁻¹ * (⟪y, N⟫ - ⟪v, y⟫ * ⟪v, N⟫) - ⟪v, N⟫) := by
      field_simp [hu_ne_zero]
      ring
    _ = u * (⟪u⁻¹ • tdir v y, N⟫ - ⟪v, N⟫) := by
      simp [tdir, u, inner_smul_left, inner_sub_left]
    _ = (1 - ⟪v, y⟫) * (⟪(1 - ⟪v, y⟫)⁻¹ • tdir v y, N⟫ - ⟪v, N⟫) := by simp [u]

theorem det_pos_trans (v n a b q : E3) (ha : ⟪v, a⟫ = 0) (hb : ⟪v, b⟫ = 0) (hq : ⟪v, q⟫ = 0)
    (han : 0 < ⟪a, n⟫) (hbn : 0 < ⟪b, n⟫) (hqn : 0 < ⟪q, n⟫)
    (hab : 0 < ⟪cross v a, b⟫) (hbq : 0 < ⟪cross v b, q⟫) : 0 < ⟪cross v a, q⟫ := by
  have hv : v ≠ 0 := by
    rintro rfl
    have h0 : cross 0 a = 0 := by
      ext i
      fin_cases i <;> simp [cross, crossProduct]
    rw [h0, inner_zero_left] at hab
    exact lt_irrefl _ hab
  have K := cramer_smul a b q v
  have hvv : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv
  have hK1 := congrArg (fun w => ⟪v, w⟫) K
  simp only [real_inner_smul_right, inner_add_right, ha, hb, hq, mul_zero, add_zero] at hK1
  have hD : ⟪cross a b, q⟫ = 0 := by
    rcases mul_eq_zero.mp hK1 with h | h
    · exact h
    · exact absurd h hvv.ne'
  rw [hD, zero_smul] at K
  have hK2 := congrArg (fun w => ⟪w, n⟫) K
  simp only [inner_zero_left, inner_add_left, real_inner_smul_left] at hK2
  have h1 : ⟪cross a v, q⟫ = -⟪cross v a, q⟫ := by
    simp [cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  have h2 : ⟪cross a b, v⟫ = ⟪cross v a, b⟫ := by
    simp [cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  rw [h1, h2] at hK2
  have hpos : 0 < ⟪cross v a, q⟫ * ⟪b, n⟫ := by
    nlinarith [mul_pos hbq han, mul_pos hab hqn]
  by_contra hle
  have hle' : ⟪cross v a, q⟫ ≤ 0 := not_lt.mp hle
  nlinarith [mul_le_mul_of_nonneg_right hle' hbn.le]

/-- Cramer's rule in the plane `v⊥`. -/
theorem cramer2 (v p s w : E3) (hp : ⟪v, p⟫ = 0) (hs : ⟪v, s⟫ = 0) (hw : ⟪v, w⟫ = 0)
    (h : ⟪cross v p, s⟫ ≠ 0) :
    w = (⟪cross v w, s⟫ / ⟪cross v p, s⟫) • p + (⟪cross v p, w⟫ / ⟪cross v p, s⟫) • s := by
  -- Helper lemma: inner product with cross product (cyclic permutation)
  have h_inner_cross_perm (a b c : E3) : ⟪a, cross b c⟫ = ⟪b, cross c a⟫ := by
    simp [Tammes15.cross, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm ((crossProduct b.ofLp) c.ofLp) a.ofLp, dotProduct_comm ((crossProduct c.ofLp) a.ofLp) b.ofLp]
    rw [triple_product_permutation a.ofLp b.ofLp c.ofLp]
  -- Helper: ⟪cross a b, c⟫ = ⟪a, cross b c⟫
  have h_inner_cross_eq (a b c : E3) : ⟪cross a b, c⟫ = ⟪a, cross b c⟫ := by
    simp [Tammes15.cross, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm c.ofLp ((crossProduct a.ofLp) b.ofLp)]
    rw [dotProduct_comm ((crossProduct b.ofLp) c.ofLp) a.ofLp]
    rw [dotProduct_comm ((crossProduct a.ofLp) b.ofLp) c.ofLp]
    rw [triple_product_permutation c.ofLp a.ofLp b.ofLp]
  -- Helper: cross a a = 0
  have h_cross_self (a : E3) : cross a a = 0 := by
    simp [Tammes15.cross, cross_self]
  -- Helper: ⟪cross a b, b⟫ = 0
  have h_dot_cross_self (a b : E3) : ⟪cross a b, b⟫ = 0 := by
    simp [Tammes15.cross, EuclideanSpace.inner_eq_star_dotProduct, dot_cross_self]
  -- Helper: ⟪cross a b, a⟫ = 0
  have h_dot_self_cross (a b : E3) : ⟪cross a b, a⟫ = 0 := by
    simp [Tammes15.cross, EuclideanSpace.inner_eq_star_dotProduct, dot_self_cross]
  -- Anticommutativity: cross a b = -cross b a
  have h_cross_anticomm (a b : E3) : cross a b = -cross b a := by
    ext i
    have h' : (crossProduct a.ofLp) b.ofLp = -((crossProduct b.ofLp) a.ofLp) := by
      calc
        (crossProduct a.ofLp) b.ofLp = -(-((crossProduct a.ofLp) b.ofLp)) := by simp
        _ = -((crossProduct b.ofLp) a.ofLp) := by rw [neg_cross a.ofLp b.ofLp]
    have h'' := congrArg (fun f : Fin 3 → ℝ => f i) h'
    simpa [Tammes15.cross, Pi.neg_apply] using h''
  -- v ≠ 0
  have hv_ne_zero : v ≠ 0 := by
    intro hvz
    apply h
    simp [Tammes15.cross, hvz]
  -- Use cramer3 with a = p, b = s, c = v, y = w
  have h_cross_denom : ⟪cross p s, v⟫ = ⟪cross v p, s⟫ := by
    calc
      ⟪cross p s, v⟫ = ⟪p, cross s v⟫ := h_inner_cross_eq p s v
      _ = ⟪s, cross v p⟫ := h_inner_cross_perm p s v
      _ = ⟪v, cross p s⟫ := h_inner_cross_perm s v p
      _ = ⟪cross v p, s⟫ := (h_inner_cross_eq v p s).symm
  have h_denom_ne : ⟪cross p s, v⟫ ≠ 0 := by rwa [h_cross_denom]
  have h_cramer := cramer3 p s v w h_denom_ne
  -- h_cramer : w = (⟪cross w s, v⟫ / ⟪cross p s, v⟫) • p + (⟪cross p w, v⟫ / ⟪cross p s, v⟫) • s + (⟪cross p s, w⟫ / ⟪cross p s, v⟫) • v
  -- Step 1: Show the coefficient of v is 0
  have h_coeff_v : ⟪cross p s, w⟫ / ⟪cross p s, v⟫ = 0 := by
    have h_inner_v := congrArg (fun x => ⟪v, x⟫) h_cramer
    -- h_inner_v : ⟪v, w⟫ = ⟪v, (A•p + B•s + C•v)⟫
    -- where A = ⟪cross w s, v⟫ / ⟪cross p s, v⟫, B = ⟪cross p w, v⟫ / ⟪cross p s, v⟫, C = ⟪cross p s, w⟫ / ⟪cross p s, v⟫
    -- Expand both sides
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right] at h_inner_v
    rw [hp, hs, hw] at h_inner_v
    -- h_inner_v : 0 = (⟪cross p s, w⟫ / ⟪cross p s, v⟫) * inner ℝ v v
    rw [real_inner_self_eq_norm_sq] at h_inner_v
    -- h_inner_v : 0 = (⟪cross p s, w⟫ / ⟪cross p s, v⟫) * ‖v‖ ^ 2
    have h_norm_sq_ne_zero : ‖v‖ ^ 2 ≠ 0 := by
      rw [← real_inner_self_eq_norm_sq v]
      intro hzero
      exact hv_ne_zero (inner_self_eq_zero.mp hzero)
    -- h_inner_v : 0 = C * ‖v‖², so C * ‖v‖² = 0
    have h_zero : (⟪cross p s, w⟫ / ⟪cross p s, v⟫) * ‖v‖ ^ 2 = 0 := by linarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_zero with (hcoeff | hnorm)
    · exact hcoeff
    · exfalso; exact h_norm_sq_ne_zero hnorm
  rw [h_coeff_v, zero_smul, add_zero] at h_cramer
  -- Now h_cramer : w = (⟪cross w s, v⟫ / ⟪cross p s, v⟫) • p + (⟪cross p w, v⟫ / ⟪cross p s, v⟫) • s
  -- Step 2: Simplify the coefficient of p: ⟪cross w s, v⟫ = ⟪cross v w, s⟫
  have h_coeff_p : ⟪cross w s, v⟫ = ⟪cross v w, s⟫ := by
    calc
      ⟪cross w s, v⟫ = ⟪w, cross s v⟫ := h_inner_cross_eq w s v
      _ = ⟪s, cross v w⟫ := h_inner_cross_perm w s v
      _ = ⟪cross v w, s⟫ := by
        calc
          ⟪s, cross v w⟫ = ⟪w, cross s v⟫ := (h_inner_cross_perm w s v).symm
          _ = ⟪v, cross w s⟫ := (h_inner_cross_perm v w s).symm
          _ = ⟪cross v w, s⟫ := (h_inner_cross_eq v w s).symm
  -- Step 3: Simplify the coefficient of s: ⟪cross p w, v⟫ = ⟪cross v p, w⟫
  have h_coeff_s : ⟪cross p w, v⟫ = ⟪cross v p, w⟫ := by
    calc
      ⟪cross p w, v⟫ = ⟪p, cross w v⟫ := h_inner_cross_eq p w v
      _ = ⟪w, cross v p⟫ := h_inner_cross_perm p w v
      _ = ⟪cross v p, w⟫ := by
        calc
          ⟪w, cross v p⟫ = ⟪p, cross w v⟫ := (h_inner_cross_perm p w v).symm
          _ = ⟪v, cross p w⟫ := (h_inner_cross_perm v p w).symm
          _ = ⟪cross v p, w⟫ := (h_inner_cross_eq v p w).symm
  -- Now put everything together
  calc
    w = (⟪cross w s, v⟫ / ⟪cross p s, v⟫) • p + (⟪cross p w, v⟫ / ⟪cross p s, v⟫) • s := h_cramer
    _ = (⟪cross v w, s⟫ / ⟪cross p s, v⟫) • p + (⟪cross v p, w⟫ / ⟪cross p s, v⟫) • s := by rw [h_coeff_p, h_coeff_s]
    _ = (⟪cross v w, s⟫ / ⟪cross v p, s⟫) • p + (⟪cross v p, w⟫ / ⟪cross v p, s⟫) • s := by rw [h_cross_denom]

/-- Two vectors of the plane `v⊥` with zero determinant are parallel. -/
theorem eq_smul_of_det_eq_zero (v a b : E3) (hv : v ≠ 0) (ha : ⟪v, a⟫ = 0) (hb : ⟪v, b⟫ = 0)
    (ha0 : a ≠ 0) (h : ⟪cross v a, b⟫ = 0) : ∃ t : ℝ, b = t • a := by
  set s := cross v a with hs
  have hv_s : ⟪v, s⟫ = 0 := by
    rw [hs]
    exact inner_cross_self v a
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have h_norm_sq_pos' : 0 < ‖v‖ ^ 2 * ‖a‖ ^ 2 := by
    have hv_sq_pos : 0 < ‖v‖ ^ 2 := pow_pos hv_norm_pos 2
    have ha_sq_pos : 0 < ‖a‖ ^ 2 := pow_pos ha_norm_pos 2
    exact mul_pos hv_sq_pos ha_sq_pos
  have h_norm_cross_sq_eq : ‖cross v a‖ ^ 2 = ‖v‖ ^ 2 * ‖a‖ ^ 2 := by
    rw [norm_cross_sq v a, ha]
    simp
  have h_norm_s_sq_pos : 0 < ‖s‖ ^ 2 := by
    rw [hs, h_norm_cross_sq_eq]
    exact h_norm_sq_pos'
  have h_cross_s_ne_zero : ⟪cross v a, s⟫ ≠ 0 := by
    rw [hs, real_inner_self_eq_norm_sq, h_norm_cross_sq_eq]
    exact ne_of_gt h_norm_sq_pos'
  have h_cramer := cramer2 v a s b ha hv_s hb h_cross_s_ne_zero
  rw [h] at h_cramer
  simp [zero_div, zero_smul] at h_cramer
  use ⟪cross v b, s⟫ / ⟪cross v a, s⟫

theorem support_line_unique (v p q₁ q₂ n₁ n₂ : E3) (k₁ k₂ : ℝ)
    (hp : ⟪v, p⟫ = 0) (hq₁ : ⟪v, q₁⟫ = 0) (hq₂ : ⟪v, q₂⟫ = 0)
    (hn₁ : ⟪v, n₁⟫ = 0) (hn₂ : ⟪v, n₂⟫ = 0) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ⟪p, n₁⟫ = k₁) (hp₂ : ⟪p, n₂⟫ = k₂) (h₁ : ⟪q₁, n₁⟫ = k₁) (h₂ : ⟪q₂, n₂⟫ = k₂)
    (h₂₁ : ⟪q₂, n₁⟫ ≤ k₁) (h₁₂ : ⟪q₁, n₂⟫ ≤ k₂)
    (hd₁ : 0 < ⟪cross v p, q₁⟫) (hd₂ : 0 < ⟪cross v p, q₂⟫) :
    k₂ • n₁ = k₁ • n₂ := by
  set u := k₂ • n₁ - k₁ • n₂ with hu
  have huv : ⟪v, u⟫ = 0 := by
    rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hn₁, hn₂]
    ring
  have hup : ⟪p, u⟫ = 0 := by
    rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hp₁, hp₂]
    ring
  have huq₁ : 0 ≤ ⟪q₁, u⟫ := by
    rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right, h₁]
    nlinarith [mul_le_mul_of_nonneg_left h₁₂ hk₁.le]
  have huq₂ : ⟪q₂, u⟫ ≤ 0 := by
    rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right, h₂]
    nlinarith [mul_le_mul_of_nonneg_left h₂₁ hk₂.le]
  have hD : ⟪cross v p, q₁⟫ ≠ 0 := hd₁.ne'
  have hq₂e := cramer2 v p q₁ q₂ hp hq₁ hq₂ hD
  have hq₂u : ⟪q₂, u⟫ = (⟪cross v p, q₂⟫ / ⟪cross v p, q₁⟫) * ⟪q₁, u⟫ := by
    conv_lhs => rw [hq₂e]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hup, mul_zero, zero_add]
  have hb : 0 < ⟪cross v p, q₂⟫ / ⟪cross v p, q₁⟫ := div_pos hd₂ hd₁
  have huq₁0 : ⟪q₁, u⟫ = 0 := by
    by_contra hne
    have hx : 0 < ⟪q₁, u⟫ := lt_of_le_of_ne huq₁ (Ne.symm hne)
    rw [hq₂u] at huq₂
    nlinarith [mul_pos hb hx]
  have K := congrArg (fun w => ⟪u, w⟫) (cramer_smul v p q₁ u)
  simp only [real_inner_smul_right, inner_add_right, real_inner_comm v u, huv,
    real_inner_comm p u, hup, real_inner_comm q₁ u, huq₁0, mul_zero, add_zero] at K
  have huu : ⟪u, u⟫ = 0 := by
    rcases mul_eq_zero.mp K with h | h
    · exact absurd h hD
    · exact h
  have h0 := inner_self_eq_zero.mp huu
  rw [hu] at h0
  exact sub_eq_zero.mp h0

/-- A maximiser of `⟪·, a⟫` over a finite set that wins the ties in `⟪·, b⟫` is exposed. -/
theorem exposed_of_lex (P : Finset E3) (w a b : E3) (hmax : ∀ y ∈ P, ⟪y, a⟫ ≤ ⟪w, a⟫)
    (htie : ∀ y ∈ P, y ≠ w → ⟪y, a⟫ = ⟪w, a⟫ → ⟪y, b⟫ < ⟪w, b⟫) :
    ∃ n : E3, ∀ y ∈ P, y ≠ w → ⟪y, n⟫ < ⟪w, n⟫ := by
  let S := P.filter (fun y => ⟪y, a⟫ < ⟪w, a⟫)
  by_cases hS : S.Nonempty
  · have hpos : ∀ y ∈ S, 0 < ⟪w, a⟫ - ⟪y, a⟫ := by
      intro y hy
      have hlt : ⟪y, a⟫ < ⟪w, a⟫ := Finset.mem_filter.mp hy |>.2
      linarith
    let r (y : E3) : ℝ := (⟪y, b⟫ - ⟪w, b⟫) / (⟪w, a⟫ - ⟪y, a⟫)
    have h_exists_max : ∃ ymax ∈ S, ∀ y ∈ S, r y ≤ r ymax :=
      Finset.exists_max_image S r hS
    rcases h_exists_max with ⟨ymax, hymaxS, hmaxr⟩
    let K := r ymax + 1
    use K • a + b
    intro y hyP hy_ne_w
    by_cases hyS : y ∈ S
    · have h_denom_pos : 0 < ⟪w, a⟫ - ⟪y, a⟫ := hpos y hyS
      have h_denom_ne_zero : ⟪w, a⟫ - ⟪y, a⟫ ≠ 0 := by linarith
      have h_ratio : r y ≤ r ymax := hmaxr y hyS
      have hK_gt_r : r y < K := by
        dsimp [K]
        linarith
      have h_diff : K * (⟪y, a⟫ - ⟪w, a⟫) + (⟪y, b⟫ - ⟪w, b⟫) < 0 := by
        have h_mul : ⟪y, b⟫ - ⟪w, b⟫ = r y * (⟪w, a⟫ - ⟪y, a⟫) := by
          dsimp [r]
          field_simp [h_denom_ne_zero]
        nlinarith
      calc
        ⟪y, K • a + b⟫ = K * ⟪y, a⟫ + ⟪y, b⟫ := by
          simp [inner_add_right, inner_smul_right]
        _ < K * ⟪w, a⟫ + ⟪w, b⟫ := by nlinarith
        _ = ⟪w, K • a + b⟫ := by simp [inner_add_right, inner_smul_right]
    · have h_not_lt : ¬ (⟪y, a⟫ < ⟪w, a⟫) := by
        intro hlt
        apply hyS
        exact Finset.mem_filter.mpr ⟨hyP, hlt⟩
      have h_eq : ⟪y, a⟫ = ⟪w, a⟫ := by
        have hle := hmax y hyP
        linarith
      have h_inner_lt : ⟪y, b⟫ < ⟪w, b⟫ := htie y hyP hy_ne_w h_eq
      calc
        ⟪y, K • a + b⟫ = K * ⟪y, a⟫ + ⟪y, b⟫ := by
          simp [inner_add_right, inner_smul_right]
        _ = K * ⟪w, a⟫ + ⟪y, b⟫ := by simp [h_eq]
        _ < K * ⟪w, a⟫ + ⟪w, b⟫ := by nlinarith
        _ = ⟪w, K • a + b⟫ := by simp [inner_add_right, inner_smul_right]
  · use b
    intro y hyP hy_ne_w
    have h_not_lt : ¬ (⟪y, a⟫ < ⟪w, a⟫) := by
      intro hlt
      apply hS
      exact ⟨y, Finset.mem_filter.mpr ⟨hyP, hlt⟩⟩
    have h_eq : ⟪y, a⟫ = ⟪w, a⟫ := by
      have hle := hmax y hyP
      linarith
    have h_inner_lt : ⟪y, b⟫ < ⟪w, b⟫ := htie y hyP hy_ne_w h_eq
    exact h_inner_lt

theorem exists_exposed_max (P : Finset E3) (hP : P.Nonempty) (a : E3) :
    ∃ w ∈ P, (∀ y ∈ P, ⟪y, a⟫ ≤ ⟪w, a⟫) ∧ ∃ n : E3, ∀ y ∈ P, y ≠ w → ⟪y, n⟫ < ⟪w, n⟫ := by
  -- Get a maximizer of inner product with a
  obtain ⟨w₀, hw₀, hmax₀⟩ := Finset.exists_max_image P (fun y => ⟪y, a⟫) hP
  -- The set of maximizers of ⟪·, a⟫ over P
  let Mx := P.filter (fun y => ∀ z ∈ P, ⟪z, a⟫ ≤ ⟪y, a⟫)
  have hMx_nonempty : Mx.Nonempty := by
    refine ⟨w₀, Finset.mem_filter.mpr ⟨hw₀, ?_⟩⟩
    intro z hz
    exact hmax₀ z hz
  -- Choose w ∈ Mx with maximal norm
  obtain ⟨w, hw, hmax_norm⟩ := Finset.exists_max_image Mx (fun y => ‖y‖) hMx_nonempty
  have hwP : w ∈ P := Finset.mem_of_mem_filter w hw
  have hw_max : ∀ y ∈ P, ⟪y, a⟫ ≤ ⟪w, a⟫ := (Finset.mem_filter.mp hw).2
  have hw_norm_max : ∀ y ∈ Mx, ‖y‖ ≤ ‖w‖ := hmax_norm
  -- Apply exposed_of_lex with b = w
  have h_exposed := exposed_of_lex P w a w hw_max (by
    intro y hy hy_ne hy_eq
    -- hy_eq : ⟪y, a⟫ = ⟪w, a⟫, so y ∈ Mx
    have hy_in_Mx : y ∈ Mx := by
      refine Finset.mem_filter.mpr ⟨hy, ?_⟩
      intro z hz
      calc
        ⟪z, a⟫ ≤ ⟪w, a⟫ := hw_max z hz
        _ = ⟪y, a⟫ := by rw [hy_eq]
    have h_norm_le : ‖y‖ ≤ ‖w‖ := hw_norm_max y hy_in_Mx
    have h_sq_pos : 0 < ‖y - w‖ ^ 2 := by
      have h_pos : 0 < ‖y - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy_ne)
      exact pow_pos h_pos 2
    have h_expand : ‖y - w‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, w⟫ + ‖w‖ ^ 2 := norm_sub_sq_real y w
    have h_sq_le : ‖y‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
      have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg _
      refine sq_le_sq.mpr ?_
      rwa [abs_of_nonneg hy_nonneg, abs_of_nonneg hw_nonneg]
    have h_ineq : ‖y‖ ^ 2 - 2 * ⟪y, w⟫ + ‖w‖ ^ 2 > 0 := by
      linarith
    have h_final : ⟪y, w⟫ < ‖w‖ ^ 2 := by
      nlinarith
    calc
      ⟪y, w⟫ < ‖w‖ ^ 2 := h_final
      _ = ⟪w, w⟫ := by rw [real_inner_self_eq_norm_sq])
  rcases h_exposed with ⟨n, hn⟩
  exact ⟨w, hwP, hw_max, n, hn⟩

theorem exists_three_exposed (v : E3) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫) :
    ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ w ∈ ({a, b, c} : Finset E3), ∃ n : E3, ∀ y ∈ P, y ≠ w → ⟪y, n⟫ < ⟪w, n⟫ := by
  obtain ⟨u, hu1, hvu⟩ := exists_unit_orthogonal v
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    exact zero_ne_one hu1
  obtain ⟨y₀, hy₀, hy₀u⟩ := hin u hvu hu0
  have hPne : P.Nonempty := ⟨y₀, hy₀⟩
  obtain ⟨a, ha, hamax, hax⟩ := exists_exposed_max P hPne u
  have hau : 0 < ⟪a, u⟫ := lt_of_lt_of_le hy₀u (hamax y₀ hy₀)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [inner_zero_left] at hau
    exact lt_irrefl 0 hau
  obtain ⟨e, hve, hae, he0⟩ : ∃ e : E3, ⟪v, e⟫ = 0 ∧ ⟪a, e⟫ = 0 ∧ e ≠ 0 := by
    by_cases hv : v = 0
    · obtain ⟨e, he1, hae⟩ := exists_unit_orthogonal a
      refine ⟨e, by rw [hv, inner_zero_left], hae, ?_⟩
      intro h
      rw [h, norm_zero] at he1
      exact zero_ne_one he1
    · refine ⟨cross v a, inner_cross_self v a, inner_cross_right_self v a, ?_⟩
      intro h
      have h2 := norm_cross_sq v a
      rw [h, norm_zero, hP a ha] at h2
      have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      nlinarith [mul_pos (pow_pos hv' 2) (pow_pos ha' 2)]
  obtain ⟨y₁, hy₁, hy₁e⟩ := hin e hve he0
  obtain ⟨b, hb, hbmax, hbx⟩ := exists_exposed_max P hPne e
  have hbe : 0 < ⟪b, e⟫ := lt_of_lt_of_le hy₁e (hbmax y₁ hy₁)
  have hve' : ⟪v, -e⟫ = 0 := by rw [inner_neg_right, hve, neg_zero]
  obtain ⟨y₂, hy₂, hy₂e⟩ := hin (-e) hve' (neg_ne_zero.mpr he0)
  obtain ⟨c, hc, hcmax, hcx⟩ := exists_exposed_max P hPne (-e)
  have hce : 0 < ⟪c, -e⟫ := lt_of_lt_of_le hy₂e (hcmax y₂ hy₂)
  rw [inner_neg_right] at hce
  refine ⟨a, ha, b, hb, c, hc, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    linarith
  · rintro rfl
    linarith
  · rintro rfl
    linarith
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hax
    · exact hbx
    · exact hcx

/-- A finite set with a transitive irreflexive relation has a minimal element. -/
theorem exists_minimal_of_trans {α : Type*} (r : α → α → Prop) (S : Finset α) (hS : S.Nonempty)
    (hirr : ∀ a ∈ S, ¬ r a a) (htr : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, r a b → r b c → r a c) :
    ∃ m ∈ S, ∀ a ∈ S, ¬ r a m := by
  let c (m : α) : ℕ := (S.filter (fun a => r a m)).card
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S c hS
  refine ⟨m, hm, ?_⟩
  intro a ha hram
  have hsubset : S.filter (fun x => r x a) ⊆ S.filter (fun x => r x m) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxS, hrxa⟩
    exact ⟨hxS, htr x hxS a ha m hm hrxa hram⟩
  have hne : S.filter (fun x => r x a) ≠ S.filter (fun x => r x m) := by
    intro heq
    have ha_mem : a ∈ S.filter (fun x => r x m) := by
      rw [Finset.mem_filter]
      exact ⟨ha, hram⟩
    have ha_not_mem : a ∉ S.filter (fun x => r x a) := by
      rw [Finset.mem_filter]
      exact fun h => hirr a ha h.2
    rw [← heq] at ha_mem
    exact ha_not_mem ha_mem
  have hssubset : S.filter (fun x => r x a) ⊂ S.filter (fun x => r x m) := by
    rwa [Finset.ssubset_iff_subset_ne, and_iff_right hsubset]
  have hcard_lt : c a < c m := Finset.card_lt_card hssubset
  have hcard_le : c m ≤ c a := hmin a ha
  linarith

theorem inner_cross_antisymm (v x y : E3) : ⟪cross v x, y⟫ = -⟪cross v y, x⟫ := by
  calc
    ⟪cross v x, y⟫ = ⟪y, cross v x⟫ := by rw [real_inner_comm]
    _ = ⟪v, cross x y⟫ := by rw [Tammes15.inner_cross_perm]
    _ = ⟪v, -cross y x⟫ := by rw [cross_anticomm_E3]
    _ = -⟪v, cross y x⟫ := by rw [inner_neg_right]
    _ = -⟪x, cross v y⟫ := by rw [← Tammes15.inner_cross_perm x v y]
    _ = -⟪cross v y, x⟫ := by rw [real_inner_comm]

/-- Gift wrapping, the choice: the most clockwise direction from an exposed point `p`, and the
farthest point in it. -/
theorem gift_wrap_choice (v : E3) (hv : v ≠ 0) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (p : E3) (hp : p ∈ P) (e : E3) (he : ∀ y ∈ P, y ≠ p → ⟪y, e⟫ < ⟪p, e⟫)
    (hne : ∃ y ∈ P, y ≠ p) :
    ∃ s ∈ P, s ≠ p ∧ (∀ q ∈ P, 0 ≤ ⟪cross v (s - p), q - p⟫) ∧
      ∀ q ∈ P, ⟪cross v (s - p), q - p⟫ = 0 → ⟪q - p, s - p⟫ ≤ ⟪s - p, s - p⟫ := by
  -- Let Q = P \\ {p}, nonempty by hne
  let Q := P.erase p
  have hQ_nonempty : Q.Nonempty := by
    rcases hne with ⟨y, hy, hy_ne⟩
    refine ⟨y, ?_⟩
    rw [Finset.mem_erase]
    exact ⟨hy_ne, hy⟩
  -- Define relation r on Q: r q q' := 0 < ⟪cross v (q - p), q' - p⟫
  set r : E3 → E3 → Prop := λ q q' => 0 < ⟪cross v (q - p), q' - p⟫ with hr_def
  have hr_irr : ∀ a ∈ Q, ¬ r a a := by
    intro a ha
    rw [hr_def]
    have hzero : ⟪cross v (a - p), a - p⟫ = 0 := by
      calc
        ⟪cross v (a - p), a - p⟫ = ⟪v, cross (a - p) (a - p)⟫ := by
          rw [real_inner_comm, Tammes15.inner_cross_perm]
        _ = ⟪v, 0⟫ := by simp [cross]
        _ = 0 := by simp
    linarith
  have hr_trans : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, r a b → r b c → r a c := by
    intro a ha b hb c hc h_ab h_bc
    rw [hr_def] at h_ab h_bc ⊢
    -- We have: 0 < ⟪cross v (a-p), b-p⟫ and 0 < ⟪cross v (b-p), c-p⟫
    -- Need: 0 < ⟪cross v (a-p), c-p⟫
    -- Use det_pos_trans with n = -e
    have ha_mem : a ∈ P := Finset.mem_of_mem_erase ha
    have hb_mem : b ∈ P := Finset.mem_of_mem_erase hb
    have hc_mem : c ∈ P := Finset.mem_of_mem_erase hc
    have ha_ne_p : a ≠ p := (Finset.mem_erase.mp ha).1
    have hb_ne_p : b ≠ p := (Finset.mem_erase.mp hb).1
    have hc_ne_p : c ≠ p := (Finset.mem_erase.mp hc).1
    have ha_v : ⟪v, a - p⟫ = 0 := by
      rw [inner_sub_right, hP a ha_mem, hP p hp, sub_self]
    have hb_v : ⟪v, b - p⟫ = 0 := by
      rw [inner_sub_right, hP b hb_mem, hP p hp, sub_self]
    have hc_v : ⟪v, c - p⟫ = 0 := by
      rw [inner_sub_right, hP c hc_mem, hP p hp, sub_self]
    have ha_e : 0 < ⟪a - p, -e⟫ := by
      rw [inner_neg_right, inner_sub_left]
      have hlt := he a ha_mem ha_ne_p
      linarith
    have hb_e : 0 < ⟪b - p, -e⟫ := by
      rw [inner_neg_right, inner_sub_left]
      have hlt := he b hb_mem hb_ne_p
      linarith
    have hc_e : 0 < ⟪c - p, -e⟫ := by
      rw [inner_neg_right, inner_sub_left]
      have hlt := he c hc_mem hc_ne_p
      linarith
    exact det_pos_trans v (-e) (a - p) (b - p) (c - p) ha_v hb_v hc_v ha_e hb_e hc_e h_ab h_bc
  -- By exists_minimal_of_trans, there exists a minimal element
  obtain ⟨m, hmQ, hm_min⟩ := exists_minimal_of_trans r Q hQ_nonempty hr_irr hr_trans
  have hmP : m ∈ P := Finset.mem_of_mem_erase hmQ
  have hm_ne_p : m ≠ p := Finset.ne_of_mem_erase hmQ
  -- Let Mn be the set of minimal elements
  let Mn := Q.filter (λ m' => ∀ a ∈ Q, ¬ r a m')
  have hm_Mn : m ∈ Mn := by
    rw [Finset.mem_filter]
    exact ⟨hmQ, hm_min⟩
  have hMn_nonempty : Mn.Nonempty := ⟨m, hm_Mn⟩
  -- Choose s ∈ Mn maximizing ‖s - p‖
  obtain ⟨s, hs_Mn, hs_max⟩ := Finset.exists_max_image Mn (λ x => ‖x - p‖) hMn_nonempty
  have hsQ : s ∈ Q := by
    rcases Finset.mem_filter.mp hs_Mn with ⟨h, _⟩
    exact h
  have hsP : s ∈ P := Finset.mem_of_mem_erase hsQ
  have hs_ne_p : s ≠ p := Finset.ne_of_mem_erase hsQ
  have hs_min : ∀ a ∈ Q, ¬ r a s := by
    rcases Finset.mem_filter.mp hs_Mn with ⟨_, h⟩
    exact h
  -- Now prove the two conditions
  have h_cond1 : ∀ q ∈ P, 0 ≤ ⟪cross v (s - p), q - p⟫ := by
    intro q hqP
    by_cases hq_eq_p : q = p
    · subst hq_eq_p
      simp
    · have hqQ : q ∈ Q := by
        rw [Finset.mem_erase]
        exact ⟨hq_eq_p, hqP⟩
      have h_not_r : ¬ r q s := hs_min q hqQ
      rw [hr_def] at h_not_r
      have h_nonpos : ⟪cross v (q - p), s - p⟫ ≤ 0 := by
        linarith
      -- Use antisymmetry: ⟪cross v (q-p), s-p⟫ ≤ 0 → ⟪cross v (s-p), q-p⟫ ≥ 0
      have h_antisymm := inner_cross_antisymm v (q - p) (s - p)
      linarith
  have h_cond2 : ∀ q ∈ P, ⟪cross v (s - p), q - p⟫ = 0 → ⟪q - p, s - p⟫ ≤ ⟪s - p, s - p⟫ := by
    intro q hqP h_cross_zero
    by_cases hq_eq_p : q = p
    · subst hq_eq_p
      simp
    · have hqQ : q ∈ Q := by
        rw [Finset.mem_erase]
        exact ⟨hq_eq_p, hqP⟩
      -- From eq_smul_of_det_eq_zero: if cross v (s-p) (q-p) = 0, then q-p = t • (s-p)
      have h_det_zero : ⟪cross v (s - p), q - p⟫ = 0 := h_cross_zero
      have hs_sub_ne_zero : s - p ≠ 0 := by
        intro hzero
        apply hs_ne_p
        exact sub_eq_zero.mp hzero
      have hs_v : ⟪v, s - p⟫ = 0 := by
        rw [inner_sub_right, hP s hsP, hP p hp, sub_self]
      have hq_v : ⟪v, q - p⟫ = 0 := by
        rw [inner_sub_right, hP q hqP, hP p hp, sub_self]
      have h_smul := eq_smul_of_det_eq_zero v (s - p) (q - p) hv hs_v hq_v hs_sub_ne_zero h_det_zero
      rcases h_smul with ⟨t, ht⟩
      -- q - p = t • (s - p)
      -- Show t > 0 using the e condition
      have hs_e : ⟪s - p, -e⟫ > 0 := by
        rw [inner_neg_right, inner_sub_left]
        have hlt := he s hsP hs_ne_p
        linarith
      have hq_e : ⟪q - p, -e⟫ > 0 := by
        rw [inner_neg_right, inner_sub_left]
        have hlt := he q hqP hq_eq_p
        linarith
      have ht_pos : 0 < t := by
        have h_eq : ⟪q - p, -e⟫ = t * ⟪s - p, -e⟫ := by
          rw [ht, inner_smul_left]
          simp
        have hpos_q : 0 < ⟪q - p, -e⟫ := hq_e
        have hpos_s : 0 < ⟪s - p, -e⟫ := hs_e
        rw [h_eq] at hpos_q
        -- t * (positive) > 0 → t > 0
        exact pos_of_mul_pos_left hpos_q hpos_s.le
      -- Show ∀ a ∈ Q, ¬ r a q (so q ∈ Mn)
      have hq_Mn : q ∈ Mn := by
        rw [Finset.mem_filter]
        refine ⟨hqQ, λ a ha => ?_⟩
        -- Need: ¬ r a q, i.e., ¬ (0 < ⟪cross v (a-p), q-p⟫)
        have h_not_ra_s : ¬ r a s := hs_min a ha
        dsimp [r] at h_not_ra_s
        -- h_not_ra_s: ¬ (0 < ⟪cross v (a-p), s-p⟫)
        -- So ⟪cross v (a-p), s-p⟫ ≤ 0
        have h_nonpos : ⟪cross v (a - p), s - p⟫ ≤ 0 := by linarith
        have h_eq : ⟪cross v (a - p), q - p⟫ = t * ⟪cross v (a - p), s - p⟫ := by
          rw [ht, inner_smul_right]
        dsimp [r]
        rw [h_eq]
        -- Need: ¬ (0 < t * ⟪cross v (a-p), s-p⟫)
        -- Since t > 0 and ⟪cross v (a-p), s-p⟫ ≤ 0, the product is ≤ 0
        nlinarith
      -- Now by maximality of s in Mn
      have h_norm_le : ‖q - p‖ ≤ ‖s - p‖ := hs_max q hq_Mn
      -- Show t ≤ 1 using norm maximality
      have h_norm_q : ‖q - p‖ = t * ‖s - p‖ := by
        rw [ht, norm_smul, Real.norm_of_nonneg ht_pos.le]
      rw [h_norm_q] at h_norm_le
      have h_norm_s_pos : 0 < ‖s - p‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr hs_ne_p
      have ht_le_one : t ≤ 1 := by
        -- From t * ‖s-p‖ ≤ ‖s-p‖ and ‖s-p‖ > 0, divide both sides
        nlinarith
      -- Now compute ⟪q-p, s-p⟫ ≤ ‖s-p‖²
      calc
        ⟪q - p, s - p⟫ = ⟪t • (s - p), s - p⟫ := by rw [ht]
        _ = t * ⟪s - p, s - p⟫ := by
          rw [inner_smul_left]
          simp
        _ = t * (RCLike.re (⟪s - p, s - p⟫)) := by simp
        _ = t * ‖s - p‖ ^ 2 := by rw [inner_self_eq_norm_sq]
        _ ≤ 1 * ‖s - p‖ ^ 2 := by nlinarith
        _ = ‖s - p‖ ^ 2 := by simp
        _ = RCLike.re (⟪s - p, s - p⟫) := by rw [inner_self_eq_norm_sq]
        _ = ⟪s - p, s - p⟫ := by simp
  exact ⟨s, hsP, hs_ne_p, h_cond1, h_cond2⟩

/-- Gift wrapping, the supporting line through `p` and `s`. -/
theorem gift_wrap_line (v : E3) (hv : v ≠ 0) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫)
    (p s : E3) (hp : p ∈ P) (hs : s ∈ P) (hsp : s ≠ p)
    (hmin : ∀ q ∈ P, 0 ≤ ⟪cross v (s - p), q - p⟫) :
    ⟪v, cross (s - p) v⟫ = 0 ∧ 0 < ⟪cross v p, s⟫ ∧ ⟪p, cross (s - p) v⟫ = ⟪cross v p, s⟫ ∧
      ⟪s, cross (s - p) v⟫ = ⟪p, cross (s - p) v⟫ ∧
      ∀ y ∈ P, ⟪y, cross (s - p) v⟫ ≤ ⟪p, cross (s - p) v⟫ := by
  set n := cross (s - p) v with hn
  have hvn : ⟪v, n⟫ = 0 := by
    rw [hn]
    exact Tammes15.inner_cross_right_self (s - p) v
  have hle (y : E3) (hy : y ∈ P) : ⟪y, n⟫ ≤ ⟪p, n⟫ := by
    rw [hn]
    have h := hmin y hy
    have hsub : ⟪y, cross (s - p) v⟫ - ⟪p, cross (s - p) v⟫ = -⟪cross v (s - p), y - p⟫ := by
      calc
        ⟪y, cross (s - p) v⟫ - ⟪p, cross (s - p) v⟫ = ⟪y - p, cross (s - p) v⟫ := by
          rw [inner_sub_left]
        _ = -⟪cross v (s - p), y - p⟫ := by
          have hanticomm : cross (s - p) v = -cross v (s - p) := by
            have h := _root_.cross_anticomm (WithLp.ofLp (s - p)) (WithLp.ofLp v)
            have h' : crossProduct (WithLp.ofLp (s - p)) (WithLp.ofLp v) =
                -crossProduct (WithLp.ofLp v) (WithLp.ofLp (s - p)) := by
              have := congrArg Neg.neg h
              simpa using this
            calc
              cross (s - p) v = WithLp.toLp 2 (crossProduct (WithLp.ofLp (s - p)) (WithLp.ofLp v)) := rfl
              _ = WithLp.toLp 2 (-crossProduct (WithLp.ofLp v) (WithLp.ofLp (s - p))) := by rw [h']
              _ = -WithLp.toLp 2 (crossProduct (WithLp.ofLp v) (WithLp.ofLp (s - p))) := by simp
              _ = -cross v (s - p) := rfl
          rw [hanticomm, inner_neg_right, real_inner_comm (y - p) (cross v (s - p))]
    have hnonpos : ⟪y, cross (s - p) v⟫ - ⟪p, cross (s - p) v⟫ ≤ 0 := by
      rw [hsub]
      linarith
    linarith
  have hsp_eq : ⟪s, n⟫ = ⟪p, n⟫ := by
    rw [hn]
    calc
      ⟪s, cross (s - p) v⟫ = ⟪p + (s - p), cross (s - p) v⟫ := by
        simp
      _ = ⟪p, cross (s - p) v⟫ + ⟪s - p, cross (s - p) v⟫ := by
        rw [inner_add_left]
      _ = ⟪p, cross (s - p) v⟫ + 0 := by
        rw [Tammes15.inner_cross_self (s - p) v]
      _ = ⟪p, cross (s - p) v⟫ := by simp
  have hcross_eq : ⟪p, n⟫ = ⟪cross v p, s⟫ := by
    rw [hn]
    calc
      ⟪p, cross (s - p) v⟫ = ⟪cross (s - p) v, p⟫ := by
        rw [real_inner_comm]
      _ = ⟪s - p, cross v p⟫ := by
        rw [real_inner_comm, Tammes15.inner_cross_perm p (s - p) v]
      _ = ⟪s, cross v p⟫ - ⟪p, cross v p⟫ := by
        rw [inner_sub_left]
      _ = ⟪s, cross v p⟫ := by
        rw [Tammes15.inner_cross_right_self v p, sub_zero]
      _ = ⟪cross v p, s⟫ := by
        rw [real_inner_comm]
  have hpos : 0 < ⟪cross v p, s⟫ := by
    have hnz : n ≠ 0 := by
      rw [hn]
      intro hzero
      have hnorm_sq_pos : 0 < ‖cross (s - p) v‖ ^ 2 := by
        have hpos1 : 0 < ‖s - p‖ ^ 2 := by
          have hne' : s - p ≠ 0 := by
            intro h; apply hsp; apply sub_eq_zero.mp h
          have := sq_pos_iff.mpr (norm_ne_zero_iff.mpr hne')
          exact this
        have hpos2 : 0 < ‖v‖ ^ 2 := by
          have hne' : v ≠ 0 := hv
          have := sq_pos_iff.mpr (norm_ne_zero_iff.mpr hne')
          exact this
        have hdot : ⟪v, s - p⟫ = 0 := by
          have hvp : ⟪v, p⟫ = 0 := hP p hp
          have hvs : ⟪v, s⟫ = 0 := hP s hs
          rw [inner_sub_right, hvp, hvs, sub_zero]
        have hnorm_cross_sq : ‖cross (s - p) v‖ ^ 2 = ‖s - p‖ ^ 2 * ‖v‖ ^ 2 - ⟪s - p, v⟫ ^ 2 :=
          Tammes15.norm_cross_sq (s - p) v
        rw [hnorm_cross_sq]
        have hpos_prod : 0 < ‖s - p‖ ^ 2 * ‖v‖ ^ 2 := by
          exact mul_pos hpos1 hpos2
        have hdot' : ⟪s - p, v⟫ = 0 := by
          rw [real_inner_comm, hdot]
        rw [hdot']
        simp [hpos_prod]
      have hzero_sq : ‖cross (s - p) v‖ ^ 2 = 0 := by
        simp [hzero]
      linarith
    have h_exists := hin n ?_ hnz
    · rcases h_exists with ⟨y, hy, hypos⟩
      have hle_p := hle y hy
      have heq : ⟪p, n⟫ = ⟪cross v p, s⟫ := hcross_eq
      rw [heq] at hle_p
      have : 0 < ⟪cross v p, s⟫ := by
        linarith
      exact this
    · -- need ⟪v, n⟫ = 0, which is hvn
      rw [hvn]
  refine ⟨hvn, hpos, ?_, ?_, ?_⟩
  · -- ⟪p, cross (s - p) v⟫ = ⟪cross v p, s⟫
    rw [hn]
    exact hcross_eq
  · -- ⟪s, cross (s - p) v⟫ = ⟪p, cross (s - p) v⟫
    rw [hn]
    exact hsp_eq
  · -- ∀ y ∈ P, ⟪y, cross (s - p) v⟫ ≤ ⟪p, cross (s - p) v⟫
    intro y hy
    rw [hn]
    exact hle y hy

/-- Gift wrapping, the points of `P` on the line from `p` to `s` lie on the segment. -/
theorem gift_wrap_segment (v : E3) (hv : v ≠ 0) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (p s e : E3) (hp : p ∈ P) (hs : s ∈ P) (hsp : s ≠ p)
    (he : ∀ y ∈ P, y ≠ p → ⟪y, e⟫ < ⟪p, e⟫)
    (hfar : ∀ q ∈ P, ⟪cross v (s - p), q - p⟫ = 0 → ⟪q - p, s - p⟫ ≤ ⟪s - p, s - p⟫)
    (y : E3) (hy : y ∈ P) (hyl : ⟪cross v (s - p), y - p⟫ = 0) (hyp : y ≠ p) (hys : y ≠ s) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ y - p = t • (s - p) := by
  have hvsp : ⟪v, s - p⟫ = 0 := by
    rw [inner_sub_right]
    simp [hP s hs, hP p hp]
  have hvy : ⟪v, y - p⟫ = 0 := by
    rw [inner_sub_right]
    simp [hP y hy, hP p hp]
  have hsp0 : s - p ≠ 0 := sub_ne_zero.mpr hsp
  obtain ⟨t, ht⟩ := eq_smul_of_det_eq_zero v (s - p) (y - p) hv hvsp hvy hsp0 hyl
  have h_inner_y : ⟪y - p, e⟫ < 0 := by
    have hye : ⟪y, e⟫ < ⟪p, e⟫ := he y hy hyp
    have : ⟪y - p, e⟫ = ⟪y, e⟫ - ⟪p, e⟫ := by simpa using inner_sub_left y p e
    rw [this]
    linarith
  have h_inner_s : ⟪s - p, e⟫ < 0 := by
    have hse : ⟪s, e⟫ < ⟪p, e⟫ := he s hs hsp
    have : ⟪s - p, e⟫ = ⟪s, e⟫ - ⟪p, e⟫ := by simpa using inner_sub_left s p e
    rw [this]
    linarith
  have ht_pos : 0 < t := by
    have h_eq : ⟪y - p, e⟫ = t * ⟪s - p, e⟫ := by
      rw [ht]
      simp [inner_smul_left]
    by_contra! h_nonpos
    have h_nonneg : t * ⟪s - p, e⟫ ≥ 0 := by
      nlinarith
    linarith [h_eq, h_inner_y, h_nonneg]
  have h_norm_sq_pos : 0 < ‖s - p‖ ^ 2 := by
    have h_norm_pos : 0 < ‖s - p‖ := norm_pos_iff.mpr hsp0
    positivity
  have ht_le_one : t ≤ 1 := by
    have hfar_y := hfar y hy hyl
    rw [ht] at hfar_y
    have h_left : ⟪t • (s - p), s - p⟫ = t * ‖s - p‖ ^ 2 := by
      simp [inner_smul_left]
    have h_right : ⟪s - p, s - p⟫ = ‖s - p‖ ^ 2 := by
      simp
    rw [h_left, h_right] at hfar_y
    have : 0 < ‖s - p‖ ^ 2 := h_norm_sq_pos
    nlinarith
  have ht_lt_one : t < 1 := by
    by_contra! h_ge
    have : t = 1 := by linarith
    rw [this, one_smul] at ht
    have hy_eq_s : y = s := by
      apply sub_left_inj.mp ht
    exact hys hy_eq_s
  exact ⟨t, ht_pos, ht_lt_one, ht⟩

/-- Gift wrapping: no exposed point lies strictly between `p` and `s`. -/
theorem gift_wrap_between (v : E3) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫)
    (p s n : E3) (hp : p ∈ P) (hs : s ∈ P) (hps : 0 < ⟪cross v p, s⟫) (hpn : 0 < ⟪p, n⟫)
    (hsn : ⟪s, n⟫ = ⟪p, n⟫) (hle : ∀ y ∈ P, ⟪y, n⟫ ≤ ⟪p, n⟫)
    (w : E3) (hw : w ∈ P) (hwx : ∃ m : E3, ∀ y ∈ P, y ≠ w → ⟪y, m⟫ < ⟪w, m⟫) :
    ¬ (0 < ⟪cross v p, w⟫ ∧ 0 < ⟪cross v w, s⟫) := by
  intro h
  rcases h with ⟨hcpw, hcws⟩
  have hvp : ⟪v, p⟫ = 0 := hP p hp
  have hvs : ⟪v, s⟫ = 0 := hP s hs
  have hvw : ⟪v, w⟫ = 0 := hP w hw
  have hDpos : 0 < ⟪cross v p, s⟫ := hps
  have hDne0 : ⟪cross v p, s⟫ ≠ 0 := by linarith
  -- w ≠ p and w ≠ s
  have hwp_ne : w ≠ p := by
    intro heq
    have hzero : ⟪cross v p, w⟫ = 0 := by
      rw [heq, real_inner_comm]
      exact inner_cross_right_self v p
    linarith
  have hws_ne : w ≠ s := by
    intro heq
    have hzero : ⟪cross v w, s⟫ = 0 := by
      rw [heq, real_inner_comm]
      exact inner_cross_right_self v s
    linarith
  -- cramer2: w = α • p + β • s
  have hcramer := cramer2 v p s w hvp hvs hvw hDne0
  set α := ⟪cross v w, s⟫ / ⟪cross v p, s⟫ with hαdef
  set β := ⟪cross v p, w⟫ / ⟪cross v p, s⟫ with hβdef
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hcws hDpos
  have hβpos : 0 < β := by
    dsimp [β]
    exact div_pos hcpw hDpos
  have hw_expr : w = α • p + β • s := by
    calc
      w = (⟪cross v w, s⟫ / ⟪cross v p, s⟫) • p + (⟪cross v p, w⟫ / ⟪cross v p, s⟫) • s := hcramer
      _ = α • p + β • s := rfl
  -- Compute ⟪w, n⟫
  have hwn : ⟪w, n⟫ = (α + β) * ⟪p, n⟫ := by
    calc
      ⟪w, n⟫ = ⟪α • p + β • s, n⟫ := by rw [hw_expr]
      _ = ⟪α • p, n⟫ + ⟪β • s, n⟫ := by rw [inner_add_left]
      _ = α * ⟪p, n⟫ + β * ⟪s, n⟫ := by simp [inner_smul_left]
      _ = α * ⟪p, n⟫ + β * ⟪p, n⟫ := by rw [hsn]
      _ = (α + β) * ⟪p, n⟫ := by ring
  -- From hle, we get α + β ≤ 1
  have hsum_le_one : α + β ≤ 1 := by
    have hwle := hle w hw
    rw [hwn] at hwle
    have hpos : 0 < ⟪p, n⟫ := hpn
    nlinarith
  -- Get m from hwx
  rcases hwx with ⟨m, hm⟩
  have hpm_lt : ⟪p, m⟫ < ⟪w, m⟫ := hm p hp (Ne.symm hwp_ne)
  have hsm_lt : ⟪s, m⟫ < ⟪w, m⟫ := hm s hs (Ne.symm hws_ne)
  -- Compute ⟪w, m⟫ in terms of p and s
  have hwm_expr : ⟪w, m⟫ = α * ⟪p, m⟫ + β * ⟪s, m⟫ := by
    calc
      ⟪w, m⟫ = ⟪α • p + β • s, m⟫ := by rw [hw_expr]
      _ = ⟪α • p, m⟫ + ⟪β • s, m⟫ := by rw [inner_add_left]
      _ = α * ⟪p, m⟫ + β * ⟪s, m⟫ := by simp [inner_smul_left]
  have hwm_lt : ⟪w, m⟫ < (α + β) * ⟪w, m⟫ := by
    calc
      ⟪w, m⟫ = α * ⟪p, m⟫ + β * ⟪s, m⟫ := hwm_expr
      _ < α * ⟪w, m⟫ + β * ⟪w, m⟫ := by
        nlinarith
      _ = (α + β) * ⟪w, m⟫ := by ring
  -- Case split on sign of ⟪w, m⟫
  by_cases hwm_pos : 0 < ⟪w, m⟫
  · -- Case 1: ⟪w, m⟫ > 0
    have hineq : (α + β) * ⟪w, m⟫ ≤ 1 * ⟪w, m⟫ := by
      nlinarith
    nlinarith
  · -- Case 2: ⟪w, m⟫ ≤ 0
    have hwm_nonpos : ⟪w, m⟫ ≤ 0 := by
      simpa using hwm_pos
    have hv_ne_zero : v ≠ 0 := by
      intro hvz
      have hcrossz : cross v p = 0 := by
        dsimp [cross]
        rw [hvz]
        simp
      have hzero : ⟪cross v p, s⟫ = 0 := by
        rw [hcrossz, inner_zero_left]
      linarith
    set m' := m - (⟪v, m⟫ / ‖v‖ ^ 2) • v with hm'def
    have hnorm : ⟪v, v⟫ = ‖v‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℝ) (E := E3) v
      simp
    have hsq_ne_zero : ‖v‖ ^ 2 ≠ 0 := by
      intro hzero
      have hnorm0 : ‖v‖ = 0 := by nlinarith
      exact hv_ne_zero (norm_eq_zero.mp hnorm0)
    have hvm' : ⟪v, m'⟫ = 0 := by
      dsimp [m']
      rw [inner_sub_right, inner_smul_right, hnorm]
      field_simp [hsq_ne_zero]
      ring
    have hP_m' : ∀ y ∈ P, ⟪y, m'⟫ = ⟪y, m⟫ := by
      intro y hy
      dsimp [m']
      rw [inner_sub_right, inner_smul_right]
      have hvy : ⟪v, y⟫ = 0 := hP y hy
      rw [real_inner_comm v y, hvy]
      simp
    have hm'_ne_zero : m' ≠ 0 := by
      intro hm'z
      have hpm'_zero : ⟪p, m'⟫ = 0 := by rw [hm'z, inner_zero_right]
      have hwm'_zero : ⟪w, m'⟫ = 0 := by rw [hm'z, inner_zero_right]
      have hpm'_zero' : ⟪p, m⟫ = 0 := by
        rw [← hP_m' p hp, hpm'_zero]
      have hwm'_zero' : ⟪w, m⟫ = 0 := by
        rw [← hP_m' w hw, hwm'_zero]
      linarith [hpm_lt, hpm'_zero', hwm'_zero']
    have hm'_orth : ⟪v, m'⟫ = 0 := hvm'
    rcases hin m' hm'_orth hm'_ne_zero with ⟨y, hy, hypos⟩
    have hy_ne_w : y ≠ w := by
      intro heq
      have h_eq_m' : ⟪y, m'⟫ = ⟪w, m'⟫ := by rw [heq]
      rw [hP_m' y hy, hP_m' w hw] at h_eq_m'
      rw [hP_m' y hy] at hypos
      rw [h_eq_m'] at hypos
      linarith
    have hy_lt : ⟪y, m⟫ < ⟪w, m⟫ := hm y hy hy_ne_w
    rw [hP_m' y hy] at hypos
    linarith

theorem gift_wrap (v : E3) (hv : v ≠ 0) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫)
    (p : E3) (hp : p ∈ P) (hpx : ∃ n : E3, ∀ y ∈ P, y ≠ p → ⟪y, n⟫ < ⟪p, n⟫) :
    ∃ s ∈ P, ∃ n : E3, ⟪v, n⟫ = 0 ∧ 0 < ⟪cross v p, s⟫ ∧ 0 < ⟪p, n⟫ ∧ ⟪s, n⟫ = ⟪p, n⟫ ∧
      (∀ y ∈ P, ⟪y, n⟫ ≤ ⟪p, n⟫) ∧
      (∀ y ∈ P, ⟪y, n⟫ = ⟪p, n⟫ → y ≠ p → y ≠ s →
        0 < ⟪cross v p, y⟫ ∧ 0 < ⟪cross v y, s⟫) ∧
      (∃ m : E3, ∀ y ∈ P, y ≠ s → ⟪y, m⟫ < ⟪s, m⟫) ∧
      ∀ w ∈ P, (∃ m : E3, ∀ y ∈ P, y ≠ w → ⟪y, m⟫ < ⟪w, m⟫) →
        ¬ (0 < ⟪cross v p, w⟫ ∧ 0 < ⟪cross v w, s⟫) := by
  obtain ⟨e, he⟩ := hpx
  have hne : ∃ y ∈ P, y ≠ p := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, -⟩ := exists_three_exposed v P hP hin
    by_cases hap : a = p
    · exact ⟨b, hb, fun h => hab (hap.trans h.symm)⟩
    · exact ⟨a, ha, hap⟩
  obtain ⟨s, hs, hsp, hmin, hfar⟩ := gift_wrap_choice v hv P hP p hp e he hne
  obtain ⟨hvn, hps, hpn_eq, hsn, hle⟩ := gift_wrap_line v hv P hP hin p s hp hs hsp hmin
  set n := cross (s - p) v with hn_def
  have hpn : 0 < ⟪p, n⟫ := by rw [hpn_eq]; exact hps
  -- the points of `P` on the supporting line lie on the segment from `p` to `s`
  have hseg : ∀ y ∈ P, ⟪y, n⟫ = ⟪p, n⟫ → y ≠ p → y ≠ s →
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ y - p = t • (s - p) := by
    intro y hy hyn hyp hys
    refine gift_wrap_segment v hv P hP p s e hp hs hsp he hfar y hy ?_ hyp hys
    rw [cross_anticomm_E3 v (s - p), ← hn_def, inner_neg_left, inner_sub_right,
      real_inner_comm y n, real_inner_comm p n, hyn, sub_self, neg_zero]
  refine ⟨s, hs, n, hvn, hps, hpn, hsn, hle, ?_, ?_, ?_⟩
  · intro y hy hyn hyp hys
    obtain ⟨t, ht0, ht1, hyt⟩ := hseg y hy hyn hyp hys
    have hy' : y = p + t • (s - p) := by rw [← hyt]; abel
    have hpp : ⟪cross v p, p⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right_self v p
    have hss : ⟪cross v s, s⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right_self v s
    have hsp' : ⟪cross v s, p⟫ = -⟪cross v p, s⟫ := inner_cross_antisymm v s p
    constructor
    · rw [hy', inner_add_right, real_inner_smul_right, inner_sub_right, hpp, zero_add, sub_zero]
      exact mul_pos ht0 hps
    · rw [inner_cross_antisymm v y s, hy', inner_add_right, real_inner_smul_right,
        inner_sub_right, hss, hsp']
      have : 0 < (1 - t) * ⟪cross v p, s⟫ := mul_pos (by linarith) hps
      linarith
  · refine exposed_of_lex P s n (s - p) (fun y hy => (hle y hy).trans_eq hsn.symm) ?_
    intro y hy hys hyn
    have hyn' : ⟪y, n⟫ = ⟪p, n⟫ := hyn.trans hsn
    have hd : 0 < ⟪s - p, s - p⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hsp)
    have h2 : ⟪s, s - p⟫ - ⟪p, s - p⟫ = ⟪s - p, s - p⟫ := by rw [inner_sub_left]
    by_cases hyp : y = p
    · rw [hyp]
      linarith
    · obtain ⟨t, ht0, ht1, hyt⟩ := hseg y hy hyn' hyp hys
      have h1 : ⟪y, s - p⟫ - ⟪p, s - p⟫ = t * ⟪s - p, s - p⟫ := by
        rw [← inner_sub_left, hyt, real_inner_smul_left]
      have : 0 < (1 - t) * ⟪s - p, s - p⟫ := mul_pos (by linarith) hd
      linarith
  · intro w hw hwx
    exact gift_wrap_between v P hP hin p s n hp hs hps hpn hsn hle w hw hwx

/-! ## Vertex facts -/

theorem contact_exposed {V : Type*} (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (c : ℝ) (hc : c < 1)
    (hsep : ∀ a b, a ≠ b → ⟪x a, x b⟫ ≤ c) {a b : V} (hab : a ≠ b) (h : ⟪x a, x b⟫ = c) :
    ExposedPair x a b := by
  set N := x a + x b with hN
  have hNa : ⟪x a, N⟫ = 1 + c := by
    dsimp [N]
    calc
      ⟪x a, x a + x b⟫ = ⟪x a, x a⟫ + ⟪x a, x b⟫ := by rw [inner_add_right]
      _ = ‖x a‖ ^ 2 + ⟪x a, x b⟫ := by rw [real_inner_self_eq_norm_sq]
      _ = 1 ^ 2 + c := by rw [hx a, h]
      _ = 1 + c := by norm_num
  have hNb : ⟪x b, N⟫ = 1 + c := by
    dsimp [N]
    calc
      ⟪x b, x a + x b⟫ = ⟪x b, x a⟫ + ⟪x b, x b⟫ := by rw [inner_add_right]
      _ = ⟪x b, x a⟫ + ‖x b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪x a, x b⟫ + ‖x b‖ ^ 2 := by rw [real_inner_comm (x b) (x a)]
      _ = c + 1 ^ 2 := by rw [h, hx b]
      _ = 1 + c := by norm_num; ring
  refine ⟨hab, N, ?_, ?_⟩
  · rw [hNa, hNb]
  · intro z hza hzb
    have h1 : ⟪x z, x a⟫ ≤ c := hsep z a hza
    have h2 : ⟪x z, x b⟫ ≤ c := hsep z b hzb
    have hsum : ⟪x z, N⟫ = ⟪x z, x a⟫ + ⟪x z, x b⟫ := by
      dsimp [N]
      rw [inner_add_right]
    rw [hsum, hNa]
    have hsumle : ⟪x z, x a⟫ + ⟪x z, x b⟫ ≤ c + c := add_le_add h1 h2
    have hlt : c + c < 1 + c := by linarith
    linarith

theorem no_closed_hemisphere {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hirr : ∀ v (t : E3), ⟪x v, t⟫ = 0 → t ≠ 0 → ∃ w, G.Adj v w ∧ 0 < ⟪t, x w⟫)
    (e : E3) (he : e ≠ 0) : ∃ a, 0 < ⟪x a, e⟫ := by
  by_contra! h
  -- h: ∀ a, ¬ 0 < ⟪x a, e⟫, i.e. ⟪x a, e⟫ ≤ 0
  obtain ⟨a, ha⟩ := Finite.exists_max (fun v => ⟪x v, e⟫)
  -- ha: ∀ v, ⟪x v, e⟫ ≤ ⟪x a, e⟫
  set m := ⟪x a, e⟫ with hm
  have hm_nonpos : m ≤ 0 := h a
  set t := e - m • x a with ht
  have h_inner_xt_a : ⟪x a, t⟫ = 0 := by
    dsimp [t]
    rw [inner_sub_right, inner_smul_right, hm]
    have h_self : ⟪x a, x a⟫ = 1 := by
      simp [hx a]
    rw [h_self]
    ring
  by_cases ht_zero : t = 0
  · -- case t = 0: then e = m • x a with m < 0
    have hm_neg : m < 0 := by
      by_contra! hm_nonneg
      have hm_zero : m = 0 := by linarith
      have he_zero : e = 0 := by
        dsimp [t] at ht_zero
        rw [hm_zero] at ht_zero
        simp at ht_zero
        exact ht_zero
      exact he he_zero
    obtain ⟨w, hw_adj⟩ := hne a
    have hw_ne_a : w ≠ a := by
      intro h_eq
      have h_loop : G.Adj a a := by simp [h_eq] at hw_adj
      exact (G.loopless.irrefl a) h_loop
    have hx_ne : x w ≠ x a := hinj.ne hw_ne_a
    have h_inner_lt_one : ⟪x a, x w⟫ < 1 := by
      by_contra! hge
      have h_eq_one : ⟪x a, x w⟫ = 1 := by
        have h_le_one : ⟪x a, x w⟫ ≤ 1 := by
          calc
            ⟪x a, x w⟫ ≤ ‖x a‖ * ‖x w‖ := real_inner_le_norm _ _
            _ = 1 * 1 := by rw [hx a, hx w]
            _ = 1 := by norm_num
        linarith
      have h_eq_vec : x a = x w :=
        ((inner_eq_one_iff_of_norm_eq_one (hx a) (hx w)).mp h_eq_one)
      exact hx_ne h_eq_vec.symm
    have he_eq : e = m • x a := by
      dsimp [t] at ht_zero
      exact sub_eq_zero.mp ht_zero
    have h_inner_we_gt_m : m < ⟪x w, e⟫ := by
      rw [he_eq]
      have htemp : ⟪x w, m • x a⟫ = m * ⟪x a, x w⟫ := by
        rw [inner_smul_right, real_inner_comm]
      rw [htemp]
      have : m * 1 < m * ⟪x a, x w⟫ :=
        mul_lt_mul_of_neg_left h_inner_lt_one hm_neg
      nlinarith
    have h_we_le_m : ⟪x w, e⟫ ≤ m := ha w
    linarith
  · -- case t ≠ 0
    obtain ⟨w, hw_adj, hw_pos⟩ := hirr a t h_inner_xt_a ht_zero
    have h_bound : ⟪t, x w⟫ ≤ 0 := by
      dsimp [t]
      rw [inner_sub_left]
      simp [inner_smul_left]
      have h_we_le_m : ⟪e, x w⟫ ≤ m := by
        rw [real_inner_comm]
        exact ha w
      have h_inner_le_one : ⟪x a, x w⟫ ≤ 1 := by
        calc
          ⟪x a, x w⟫ ≤ ‖x a‖ * ‖x w‖ := real_inner_le_norm _ _
          _ = 1 * 1 := by rw [hx a, hx w]
          _ = 1 := by norm_num
      have h_nonpos : m ≤ 0 := hm_nonpos
      have h_mul : m * 1 ≤ m * ⟪x a, x w⟫ :=
        mul_le_mul_of_nonpos_left h_inner_le_one h_nonpos
      have : m * 1 = m := by ring
      rw [this] at h_mul
      linarith
    linarith

/-- An argument with nonpositive real part, reduced to `[0, 2π)`, is at least `π / 2`. -/
theorem toIcoMod_arg_lower_bound {z : ℂ} (hre : z.re ≤ 0) (hz : z ≠ 0) :
    π / 2 ≤ toIcoMod Real.two_pi_pos (0 : ℝ) z.arg := by
  have harg_mem : z.arg ∈ Set.Ioc (-Real.pi) Real.pi := Complex.arg_mem_Ioc z
  rcases harg_mem with ⟨harg_gt_neg_pi, harg_le_pi⟩
  by_cases h_mid : -(π/2) < z.arg ∧ z.arg < π/2
  · rcases h_mid with ⟨hlt1, hlt2⟩
    have h_cos_pos : 0 < Real.cos z.arg := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    have h_norm_pos : 0 < ‖z‖ := (norm_pos_iff.mpr hz)
    have h_re_pos : 0 < z.re := by
      have := Complex.norm_mul_cos_arg z
      rw [← this]
      nlinarith
    linarith
  · rw [not_and_or] at h_mid
    rcases h_mid with (h_le | h_ge)
    · have h_sum_mem : z.arg + 2*π ∈ Set.Ico (0 : ℝ) (2*π) := by
        constructor <;> nlinarith
      have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = z.arg + 2*π := by
        calc
          toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = toIcoMod Real.two_pi_pos (0 : ℝ) ((z.arg + 2*π) - 2*π) := by ring_nf
          _ = toIcoMod Real.two_pi_pos (0 : ℝ) (z.arg + 2*π) := by rw [toIcoMod_sub Real.two_pi_pos (0 : ℝ) (z.arg + 2*π)]
          _ = z.arg + 2*π := by
            rw [(toIcoMod_eq_self Real.two_pi_pos).mpr]
            simpa [add_comm] using h_sum_mem
      rw [h_eq]
      nlinarith
    · have h_mem : z.arg ∈ Set.Ico (0 : ℝ) (2*π) := by
        constructor <;> nlinarith
      have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = z.arg := by
        rw [(toIcoMod_eq_self Real.two_pi_pos).mpr]
        simpa [add_comm] using h_mem
      rw [h_eq]
      nlinarith

/-- An argument with nonpositive real part, reduced to `[0, 2π)`, is at most `3π / 2`. -/
theorem toIcoMod_arg_upper_bound {z : ℂ} (hre : z.re ≤ 0) (hz : z ≠ 0) :
    toIcoMod Real.two_pi_pos (0 : ℝ) z.arg ≤ 3 * π / 2 := by
  have harg_mem : z.arg ∈ Set.Ioc (-Real.pi) Real.pi := Complex.arg_mem_Ioc z
  rcases harg_mem with ⟨harg_gt_neg_pi, harg_le_pi⟩
  by_cases h_mid : -(π/2) < z.arg ∧ z.arg < π/2
  · rcases h_mid with ⟨hlt1, hlt2⟩
    have h_cos_pos : 0 < Real.cos z.arg := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    have h_norm_pos : 0 < ‖z‖ := (norm_pos_iff.mpr hz)
    have h_re_pos : 0 < z.re := by
      have := Complex.norm_mul_cos_arg z
      rw [← this]
      nlinarith
    linarith
  · rw [not_and_or] at h_mid
    rcases h_mid with (h_le | h_ge)
    · have h_sum_mem : z.arg + 2*π ∈ Set.Ico (0 : ℝ) (2*π) := by
        constructor <;> nlinarith
      have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = z.arg + 2*π := by
        calc
          toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = toIcoMod Real.two_pi_pos (0 : ℝ) ((z.arg + 2*π) - 2*π) := by ring_nf
          _ = toIcoMod Real.two_pi_pos (0 : ℝ) (z.arg + 2*π) := by rw [toIcoMod_sub Real.two_pi_pos (0 : ℝ) (z.arg + 2*π)]
          _ = z.arg + 2*π := by
            rw [(toIcoMod_eq_self Real.two_pi_pos).mpr]
            simpa [add_comm] using h_sum_mem
      rw [h_eq]
      nlinarith
    · have h_mem : z.arg ∈ Set.Ico (0 : ℝ) (2*π) := by
        constructor <;> nlinarith
      have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) z.arg = z.arg := by
        rw [(toIcoMod_eq_self Real.two_pi_pos).mpr]
        simpa [add_comm] using h_mem
      rw [h_eq]
      nlinarith

/-- At a vertex whose consecutive corners lie in `(0, π)`, every nonzero tangent direction `t` has
a neighbour on its open side (a step of Lemma B, paper, Section 3). -/
theorem exists_pos_of_corner_lt_pi {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (_hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (v : V) (hv : ∃ w, G.Adj v w) (t : E3) (ht : ⟪x v, t⟫ = 0) (ht0 : t ≠ 0) :
    ∃ w, G.Adj v w ∧ 0 < ⟪t, x w⟫ := by
  by_contra! h
  -- h : ∀ w, G.Adj v w → ⟪t, x w⟫ ≤ 0
  have hxv : ‖x v‖ = 1 := hx v
  -- tdir (x v) t = t since ⟪x v, t⟫ = 0
  have htdir_t : Tammes15.tdir (x v) t = t := by
    dsimp [Tammes15.tdir]
    rw [ht, zero_smul, sub_zero]
  have htdir_t_nonzero : Tammes15.tdir (x v) t ≠ 0 := by
    rw [htdir_t]
    exact ht0
  -- Helper: if tdir v' a' = 0 then ocorner v' a' b' = 0
  have h_ocorner_zero_of_tdir_zero (v' a' b' : E3) (hzero : Tammes15.tdir v' a' = 0) :
      Tammes15.ocorner v' a' b' = 0 := by
    dsimp [Tammes15.ocorner]
    have hre : ⟪Tammes15.tdir v' a', Tammes15.tdir v' b'⟫ = (0 : ℝ) := by rw [hzero, inner_zero_left]
    have him : ⟪v', Tammes15.cross (Tammes15.tdir v' a') (Tammes15.tdir v' b')⟫ = (0 : ℝ) := by
      rw [hzero]; simp [Tammes15.cross]
    rw [hre, him]
    have h_arg_zero : (⟨(0 : ℝ), (0 : ℝ)⟩ : ℂ).arg = (0 : ℝ) := Complex.arg_zero
    rw [h_arg_zero]
    simp
  -- Get a dart at v from hv
  obtain ⟨w0, hw0_adj⟩ := hv
  let d0 : G.Dart := ⟨(v, w0), hw0_adj⟩
  have hd0_fst : d0.fst = v := rfl
  -- The set of darts at v
  let darts_at_v : Finset G.Dart := Finset.filter (fun (d : G.Dart) => d.fst = v) Finset.univ
  have h_nonempty : darts_at_v.Nonempty := by
    refine ⟨d0, ?_⟩
    dsimp [darts_at_v]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0_fst⟩
  -- φ(w) = ocorner (x v) t (x w)
  set φ : V → ℝ := fun w => Tammes15.ocorner (x v) t (x w) with hφ_def
  -- Get the dart d at v maximizing φ(d.snd)
  obtain ⟨d, hd_mem, hd_max⟩ := Finset.exists_max_image darts_at_v (fun d => φ d.snd) h_nonempty
  have hd_fst : d.fst = v := (Finset.mem_filter.mp hd_mem).2
  have hd_adj : G.Adj v d.snd := by
    simpa [hd_fst] using d.adj
  have h_inner_nonpos : ⟪t, x d.snd⟫ ≤ 0 := h d.snd hd_adj
  obtain ⟨hκ_pos, hκ_lt_pi⟩ := hcorner d
  rw [hd_fst] at hκ_pos hκ_lt_pi
  -- d' = R.rot d
  set d' := R.rot d with hd'_def
  have hd'_fst : d'.fst = v := by
    rw [hd'_def, R.rot_fst, hd_fst]
  set κ := Tammes15.ocorner (x v) (x d.snd) (x d'.snd) with hκ_def
  -- tdir (x v) (x d.snd) ≠ 0
  have htdir_d_nonzero : Tammes15.tdir (x v) (x d.snd) ≠ 0 := by
    intro hzero
    have hκ_zero : κ = 0 := h_ocorner_zero_of_tdir_zero (x v) (x d.snd) (x d'.snd) hzero
    rw [hκ_zero] at hκ_pos
    linarith
  -- tdir (x v) (x d'.snd) ≠ 0
  have htdir_d'_nonzero : Tammes15.tdir (x v) (x d'.snd) ≠ 0 := by
    intro hzero
    have hκ_zero : κ = 0 := by
      dsimp [κ, Tammes15.ocorner]
      have hre : ⟪Tammes15.tdir (x v) (x d.snd), Tammes15.tdir (x v) (x d'.snd)⟫ = (0 : ℝ) := by
        rw [hzero, inner_zero_right]
      have him : ⟪x v, Tammes15.cross (Tammes15.tdir (x v) (x d.snd)) (Tammes15.tdir (x v) (x d'.snd))⟫ = (0 : ℝ) := by
        rw [hzero]; simp [Tammes15.cross]
      rw [hre, him]
      have h_arg_zero : (⟨(0 : ℝ), (0 : ℝ)⟩ : ℂ).arg = (0 : ℝ) := Complex.arg_zero
      rw [h_arg_zero]
      simp
    rw [hκ_zero] at hκ_pos
    linarith
  -- Use ocorn_add
  have h_ocorn_add := Tammes15.ocorner_add (x v) t (x d.snd) (x d'.snd) hxv htdir_t_nonzero htdir_d_nonzero htdir_d'_nonzero
  -- h_ocorn_add : Tammes15.ocorner (x v) t (x d'.snd) = toIcoMod Real.two_pi_pos 0 (Tammes15.ocorner (x v) t (x d.snd) + Tammes15.ocorner (x v) (x d.snd) (x d'.snd))
  -- Simplify using φ and κ
  change φ d'.snd = toIcoMod Real.two_pi_pos 0 (φ d.snd + κ) at h_ocorn_add
  -- h_ocorn_add : φ d'.snd = toIcoMod Real.two_pi_pos 0 (φ d.snd + κ)
  -- Now derive contradiction
  have h_sum_ge : 0 ≤ φ d.snd + κ := by
    have hφ_nonneg : 0 ≤ φ d.snd := by
      unfold φ Tammes15.ocorner
      have := toIcoMod_mem_Ico' Real.two_pi_pos (Complex.arg ⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d.snd)⟫,
        ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d.snd))⟫⟩)
      exact this.1
    linarith
  by_cases h_sum_lt_two_pi : φ d.snd + κ < 2*π
  · -- Case 1: φ(d.snd) + κ < 2π
    have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) (φ d.snd + κ) = φ d.snd + κ := by
      rw [(toIcoMod_eq_self Real.two_pi_pos).mpr]
      constructor
      · exact h_sum_ge
      · linarith
    rw [h_eq] at h_ocorn_add
    have h_le : φ d'.snd ≤ φ d.snd := hd_max d' (by
      dsimp [darts_at_v]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd'_fst⟩)
    rw [h_ocorn_add] at h_le
    linarith
  · -- Case 2: φ(d.snd) + κ ≥ 2π
    have h_sum_lt_three_pi : φ d.snd + κ < 3*π := by
      have hφ_lt_two_pi : φ d.snd < 2*π := by
        unfold φ Tammes15.ocorner
        have := toIcoMod_mem_Ico' Real.two_pi_pos (Complex.arg ⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d.snd)⟫,
          ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d.snd))⟫⟩)
        exact this.2
      nlinarith
    have h_eq : toIcoMod Real.two_pi_pos (0 : ℝ) (φ d.snd + κ) = φ d.snd + κ - 2*π := by
      rw [(toIcoMod_eq_iff Real.two_pi_pos).mpr]
      constructor
      · rw [Set.mem_Ico]
        constructor
        · nlinarith
        · nlinarith
      · refine ⟨1, ?_⟩
        ring
    rw [h_eq] at h_ocorn_add
    -- Now h_ocorn_add : φ d'.snd = φ d.snd + κ - 2π
    -- We need to show φ d.snd + κ - 2π < π/2 to get a contradiction
    -- with the lower bound φ d'.snd ≥ π/2
    -- First, handle the case φ d.snd = 0 separately
    by_cases hφ_zero : φ d.snd = 0
    · -- If φ d.snd = 0, then h_ocorn_add gives φ d'.snd = κ - 2π < 0 (since κ < π)
      -- But φ d'.snd ≥ 0 (from toIcoMod_mem_Ico'), contradiction
      have hφ'_nonneg : 0 ≤ φ d'.snd := by
        unfold φ Tammes15.ocorner
        have := toIcoMod_mem_Ico' Real.two_pi_pos (Complex.arg ⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d'.snd)⟫,
          ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d'.snd))⟫⟩)
        exact this.1
      rw [h_ocorn_add] at hφ'_nonneg
      rw [hφ_zero] at hφ'_nonneg
      have : κ - 2*π < 0 := by nlinarith
      linarith
    · -- φ d.snd > 0, so the complex number for φ d.snd is nonzero
      have hz_ne_zero : (⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d.snd)⟫,
        ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d.snd))⟫⟩ : ℂ) ≠ 0 := by
        intro hz_eq
        apply hφ_zero
        unfold φ Tammes15.ocorner
        rw [hz_eq, Complex.arg_zero]
        simp
      have hz_re_nonpos : (⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d.snd)⟫,
        ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d.snd))⟫⟩ : ℂ).re ≤ 0 := by
        dsimp
        rw [htdir_t]
        dsimp [Tammes15.tdir]
        calc
          ⟪t, x d.snd - ⟪x v, x d.snd⟫ • (x v)⟫ = ⟪t, x d.snd⟫ - ⟪t, ⟪x v, x d.snd⟫ • (x v)⟫ := by rw [inner_sub_right]
          _ = ⟪t, x d.snd⟫ - ⟪x v, x d.snd⟫ * ⟪t, x v⟫ := by rw [inner_smul_right]
          _ = ⟪t, x d.snd⟫ - ⟪x v, x d.snd⟫ * 0 := by rw [real_inner_comm (x v) t, ht]
          _ = ⟪t, x d.snd⟫ := by ring
          _ ≤ 0 := h_inner_nonpos
      -- Now apply the lower bound lemma
      have h_lower : π/2 ≤ φ d.snd := by
        unfold φ Tammes15.ocorner
        exact toIcoMod_arg_lower_bound hz_re_nonpos hz_ne_zero
      -- Also need upper bound for φ d.snd
      have h_upper : φ d.snd ≤ 3*π/2 := by
        unfold φ Tammes15.ocorner
        exact toIcoMod_arg_upper_bound hz_re_nonpos hz_ne_zero
      -- Now φ d.snd + κ - 2π < 3π/2 + π - 2π = π/2
      have h_contra : φ d.snd + κ - 2*π < π/2 := by
        nlinarith
      -- But we also need a lower bound for φ d'.snd
      -- If φ d'.snd = 0, we get a contradiction as before
      by_cases hφ'_zero : φ d'.snd = 0
      · exfalso
        have hsr := sameRay_of_ocorner_eq_zero (x v) t (x d'.snd) hxv hφ'_zero
        rw [htdir_t] at hsr
        obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := hsr.exists_pos ht0 htdir_d'_nonzero
        have hd'_adj : G.Adj v d'.snd := by simpa [hd'_fst] using d'.adj
        have h1 : ⟪t, x d'.snd⟫ ≤ 0 := h d'.snd hd'_adj
        have h2 : ⟪t, tdir (x v) (x d'.snd)⟫ = ⟪t, x d'.snd⟫ := by
          simp only [tdir, inner_sub_right, real_inner_smul_right, real_inner_comm (x v) t, ht,
            mul_zero, sub_zero]
        have h3 : ⟪t, r₁ • t⟫ = ⟪t, r₂ • tdir (x v) (x d'.snd)⟫ := by rw [hr]
        rw [real_inner_smul_right, real_inner_smul_right, h2] at h3
        have h4 : 0 < ⟪t, t⟫ := real_inner_self_pos.mpr ht0
        nlinarith
      · -- φ d'.snd > 0, so its complex number is nonzero
        have hz'_ne_zero : (⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d'.snd)⟫,
          ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d'.snd))⟫⟩ : ℂ) ≠ 0 := by
          intro hz_eq
          apply hφ'_zero
          unfold φ Tammes15.ocorner
          rw [hz_eq, Complex.arg_zero]
          simp
        have hz'_re_nonpos : (⟨⟪Tammes15.tdir (x v) t, Tammes15.tdir (x v) (x d'.snd)⟫,
          ⟪x v, Tammes15.cross (Tammes15.tdir (x v) t) (Tammes15.tdir (x v) (x d'.snd))⟫⟩ : ℂ).re ≤ 0 := by
          dsimp
          rw [htdir_t]
          dsimp [Tammes15.tdir]
          have hd'_adj : G.Adj v d'.snd := by
            simpa [hd'_fst] using d'.adj
          have h_inner_nonpos_d' : ⟪t, x d'.snd⟫ ≤ 0 := h d'.snd hd'_adj
          calc
            ⟪t, x d'.snd - ⟪x v, x d'.snd⟫ • (x v)⟫ = ⟪t, x d'.snd⟫ - ⟪t, ⟪x v, x d'.snd⟫ • (x v)⟫ := by rw [inner_sub_right]
            _ = ⟪t, x d'.snd⟫ - ⟪x v, x d'.snd⟫ * ⟪t, x v⟫ := by rw [inner_smul_right]
            _ = ⟪t, x d'.snd⟫ - ⟪x v, x d'.snd⟫ * 0 := by rw [real_inner_comm (x v) t, ht]
            _ = ⟪t, x d'.snd⟫ := by ring
            _ ≤ 0 := h_inner_nonpos_d'
        have h_lower' : π/2 ≤ φ d'.snd := by
          unfold φ Tammes15.ocorner
          exact toIcoMod_arg_lower_bound hz'_re_nonpos hz'_ne_zero
        rw [h_ocorn_add] at h_lower'
        linarith

theorem three_le_degree {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (v : V) (hv : ∃ w, G.Adj v w) : 3 ≤ G.degree v := by
  -- Let D be the set of darts whose tail is v
  let D := Finset.univ.filter (fun e : G.Dart => e.fst = v)
  have hDcard : D.card = G.degree v := by
    simpa [D] using SimpleGraph.dart_fst_fiber_card_eq_degree G v
  have hDnonempty : D.Nonempty := by
    rcases hv with ⟨w, hw⟩
    refine ⟨⟨(v, w), hw⟩, ?_⟩
    simp [D]
  have hD_rot_maps : ∀ e ∈ D, R.rot e ∈ D := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨_, hefst⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [R.rot_fst e, hefst]
  have hD_no_fixed : ∀ e ∈ D, R.rot e ≠ e := by
    intro e he h_eq
    have hcorner_e := hcorner e
    rcases hcorner_e with ⟨hpos, hlt⟩
    have hzero : ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) = 0 := by
      rw [h_eq]
      apply ocorner_eq_zero_of_sameRay (x e.fst) (x e.snd) (x e.snd)
      exact SameRay.rfl
    linarith
  have hD_card_ge_2 : 2 ≤ D.card := by
    by_contra! h
    have hcard_lt_2 : D.card < 2 := by omega
    have hcard_pos : 0 < D.card := by
      rwa [Finset.card_pos]
    have hcard_eq_1 : D.card = 1 := by omega
    rcases (Finset.card_eq_one.mp hcard_eq_1) with ⟨d, hd⟩
    have h_rot_d_in_D : R.rot d ∈ D := hD_rot_maps d (by rw [hd]; simp)
    rw [hd] at h_rot_d_in_D
    have h_rot_d_eq_d : R.rot d = d := by
      simpa using h_rot_d_in_D
    exact hD_no_fixed d (by rw [hd]; simp) h_rot_d_eq_d
  have hD_card_ne_2 : D.card ≠ 2 := by
    intro hcard_eq_2
    rcases (Finset.card_eq_two.mp hcard_eq_2) with ⟨d, d', h_ne, hd_eq⟩
    have hd_fst : d.fst = v := by
      have : d ∈ D := by rw [hd_eq]; simp
      rcases Finset.mem_filter.mp this with ⟨_, h⟩
      exact h
    have hd'_fst : d'.fst = v := by
      have : d' ∈ D := by rw [hd_eq]; simp
      rcases Finset.mem_filter.mp this with ⟨_, h⟩
      exact h
    have h_rot_d_in_D : R.rot d ∈ D := hD_rot_maps d (by rw [hd_eq]; simp)
    have h_rot_d'_in_D : R.rot d' ∈ D := hD_rot_maps d' (by rw [hd_eq]; simp)
    rw [hd_eq] at h_rot_d_in_D h_rot_d'_in_D
    have h_rot_d_eq_d' : R.rot d = d' := by
      rcases Finset.mem_insert.mp h_rot_d_in_D with (h | h)
      · exfalso; exact hD_no_fixed d (by rw [hd_eq]; simp) h
      · exact Finset.mem_singleton.mp h
    have h_rot_d'_eq_d : R.rot d' = d := by
      rcases Finset.mem_insert.mp h_rot_d'_in_D with (h | h)
      · exact h
      · exfalso; exact hD_no_fixed d' (by rw [hd_eq]; simp) (Finset.mem_singleton.mp h)
    set u := d.snd with hu_def
    set u' := d'.snd with hu'_def
    have hcorner_d := hcorner d
    have hcorner_d' := hcorner d'
    rcases hcorner_d with ⟨hκ_pos, hκ_lt⟩
    rcases hcorner_d' with ⟨hκ'_pos, hκ'_lt⟩
    -- Rewrite hκ_pos and hκ_lt using the definitions of u and u'
    have hκ_pos' : 0 < ocorner (x v) (x u) (x u') := by
      simpa [hd_fst, hu_def, h_rot_d_eq_d', hu'_def] using hκ_pos
    have hκ_lt' : ocorner (x v) (x u) (x u') < π := by
      simpa [hd_fst, hu_def, h_rot_d_eq_d', hu'_def] using hκ_lt
    have hκ'_pos' : 0 < ocorner (x v) (x u') (x u) := by
      simpa [hd'_fst, hu'_def, h_rot_d'_eq_d, hu_def] using hκ'_pos
    have hκ'_lt' : ocorner (x v) (x u') (x u) < π := by
      simpa [hd'_fst, hu'_def, h_rot_d'_eq_d, hu_def] using hκ'_lt
    -- The tangent parts are nonzero
    have htdir_ne_zero : tdir (x v) (x u) ≠ 0 := by
      intro hzero
      have h_sameRay : SameRay ℝ (tdir (x v) (x u)) (tdir (x v) (x u')) := by
        rw [hzero]
        exact SameRay.zero_left _
      have hzero_occ : ocorner (x v) (x u) (x u') = 0 :=
        ocorner_eq_zero_of_sameRay (x v) (x u) (x u') h_sameRay
      rw [hzero_occ] at hκ_pos'
      linarith
    have htdir_ne_zero' : tdir (x v) (x u') ≠ 0 := by
      intro hzero
      have h_sameRay : SameRay ℝ (tdir (x v) (x u')) (tdir (x v) (x u)) := by
        rw [hzero]
        exact SameRay.zero_left _
      have hzero_occ : ocorner (x v) (x u') (x u) = 0 :=
        ocorner_eq_zero_of_sameRay (x v) (x u') (x u) h_sameRay
      rw [hzero_occ] at hκ'_pos'
      linarith
    -- Apply ocorner_add
    have h_add := ocorner_add (x v) (x u) (x u') (x u) (hx v) htdir_ne_zero htdir_ne_zero'
      htdir_ne_zero
    -- LHS: ocorner (x v) (x u) (x u) = 0
    have hLHS : ocorner (x v) (x u) (x u) = 0 :=
      ocorner_eq_zero_of_sameRay (x v) (x u) (x u) SameRay.rfl
    rw [hLHS] at h_add
    -- RHS: toIcoMod two_pi_pos 0 (ocorner (x v) (x u) (x u') + ocorner (x v) (x u') (x u))
    set κ := ocorner (x v) (x u) (x u') with hκ_def
    set κ' := ocorner (x v) (x u') (x u) with hκ'_def
    have h_sum_pos : 0 < κ + κ' := by linarith
    have h_sum_lt_two_pi : κ + κ' < 2 * π := by linarith
    have h_sum_nonneg : 0 ≤ κ + κ' := by linarith
    have h_sum_lt_two_pi' : κ + κ' < 0 + 2 * π := by
      simpa using h_sum_lt_two_pi
    have h_toIcoMod_eq : toIcoMod Real.two_pi_pos 0 (κ + κ') = κ + κ' := by
      rw [toIcoMod_eq_self Real.two_pi_pos]
      exact ⟨h_sum_nonneg, h_sum_lt_two_pi'⟩
    rw [hκ_def, hκ'_def] at h_add
    rw [h_toIcoMod_eq] at h_add
    -- Now h_add says 0 = κ + κ', but both are positive
    linarith
  -- Combine: D.card ≥ 2 and D.card ≠ 2, so D.card ≥ 3
  have hD_card_ge_3 : 3 ≤ D.card := by
    have : 2 ≤ D.card := hD_card_ge_2
    have : D.card ≠ 2 := hD_card_ne_2
    omega
  -- Finally, D.card = G.degree v
  rw [← hDcard]
  exact hD_card_ge_3

theorem face_period_ge_three {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3)
    (hpos : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd)) (e : G.Dart) :
    3 ≤ Function.minimalPeriod R.face e := by
  have h_finite : Finite G.Dart := by
    infer_instance
  have h_inj : Function.Injective (R.face : G.Dart → G.Dart) :=
    (R.face : Equiv.Perm G.Dart).injective
  have h_periodic : e ∈ Function.periodicPts (R.face : G.Dart → G.Dart) :=
    Function.Injective.mem_periodicPts h_inj e
  have h_pos : 0 < Function.minimalPeriod (R.face : G.Dart → G.Dart) e :=
    Function.minimalPeriod_pos_of_mem_periodicPts h_periodic
  have h_rot_symm_fst : ∀ (d : G.Dart), (R.rot.symm d).fst = d.fst := by
    intro d
    have := R.rot_fst (R.rot.symm d)
    simpa [Equiv.apply_symm_apply] using this.symm
  have h_face_fst : ∀ (d : G.Dart), ((R.face : G.Dart → G.Dart) d).fst = d.snd := by
    intro d
    have : (R.face : G.Dart → G.Dart) d = R.rot.symm (SimpleGraph.Dart.symm d) := by
      simp [RotSys.face, Equiv.trans_apply, Function.Involutive.coe_toPerm]
    simp [this, h_rot_symm_fst]
  have h_ne_one : Function.minimalPeriod (R.face : G.Dart → G.Dart) e ≠ 1 := by
    intro h_eq1
    have h_fixed : Function.IsFixedPt (R.face : G.Dart → G.Dart) e :=
      ((Function.minimalPeriod_eq_one_iff_isFixedPt (f := (R.face : G.Dart → G.Dart)) (x := e)).mp h_eq1)
    have h_face_eq : (R.face : G.Dart → G.Dart) e = e := h_fixed
    have h_fst_eq : e.fst = e.snd := by
      calc
        e.fst = ((R.face : G.Dart → G.Dart) e).fst := by rw [h_face_eq]
        _ = e.snd := h_face_fst e
    exact e.fst_ne_snd h_fst_eq
  have h_ne_two : Function.minimalPeriod (R.face : G.Dart → G.Dart) e ≠ 2 := by
    intro h_eq2
    have h_iter : (R.face : G.Dart → G.Dart)^[Function.minimalPeriod (R.face : G.Dart → G.Dart) e] e = e :=
      Function.iterate_minimalPeriod (f := (R.face : G.Dart → G.Dart)) (x := e)
    rw [h_eq2] at h_iter
    have h_iter_sq : (R.face : G.Dart → G.Dart)^[2] e = (R.face : G.Dart → G.Dart) ((R.face : G.Dart → G.Dart) e) := by
      simp
    rw [h_iter_sq] at h_iter
    set f := (R.face : G.Dart → G.Dart) e with hf_def
    have h_face_f : (R.face : G.Dart → G.Dart) f = e := h_iter
    have h_f_snd_eq_e_fst : f.snd = e.fst := by
      calc
        f.snd = ((R.face : G.Dart → G.Dart) f).fst := by rw [h_face_fst f]
        _ = e.fst := by rw [h_face_f]
    have h_f_eq_e_symm : f = e.symm := by
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · -- fst
        dsimp [f]
        simpa using h_face_fst e
      · -- snd
        dsimp [f]
        simpa using h_f_snd_eq_e_fst
    have h_rot_f_eq_e_symm : R.rot f = e.symm := by
      rw [hf_def]
      -- R.rot (R.face e) = R.rot (R.rot.symm (e.symm)) = e.symm
      have h_face_eq' : (R.face : G.Dart → G.Dart) e = R.rot.symm (SimpleGraph.Dart.symm e) := by
        simp [RotSys.face, Equiv.trans_apply, Function.Involutive.coe_toPerm]
      rw [h_face_eq']
      simp
    have h_rot_e_symm_eq_e_symm : R.rot e.symm = e.symm := by
      calc
        R.rot e.symm = R.rot f := by rw [h_f_eq_e_symm]
        _ = e.symm := h_rot_f_eq_e_symm
    have h_contra := hpos e.symm
    rw [h_rot_e_symm_eq_e_symm] at h_contra
    have h_zero : ocorner (x e.symm.fst) (x e.symm.snd) (x e.symm.snd) = 0 := by
      apply ocorner_eq_zero_of_sameRay
      exact SameRay.refl _
    rw [h_zero] at h_contra
    exact lt_irrefl 0 h_contra
  have h_ge_3 : 3 ≤ Function.minimalPeriod (R.face : G.Dart → G.Dart) e := by
    by_contra! h_lt
    have h_le_2 : Function.minimalPeriod (R.face : G.Dart → G.Dart) e ≤ 2 := by omega
    have h_pos' : 0 < Function.minimalPeriod (R.face : G.Dart → G.Dart) e := h_pos
    have h_cases : Function.minimalPeriod (R.face : G.Dart → G.Dart) e = 1 ∨ Function.minimalPeriod (R.face : G.Dart → G.Dart) e = 2 := by
      omega
    rcases h_cases with (h | h)
    · exact h_ne_one h
    · exact h_ne_two h
  exact h_ge_3

/-! ## The hemisphere lemma for walks turning left -/

theorem pole_sdist (a b c : E3) (hb : ‖b‖ = 1) (hpos : 0 < ⟪cross b c, a⟫) :
    sdist (‖cross a b‖⁻¹ • cross a b) (‖cross b c‖⁻¹ • cross b c) = π - ocorner b c a := by
  obtain ⟨h0, hπ⟩ := (ocorner_pos_lt_pi_iff b c a).mpr hpos
  obtain ⟨e, he, hbe⟩ := exists_unit_orthogonal b
  set ta := tdir b a with hta
  set tc := tdir b c with htc
  have hcos : Real.cos (ocorner b c a) = ⟪tc, ta⟫ / (‖tc‖ * ‖ta‖) := by
    set q := conj (tcoord b e c) * tcoord b e a with hq
    have hq0 : q ≠ 0 := by
      intro h
      have h' : ocorner b c a = 0 := by
        rw [ocorner_eq_arg b e c a hb he hbe, ← hq, h, Complex.arg_zero]
        exact toIcoMod_apply_left _ _
      linarith
    have hre : q.re = ⟪tc, ta⟫ := by
      rw [hq, htc, hta, inner_tdir_frame b e c a hb he hbe]
      simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hnorm : ‖q‖ = ‖tc‖ * ‖ta‖ := by
      rw [hq, norm_mul, Complex.norm_conj, htc, hta, norm_tdir_eq_norm_tcoord b e c hb he hbe,
        norm_tdir_eq_norm_tcoord b e a hb he hbe]
    rw [ocorner_eq_arg b e c a hb he hbe, ← hq, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul,
      Real.cos_sub_int_mul_two_pi, Complex.cos_arg hq0, hre, hnorm]
  have hab : ⟪cross a b, cross b c⟫ = -⟪ta, tc⟫ := by
    have hbc : ⟪cross a b, cross b c⟫ = ⟪a, b⟫ * ⟪b, c⟫ - ⟪a, c⟫ * ⟪b, b⟫ := by
      simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
        crossProduct, star_trivial]
      simp
      ring
    rw [hbc, hta, htc, inner_tdir b a c hb, real_inner_self_eq_norm_sq, hb, real_inner_comm a b]
    ring
  have hna : ‖cross a b‖ = ‖ta‖ := by
    have h1 : ‖cross a b‖ ^ 2 = ‖ta‖ ^ 2 := by
      rw [norm_cross_sq, hta, norm_tdir_sq b a hb, hb, real_inner_comm a b]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hnc : ‖cross b c‖ = ‖tc‖ := by
    have h1 : ‖cross b c‖ ^ 2 = ‖tc‖ ^ 2 := by
      rw [norm_cross_sq, htc, norm_tdir_sq b c hb, hb]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hinner : ⟪‖cross a b‖⁻¹ • cross a b, ‖cross b c‖⁻¹ • cross b c⟫ =
      Real.cos (π - ocorner b c a) := by
    rw [real_inner_smul_left, real_inner_smul_right, hab, hna, hnc, Real.cos_pi_sub, hcos,
      real_inner_comm ta tc]
    ring
  unfold sdist
  rw [hinner, Real.arccos_cos (by linarith) (by linarith)]

/-- The triangle inequality along a path of unit vectors. -/
theorem sdist_chain_le (p : ℕ → E3) (hp : ∀ k, ‖p k‖ = 1) (a b : ℕ) (hab : a ≤ b) :
    sdist (p a) (p b) ≤ ∑ k ∈ Finset.Ico a b, sdist (p k) (p (k + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => rw [sdist_self _ (hp a), Finset.Ico_self, Finset.sum_empty]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    exact (sdist_triangle _ _ _ (hp a) (hp b) (hp (b + 1))).trans (by linarith)

/-- A point of the minor arc `p q` at distance `t` from `p`. -/
theorem exists_arc_point (p q : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : sdist p q < π)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ sdist p q) :
    ∃ B : E3, ‖B‖ = 1 ∧ sdist p B = t ∧ sdist B q = sdist p q - t := by
  set d := sdist p q with hd_def
  have hd_nonneg : 0 ≤ d := by
    rw [hd_def, Tammes15.sdist]
    exact Real.arccos_nonneg _
  have hd_lt_pi : d < π := hpq
  have hcos_d : cos d = ⟪p, q⟫ := by
    rw [hd_def, Tammes15.sdist]
    have h_abs := abs_real_inner_le_norm p q
    rw [hp, hq] at h_abs
    have h_abs' : |⟪p, q⟫| ≤ 1 := by
      simpa using h_abs
    have hlow : -1 ≤ ⟪p, q⟫ := (abs_le.mp h_abs').1
    have hhigh : ⟪p, q⟫ ≤ 1 := (abs_le.mp h_abs').2
    exact Real.cos_arccos hlow hhigh
  by_cases hd_zero : d = 0
  · -- case d = 0: then p = q and t = 0, take B = p
    have h_inner_pq : ⟪p, q⟫ = 1 := by
      have := congrArg cos hd_zero
      rw [Real.cos_zero, hcos_d] at this
      exact this
    have hpq_eq : p = q := by
      have h_eq_norm_sq : ‖p - q‖^2 = 0 := by
        calc
          ‖p - q‖^2 = ⟪p - q, p - q⟫ := by rw [real_inner_self_eq_norm_sq]
          _ = ⟪p, p⟫ - 2 * ⟪p, q⟫ + ⟪q, q⟫ := by rw [real_inner_sub_sub_self]
          _ = ‖p‖^2 - 2 * ⟪p, q⟫ + ‖q‖^2 := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
          _ = 1 - 2 * 1 + 1 := by rw [hp, hq, h_inner_pq]; ring
          _ = 0 := by ring
      have h_norm_zero : ‖p - q‖ = 0 := by nlinarith
      exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
    have ht_zero : t = 0 := by
      rw [hd_zero] at ht1
      linarith
    refine ⟨p, hp, ?_, ?_⟩
    · rw [ht_zero, Tammes15.sdist, hpq_eq]
      rw [real_inner_self_eq_norm_sq, hq]
      simp
    · rw [ht_zero, hd_zero, sub_self, Tammes15.sdist, hpq_eq]
      rw [real_inner_self_eq_norm_sq, hq]
      simp
  · -- case d > 0
    have hd_pos : 0 < d := by
      by_contra! h
      have h_eq : d = 0 := le_antisymm h hd_nonneg
      exact hd_zero h_eq
    have hsin_d_pos : 0 < sin d :=
      Real.sin_pos_of_mem_Ioo ⟨hd_pos, hd_lt_pi⟩
    have hsin_d_ne_zero : sin d ≠ 0 := by linarith
    set α := sin (d - t) / sin d with hα_def
    set β := sin t / sin d with hβ_def
    set B := α • p + β • q with hB_def
    have hkey : sin (d - t)^2 + sin t ^ 2 + 2 * sin (d - t) * sin t * cos d = sin d ^ 2 := by
      rw [Real.sin_sub d t]
      nlinarith [Real.sin_sq_add_cos_sq d, Real.sin_sq_add_cos_sq t]
    have hB_norm_sq : ‖B‖^2 = 1 := by
      rw [hB_def]
      rw [← real_inner_self_eq_norm_sq]
      have h_inner_expand : ⟪α • p + β • q, α • p + β • q⟫ = α^2 + β^2 + 2 * α * β * cos d := by
        calc
          ⟪α • p + β • q, α • p + β • q⟫ = ⟪α • p, α • p⟫ + 2 * ⟪α • p, β • q⟫ + ⟪β • q, β • q⟫ := by
            rw [real_inner_add_add_self]
          _ = ((α * α) * ⟪p, p⟫) + 2 * ((α * β) * ⟪p, q⟫) + ((β * β) * ⟪q, q⟫) := by
            have h1 : ⟪α • p, α • p⟫ = (α * α) * ⟪p, p⟫ := by
              calc
                ⟪α • p, α • p⟫ = α * ⟪p, α • p⟫ := by rw [real_inner_smul_left]
                _ = α * (α * ⟪p, p⟫) := by rw [real_inner_smul_right]
                _ = (α * α) * ⟪p, p⟫ := by ring
            have h2 : ⟪α • p, β • q⟫ = (α * β) * ⟪p, q⟫ := by
              calc
                ⟪α • p, β • q⟫ = α * ⟪p, β • q⟫ := by rw [real_inner_smul_left]
                _ = α * (β * ⟪p, q⟫) := by rw [real_inner_smul_right]
                _ = (α * β) * ⟪p, q⟫ := by ring
            have h3 : ⟪β • q, β • q⟫ = (β * β) * ⟪q, q⟫ := by
              calc
                ⟪β • q, β • q⟫ = β * ⟪q, β • q⟫ := by rw [real_inner_smul_left]
                _ = β * (β * ⟪q, q⟫) := by rw [real_inner_smul_right]
                _ = (β * β) * ⟪q, q⟫ := by ring
            rw [h1, h2, h3]
          _ = α^2 * ⟪p, p⟫ + 2 * α * β * ⟪p, q⟫ + β^2 * ⟪q, q⟫ := by ring
          _ = α^2 * ‖p‖^2 + 2 * α * β * ⟪p, q⟫ + β^2 * ‖q‖^2 := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
          _ = α^2 * 1^2 + 2 * α * β * cos d + β^2 * 1^2 := by rw [hp, hq, hcos_d]
          _ = α^2 + β^2 + 2 * α * β * cos d := by ring
      rw [h_inner_expand]
      rw [hα_def, hβ_def]
      field_simp [hsin_d_ne_zero]
      nlinarith
    have hB_norm : ‖B‖ = 1 := by
      have h_nonneg : 0 ≤ ‖B‖ := norm_nonneg _
      nlinarith
    have h_inner_pB : ⟪p, B⟫ = cos t := by
      rw [hB_def]
      calc
        ⟪p, α • p + β • q⟫ = ⟪p, α • p⟫ + ⟪p, β • q⟫ := by rw [inner_add_right]
        _ = α * ⟪p, p⟫ + β * ⟪p, q⟫ := by simp [real_inner_smul_right]
        _ = α * ‖p‖^2 + β * cos d := by rw [real_inner_self_eq_norm_sq, hcos_d]
        _ = α * 1^2 + β * cos d := by rw [hp]
        _ = α + β * cos d := by ring
        _ = (sin (d - t) / sin d) + (sin t / sin d) * cos d := by rw [hα_def, hβ_def]
        _ = (sin (d - t) + sin t * cos d) / sin d := by ring
        _ = (sin d * cos t) / sin d := by
          rw [Real.sin_sub d t]
          ring
        _ = cos t := by field_simp [hsin_d_ne_zero]
    have h_inner_Bq : ⟪B, q⟫ = cos (d - t) := by
      rw [hB_def]
      have h_sin_sq_eq : 1 - cos d ^ 2 = sin d ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq d]
      calc
        ⟪α • p + β • q, q⟫ = ⟪α • p, q⟫ + ⟪β • q, q⟫ := by rw [inner_add_left]
        _ = α * ⟪p, q⟫ + β * ⟪q, q⟫ := by simp [real_inner_smul_left]
        _ = α * cos d + β * ‖q‖^2 := by rw [hcos_d, real_inner_self_eq_norm_sq]
        _ = α * cos d + β * 1^2 := by rw [hq]
        _ = α * cos d + β := by ring
        _ = (sin (d - t) / sin d) * cos d + (sin t / sin d) := by rw [hα_def, hβ_def]
        _ = (sin (d - t) * cos d + sin t) / sin d := by ring
        _ = (sin d * cos (d - t)) / sin d := by
          calc
            (sin (d - t) * cos d + sin t) / sin d
                = ((sin d * cos t - cos d * sin t) * cos d + sin t) / sin d := by rw [Real.sin_sub d t]
            _ = (sin d * cos t * cos d - cos d ^ 2 * sin t + sin t) / sin d := by ring
            _ = (sin d * cos d * cos t + sin t * (1 - cos d ^ 2)) / sin d := by ring
            _ = (sin d * cos d * cos t + sin t * sin d ^ 2) / sin d := by rw [h_sin_sq_eq]
            _ = (sin d * (cos d * cos t + sin d * sin t)) / sin d := by ring
            _ = (sin d * cos (d - t)) / sin d := by rw [Real.cos_sub d t]
        _ = cos (d - t) := by field_simp [hsin_d_ne_zero]
    have ht_le_pi : t ≤ π := by linarith
    have hdt_nonneg : 0 ≤ d - t := by linarith
    have hdt_le_pi : d - t ≤ π := by linarith
    have hsdist_pB : sdist p B = t := by
      rw [Tammes15.sdist]
      apply Real.arccos_eq_of_eq_cos ht0 ht_le_pi
      rw [h_inner_pB]
    have hsdist_Bq : sdist B q = d - t := by
      rw [Tammes15.sdist]
      apply Real.arccos_eq_of_eq_cos hdt_nonneg hdt_le_pi
      rw [h_inner_Bq]
    exact ⟨B, hB_norm, hsdist_pB, hsdist_Bq⟩

/-- The minor arc `p q` crosses the plane `M⊥` when `p` is above it and `q` is not. -/
theorem exists_cross_point (p q M : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : sdist p q < π)
    (hpM : 0 < ⟪p, M⟫) (hqM : ⟪q, M⟫ ≤ 0) :
    ∃ C : E3, ‖C‖ = 1 ∧ ⟪C, M⟫ = 0 ∧ sdist p C + sdist C q = sdist p q := by
  set l := -⟪q, M⟫ with hl_def
  have hl_nonneg : 0 ≤ l := by
    linarith
  set m := ⟪p, M⟫ with hm_def
  have hm_pos : 0 < m := hpM
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  set c := l • p + m • q with hc_def
  have hc_inner : ⟪c, M⟫ = 0 := by
    dsimp [c]
    simp [inner_add_left, inner_smul_left, hl_def, hm_def]
    ring
  have hp_ne_zero : p ≠ 0 := by
    intro hzero
    have : ‖p‖ = 0 := by simp [hzero]
    linarith
  have hq_ne_zero : q ≠ 0 := by
    intro hzero
    have : ‖q‖ = 0 := by simp [hzero]
    linarith
  have hc_ne_zero : c ≠ 0 := by
    intro hzero
    have hzero' : l • p + m • q = 0 := hzero
    by_cases hl_zero : l = 0
    · -- l = 0, then m • q = 0, so q = 0, contradiction
      have hmq : m • q = 0 := by
        simpa [hl_zero] using hzero'
      rcases smul_eq_zero.mp hmq with (hmzero | hqzero)
      · exfalso; linarith
      · exact hq_ne_zero hqzero
    · -- l > 0, then q = -(l/m) • p, so ‖q‖ = ‖p‖ = 1, and q = -p
      have hl_pos : 0 < l := lt_of_le_of_ne hl_nonneg (Ne.symm hl_zero)
      have hq_eq : m • q = -l • p := by
        simpa [neg_smul] using eq_neg_of_add_eq_zero_right hzero'
      have hq_eq' : q = (-l / m) • p := by
        calc
          q = (m⁻¹ • (m • q)) := by
            simp [hm_pos.ne.symm]
          _ = (m⁻¹ • (-l • p)) := by rw [hq_eq]
          _ = ((-l) * m⁻¹) • p := by simp [smul_smul, mul_comm]
          _ = (-l / m) • p := by ring_nf
      have h_abs : |-l / m| = 1 := by
        calc
          |-l / m| = |-l / m| * 1 := by ring
          _ = |-l / m| * ‖p‖ := by rw [hp]
          _ = ‖(-l / m)‖ * ‖p‖ := by rw [Real.norm_eq_abs]
          _ = ‖(-l / m) • p‖ := by rw [norm_smul]
          _ = ‖q‖ := by rw [← hq_eq']
          _ = 1 := hq
      have h_neg : (-l / m : ℝ) < 0 := by
        refine div_neg_of_neg_of_pos ?_ hm_pos
        linarith
      have h_abs_val : (-l / m : ℝ) = -1 := by
        rw [abs_of_neg h_neg] at h_abs
        linarith
      have hq_eq_neg_p : q = -p := by
        calc
          q = (-l / m) • p := hq_eq'
          _ = (-1) • p := by simp [h_abs_val]
          _ = -p := by simp
      -- Now sdist p q = sdist p (-p) = π, contradicting hpq
      have hsdist_pq : sdist p q = π := by
        rw [hq_eq_neg_p, sdist_neg_right, sdist_self p hp, sub_zero]
      linarith
  set C := (‖c‖⁻¹ : ℝ) • c with hC_def
  have hC_norm : ‖C‖ = 1 := by
    dsimp [C]
    rw [norm_smul, norm_inv, norm_norm]
    field_simp [norm_ne_zero_iff.mpr hc_ne_zero]
  have hC_inner : ⟪C, M⟫ = 0 := by
    dsimp [C]
    simp [inner_smul_left, hc_inner]
  have h_sdist_eq_angle_pC : sdist p C = angle p C :=
    sdist_eq_angle p C hp hC_norm
  have h_sdist_eq_angle_Cq : sdist C q = angle C q :=
    sdist_eq_angle C q hC_norm hq
  have h_sdist_eq_angle_pq : sdist p q = angle p q :=
    sdist_eq_angle p q hp hq
  have h_angle_add : angle p c + angle c q = angle p q := by
    apply angle_add_of_cone p q hp_ne_zero hq_ne_zero l m hl_nonneg hm_nonneg
    simpa [c] using hc_ne_zero
  -- Now we need angle p C + angle C q = angle p q
  -- C = ‖c‖⁻¹ • c, and ‖c‖⁻¹ > 0
  have h_norm_c_pos : 0 < ‖c‖ := by
    apply norm_pos_iff.mpr
    exact hc_ne_zero
  have h_inv_pos : 0 < (‖c‖⁻¹ : ℝ) := inv_pos.mpr h_norm_c_pos
  have h_angle_pC : angle p C = angle p c := by
    dsimp [C]
    simpa using (InnerProductGeometry.angle_smul_right_of_pos h_inv_pos (x := p) (y := c))
  have h_angle_Cq : angle C q = angle c q := by
    dsimp [C]
    simpa using (InnerProductGeometry.angle_smul_left_of_pos h_inv_pos (x := c) (y := q))
  refine ⟨C, hC_norm, hC_inner, ?_⟩
  calc
    sdist p C + sdist C q = angle p C + angle C q := by
      simp [h_sdist_eq_angle_pC, h_sdist_eq_angle_Cq]
    _ = angle p c + angle c q := by simp [h_angle_pC, h_angle_Cq]
    _ = angle p q := h_angle_add
    _ = sdist p q := by rw [h_sdist_eq_angle_pq]

/-- A point of the great circle orthogonal to `A + B` is at total distance `π` from `A` and
`B`. -/
theorem sdist_add_eq_pi (A B C : E3) (hC : ⟪C, A + B⟫ = 0) :
    sdist A C + sdist C B = π := by
  have hinner : ⟪C, B⟫ = -⟪C, A⟫ := by
    have hsum : ⟪C, A⟫ + ⟪C, B⟫ = 0 := by
      simpa [inner_add_right] using hC
    linarith
  calc
    sdist A C + sdist C B = arccos ⟪A, C⟫ + arccos ⟪C, B⟫ := rfl
    _ = arccos ⟪A, C⟫ + arccos (-⟪C, A⟫) := by rw [hinner]
    _ = arccos ⟪A, C⟫ + arccos (-⟪A, C⟫) := by rw [real_inner_comm C A]
    _ = arccos ⟪A, C⟫ + (π - arccos ⟪A, C⟫) := by rw [Real.arccos_neg]
    _ = π := by ring

/-- A path from a point above the plane `M⊥` to a point not above it passes through the plane. -/
theorem path_cross (M : E3) (m : ℕ) (p : ℕ → E3) (hp : ∀ k, ‖p k‖ = 1)
    (hshort : ∀ k < m, sdist (p k) (p (k + 1)) < π) (h0 : 0 < ⟪p 0, M⟫)
    (i : ℕ) (him : i ≤ m) (hi : ⟪p i, M⟫ ≤ 0) :
    ∃ C : E3, ‖C‖ = 1 ∧ ⟪C, M⟫ = 0 ∧
      sdist (p 0) C + sdist C (p m) ≤ ∑ k ∈ Finset.range m, sdist (p k) (p (k + 1)) := by
  have h_exists : ∃ n, ⟪p n, M⟫ ≤ 0 := ⟨i, hi⟩
  set j := Nat.find h_exists with hj_def
  have hj_spec : ⟪p j, M⟫ ≤ 0 := Nat.find_spec h_exists
  have hj_le_i : j ≤ i := Nat.find_min' h_exists hi
  have hj_le_m : j ≤ m := le_trans hj_le_i him
  have hj_ne_zero : j ≠ 0 := by
    intro hzero
    rw [hzero] at hj_spec
    linarith
  rcases Nat.exists_eq_succ_of_ne_zero hj_ne_zero with ⟨k, hk⟩
  have hk_lt_m : k < m := by
    have hk_succ_le_m : k.succ ≤ m := by
      rw [← hk]
      exact hj_le_m
    omega
  have hk_pos : 0 < ⟪p k, M⟫ := by
    by_contra! hle
    have hk_lt_j : k < j := by
      rw [hk]
      omega
    have h_contra := Nat.find_min h_exists hk_lt_j
    exact h_contra hle
  have hshort_k : sdist (p k) (p (k + 1)) < π := hshort k hk_lt_m
  have h_next_M : ⟪p (k + 1), M⟫ ≤ 0 := by
    simpa [hk] using hj_spec
  rcases exists_cross_point (p k) (p (k + 1)) M (hp k) (hp (k + 1)) hshort_k hk_pos h_next_M
    with ⟨C, hC_norm, hC_M, hC_dist⟩
  refine ⟨C, hC_norm, hC_M, ?_⟩
  have h_tri1 : sdist (p 0) C ≤ sdist (p 0) (p k) + sdist (p k) C :=
    sdist_triangle (p 0) (p k) C (hp 0) (hp k) hC_norm
  have h_tri2 : sdist C (p m) ≤ sdist C (p (k + 1)) + sdist (p (k + 1)) (p m) :=
    sdist_triangle C (p (k + 1)) (p m) hC_norm (hp (k + 1)) (hp m)
  have h_chain1 : sdist (p 0) (p k) ≤ ∑ x ∈ Finset.Ico 0 k, sdist (p x) (p (x + 1)) := by
    by_cases hk0 : k = 0
    · rw [hk0]
      have hself : sdist (p 0) (p 0) = 0 := by
        simp [Tammes15.sdist, hp 0]
      rw [hself]
      simp
    · have h0k : 0 ≤ k := Nat.zero_le k
      exact sdist_chain_le p hp 0 k h0k
  have h_chain2 : sdist (p (k + 1)) (p m) ≤ ∑ x ∈ Finset.Ico (k + 1) m, sdist (p x) (p (x + 1)) := by
    have hkm : k + 1 ≤ m := by omega
    exact sdist_chain_le p hp (k + 1) m hkm
  have h_sum_split : ∑ x ∈ Finset.range m, sdist (p x) (p (x + 1)) =
      (∑ x ∈ Finset.Ico 0 k, sdist (p x) (p (x + 1))) + sdist (p k) (p (k + 1)) +
      (∑ x ∈ Finset.Ico (k + 1) m, sdist (p x) (p (x + 1))) := by
    set f := fun (x : ℕ) => sdist (p x) (p (x + 1)) with hf
    calc
      ∑ x ∈ Finset.range m, f x = ∑ x ∈ Finset.Ico 0 m, f x := by
        simp [Nat.Ico_zero_eq_range]
      _ = (∑ x ∈ Finset.Ico 0 (k + 1), f x) + (∑ x ∈ Finset.Ico (k + 1) m, f x) := by
        simpa using (Finset.sum_Ico_consecutive f (by omega : 0 ≤ k + 1) (by omega : k + 1 ≤ m)).symm
      _ = ((∑ x ∈ Finset.Ico 0 k, f x) + f k) + (∑ x ∈ Finset.Ico (k + 1) m, f x) := by
        rw [Finset.sum_Ico_succ_top (by omega : 0 ≤ k) f]
      _ = (∑ x ∈ Finset.Ico 0 k, f x) + f k + (∑ x ∈ Finset.Ico (k + 1) m, f x) := by ring
      _ = (∑ x ∈ Finset.Ico 0 k, sdist (p x) (p (x + 1))) + sdist (p k) (p (k + 1)) +
          (∑ x ∈ Finset.Ico (k + 1) m, sdist (p x) (p (x + 1))) := by simp [hf]
  calc
    sdist (p 0) C + sdist C (p m) ≤ (sdist (p 0) (p k) + sdist (p k) C) + (sdist C (p (k + 1)) + sdist (p (k + 1)) (p m)) := by
      nlinarith
    _ = (sdist (p 0) (p k) + sdist (p k) C + sdist C (p (k + 1))) + sdist (p (k + 1)) (p m) := by ring
    _ ≤ (sdist (p 0) (p k) + sdist (p k) (p (k + 1))) + sdist (p (k + 1)) (p m) := by
      nlinarith
    _ ≤ ((∑ x ∈ Finset.Ico 0 k, sdist (p x) (p (x + 1))) + sdist (p k) (p (k + 1))) +
        sdist (p (k + 1)) (p m) := by
      nlinarith
    _ ≤ ((∑ x ∈ Finset.Ico 0 k, sdist (p x) (p (x + 1))) + sdist (p k) (p (k + 1))) +
        (∑ x ∈ Finset.Ico (k + 1) m, sdist (p x) (p (x + 1))) := by
      nlinarith
    _ = ∑ x ∈ Finset.range m, sdist (p x) (p (x + 1)) := by rw [h_sum_split]

/-- A closed path cut at `j` into two paths of length below `π` lies in the open hemisphere of
pole `p 0 + p j`. -/
theorem hemisphere_of_split (m j : ℕ) (hjm : j ≤ m) (p : ℕ → E3) (hp : ∀ k, ‖p k‖ = 1)
    (hshort : ∀ k < m, sdist (p k) (p (k + 1)) < π) (hclosed : p m = p 0)
    (h₁ : ∑ k ∈ Finset.range j, sdist (p k) (p (k + 1)) < π)
    (h₂ : ∑ k ∈ Finset.Ico j m, sdist (p k) (p (k + 1)) < π) :
    ∀ k ≤ m, 0 < ⟪p k, p 0 + p j⟫ := by
  set A := p 0
  set B := p j
  set M := A + B
  have hA : ‖A‖ = 1 := hp 0
  have hB : ‖B‖ = 1 := hp j
  have hAB_sdist_lt_pi : sdist A B < π := by
    have hchain := sdist_chain_le p hp 0 j (Nat.zero_le j)
    have hIco0j : Finset.Ico 0 j = Finset.range j := by
      ext i; simp [Finset.mem_range]
    rw [hIco0j] at hchain
    linarith
  have hAB_ne_neg : B ≠ -A := by
    intro h_eq
    have h_sdist_pi : sdist A B = π := by
      rw [h_eq]
      rw [sdist_neg_right A A, sdist_self A hA, sub_zero]
    linarith
  have h_inner_gt_neg_one : -1 < ⟪A, B⟫ := by
    by_contra! hle
    have h_norm_sq_nonpos : ‖A + B‖ ^ 2 ≤ 0 := by
      calc
        ‖A + B‖ ^ 2 = ⟪A + B, A + B⟫ := by rw [real_inner_self_eq_norm_sq]
        _ = ⟪A, A + B⟫ + ⟪B, A + B⟫ := by rw [inner_add_left]
        _ = (⟪A, A⟫ + ⟪A, B⟫) + (⟪B, A⟫ + ⟪B, B⟫) := by rw [inner_add_right, inner_add_right]
        _ = ⟪A, A⟫ + ⟪A, B⟫ + ⟪B, A⟫ + ⟪B, B⟫ := by ring
        _ = ‖A‖ ^ 2 + ‖B‖ ^ 2 + (⟪A, B⟫ + ⟪B, A⟫) := by
          simp [add_comm, add_left_comm, add_assoc]
        _ = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * ⟪A, B⟫ := by
          rw [real_inner_comm A B]
          ring
        _ = 1 ^ 2 + 1 ^ 2 + 2 * ⟪A, B⟫ := by rw [hA, hB]
        _ = 2 + 2 * ⟪A, B⟫ := by norm_num
        _ ≤ 2 + 2 * (-1) := by nlinarith
        _ = 0 := by ring
    have h_norm_zero : ‖A + B‖ = 0 := by
      have h_sq_eq_zero : ‖A + B‖ ^ 2 = 0 := by
        have h_nonneg : 0 ≤ ‖A + B‖ ^ 2 := by positivity
        nlinarith
      have h_nonneg_norm : 0 ≤ ‖A + B‖ := by positivity
      nlinarith
    have h_sum_zero : A + B = 0 := norm_eq_zero.mp h_norm_zero
    have hB_eq_neg_A : B = -A := by
      calc
        B = (A + B) - A := by abel
        _ = 0 - A := by rw [h_sum_zero]
        _ = -A := by simp
    exact hAB_ne_neg hB_eq_neg_A
  have hA_M_pos : 0 < ⟪A, M⟫ := by
    dsimp [M]
    rw [inner_add_right, real_inner_self_eq_norm_sq, hA]
    nlinarith
  have hB_M_pos : 0 < ⟪B, M⟫ := by
    dsimp [M]
    rw [inner_add_right, real_inner_self_eq_norm_sq, hB]
    have htemp : ⟪B, A⟫ = ⟪A, B⟫ := by rw [real_inner_comm B A]
    rw [htemp]
    have : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [this]
    nlinarith
  intro k hk
  by_contra! hle
  by_cases hkj : k ≤ j
  · have hshort_j : ∀ k' < j, sdist (p k') (p (k' + 1)) < π := by
      intro k' hk'
      apply hshort k'
      omega
    have h_path := path_cross M j p hp hshort_j hA_M_pos k hkj hle
    rcases h_path with ⟨C, hC_norm, hC_M, hC_sum⟩
    have h_sum_eq_pi : sdist A C + sdist C B = π := by
      apply sdist_add_eq_pi A B C
      dsimp [M] at hC_M
      exact hC_M
    linarith
  · have hjk : j ≤ k := by omega
    have hp' : ∀ k', ‖p (j + k')‖ = 1 := by
      intro k'; rw [hp]
    have hshort' : ∀ k' < m - j, sdist (p (j + k')) (p (j + k' + 1)) < π := by
      intro k' hk'
      apply hshort (j + k')
      omega
    have hk_sub : k - j ≤ m - j := by omega
    have hk_sub_eq : j + (k - j) = k := by omega
    have hm_sub_eq : j + (m - j) = m := by omega
    have h_path := path_cross M (m - j) (λ i => p (j + i)) hp' hshort' hB_M_pos (k - j) hk_sub
      (by
        rw [hk_sub_eq]
        exact hle)
    rcases h_path with ⟨C, hC_norm, hC_M, hC_sum⟩
    rw [add_zero j, hm_sub_eq] at hC_sum
    -- hC_sum : sdist (p j) C + sdist C (p m) ≤ ∑ k ∈ range (m - j), sdist (p (j + k)) (p (j + (k + 1)))
    rw [show p j = B from rfl, hclosed] at hC_sum
    -- hC_sum : sdist B C + sdist C A ≤ ∑ k ∈ range (m - j), sdist (p (j + k)) (p (j + (k + 1)))
    have hsum_eq : ∑ k ∈ Finset.range (m - j), sdist (p (j + k)) (p (j + (k + 1))) =
                  ∑ k ∈ Finset.Ico j m, sdist (p k) (p (k + 1)) := by
      have := Finset.sum_Ico_eq_sum_range (λ x => sdist (p x) (p (x + 1))) j m
      -- this : ∑ k ∈ Ico j m, sdist (p k) (p (k + 1)) = ∑ k ∈ range (m - j), sdist (p (j + k)) (p ((j + k) + 1))
      -- We need to relate sdist (p (j + (k + 1))) to sdist (p ((j + k) + 1))
      calc
        ∑ k ∈ Finset.range (m - j), sdist (p (j + k)) (p (j + (k + 1))) =
            ∑ k ∈ Finset.range (m - j), sdist (p (j + k)) (p ((j + k) + 1)) := by
          refine Finset.sum_congr rfl (λ k hk => ?_)
          rw [add_assoc]
        _ = ∑ k ∈ Finset.Ico j m, sdist (p k) (p (k + 1)) := by rw [← this]
    rw [hsum_eq] at hC_sum
    have h_sum_eq_pi : sdist B C + sdist C A = π := by
      apply sdist_add_eq_pi B A C
      rw [add_comm B A]
      dsimp [M] at hC_M
      exact hC_M
    linarith

/-- The index where the partial sums of nonnegative terms pass a level `c`. -/
theorem exists_split_index (L : ℕ) (l : ℕ → ℝ) (_hl : ∀ k, 0 ≤ l k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < ∑ k ∈ Finset.range (L + 1), l k) :
    ∃ j ≤ L, ∑ k ∈ Finset.range j, l k ≤ c ∧ c < ∑ k ∈ Finset.range (j + 1), l k := by
  have h_exists : ∃ j, c < ∑ k ∈ Finset.range (j + 1), l k := by
    refine ⟨L, ?_⟩
    simpa using hc
  let j := Nat.find h_exists
  have hj_spec : c < ∑ k ∈ Finset.range (j + 1), l k := Nat.find_spec h_exists
  have hj_le_L : j ≤ L := Nat.find_min' h_exists hc
  have h_sum_le : ∑ k ∈ Finset.range j, l k ≤ c := by
    by_cases hz : j = 0
    · rw [hz]
      simp [hc0]
    · rcases Nat.exists_eq_succ_of_ne_zero hz with ⟨i, hi⟩
      rw [hi]
      have hi_lt_j : i < j := by
        rw [hi]
        exact Nat.lt_succ_self i
      have h_not : ¬ (c < ∑ k ∈ Finset.range (i + 1), l k) :=
        Nat.find_min h_exists hi_lt_j
      have hle : ∑ k ∈ Finset.range (i + 1), l k ≤ c := by linarith
      simpa using hle
  exact ⟨j, hj_le_L, h_sum_le, hj_spec⟩

theorem polygon_hemisphere (L : ℕ) (n : Fin (L + 1) → E3) (hn : ∀ i, ‖n i‖ = 1)
    (hshort : ∀ i, sdist (n i) (n (i + 1)) < π)
    (hsum : ∑ i, sdist (n i) (n (i + 1)) < 2 * π) :
    ∃ z : E3, ∀ i, 0 < ⟪z, n i⟫ := by
  set p : ℕ → E3 := fun k => n (k : Fin (L + 1)) with hp_def
  have hp : ∀ k, ‖p k‖ = 1 := fun k => hn _
  have hpn : ∀ i : Fin (L + 1), p i.val = n i := fun i => by
    simp only [hp_def, Fin.cast_val_eq_self]
  have hstep : ∀ k, sdist (p k) (p (k + 1)) = sdist (n k) (n ((k : Fin (L + 1)) + 1)) := by
    intro k
    simp only [hp_def, Nat.cast_succ]
  have hshort_p : ∀ k, sdist (p k) (p (k + 1)) < π := fun k => by
    rw [hstep]
    exact hshort _
  have hclosed : p (L + 1) = p 0 := by
    simp only [hp_def, Nat.cast_zero]
    congr 1
    exact Fin.ext (by simp)
  set l : ℕ → ℝ := fun k => sdist (p k) (p (k + 1)) with hl_def
  have hl0 : ∀ k, 0 ≤ l k := fun k => Real.arccos_nonneg _
  have hS : ∑ k ∈ Finset.range (L + 1), l k = ∑ i, sdist (n i) (n (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hl_def, hstep, Fin.cast_val_eq_self]
  set S := ∑ k ∈ Finset.range (L + 1), l k with hS_def
  have hS2 : S < 2 * π := by
    rw [hS]
    exact hsum
  have hπ := Real.pi_pos
  by_cases hSπ : S < π
  · -- the whole polygon is shorter than `π`: cut it at its first vertex
    have h := hemisphere_of_split (L + 1) 0 (Nat.zero_le _) p hp (fun k _ => hshort_p k) hclosed
      (by rw [Finset.sum_range_zero]; exact hπ) (by rw [← Finset.range_eq_Ico]; exact hSπ)
    refine ⟨p 0 + p 0, fun i => ?_⟩
    have hi := i.isLt
    rw [real_inner_comm, ← hpn i]
    exact h i.val (by omega)
  · -- cut the polygon at half its length, inserting the point `B` of the edge `j` there
    rw [not_lt] at hSπ
    obtain ⟨j, hjL, hA, hA1⟩ := exists_split_index L l hl0 (S / 2) (by linarith)
      (by rw [← hS_def]; linarith)
    rw [Finset.sum_range_succ] at hA1
    set A := ∑ k ∈ Finset.range j, l k with hA_def
    have hlj : l j < π := hshort_p j
    obtain ⟨B, hB, hB1, hB2⟩ := exists_arc_point (p j) (p (j + 1)) (hp j) (hp (j + 1))
      (hshort_p j) (S / 2 - A) (by linarith) (by show S / 2 - A ≤ l j; linarith)
    set q : ℕ → E3 := fun k => if k ≤ j then p k else if k = j + 1 then B else p (k - 1)
      with hq_def
    have hq_le : ∀ k, k ≤ j → q k = p k := fun k hk => by simp [hq_def, hk]
    have hq_mid : q (j + 1) = B := by simp [hq_def]
    have hq_gt : ∀ k, j + 2 ≤ k → q k = p (k - 1) := fun k hk => by
      simp [hq_def, show ¬ k ≤ j by omega, show k ≠ j + 1 by omega]
    have hq : ∀ k, ‖q k‖ = 1 := by
      intro k
      simp only [hq_def]
      split_ifs
      · exact hp k
      · exact hB
      · exact hp _
    have hqs_lt : ∀ k, k < j → sdist (q k) (q (k + 1)) = l k := fun k hk => by
      rw [hq_le k hk.le, hq_le (k + 1) hk]
    have hqs_j : sdist (q j) (q (j + 1)) = S / 2 - A := by
      rw [hq_le j le_rfl, hq_mid, hB1]
    have hqs_j1 : sdist (q (j + 1)) (q (j + 1 + 1)) = l j - (S / 2 - A) := by
      rw [hq_mid, hq_gt (j + 1 + 1) (by omega), show j + 1 + 1 - 1 = j + 1 by omega, hB2]
    have hqs_gt : ∀ k, j + 1 ≤ k → sdist (q (k + 1)) (q (k + 1 + 1)) = l k := fun k hk => by
      rw [hq_gt (k + 1) (by omega), hq_gt (k + 1 + 1) (by omega),
        show k + 1 - 1 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega]
    have hshort_q : ∀ k < L + 1 + 1, sdist (q k) (q (k + 1)) < π := by
      intro k hk
      rcases lt_trichotomy k j with h | h | h
      · rw [hqs_lt k h]
        exact hshort_p k
      · rw [h, hqs_j]
        linarith
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        by_cases hk' : k' = j
        · rw [hk', hqs_j1]
          linarith
        · rw [hqs_gt k' (by omega)]
          exact hshort_p k'
    have hclosed_q : q (L + 1 + 1) = q 0 := by
      rw [hq_gt (L + 1 + 1) (by omega), hq_le 0 (Nat.zero_le _),
        show L + 1 + 1 - 1 = L + 1 by omega, hclosed]
    have hsum1 : ∑ k ∈ Finset.range j, sdist (q k) (q (k + 1)) = A :=
      Finset.sum_congr rfl (fun k hk => hqs_lt k (Finset.mem_range.mp hk))
    have h₁ : ∑ k ∈ Finset.range (j + 1), sdist (q k) (q (k + 1)) < π := by
      rw [Finset.sum_range_succ, hsum1, hqs_j]
      linarith
    have hshift : ∑ k ∈ Finset.Ico (j + 1 + 1) (L + 1 + 1), sdist (q k) (q (k + 1)) =
        ∑ k ∈ Finset.Ico (j + 1) (L + 1), l k := by
      rw [← Finset.sum_Ico_add' (fun k => sdist (q k) (q (k + 1))) (j + 1) (L + 1) 1]
      exact Finset.sum_congr rfl (fun k hk => hqs_gt k (Finset.mem_Ico.mp hk).1)
    have hsplit := Finset.sum_range_add_sum_Ico l (show j + 1 ≤ L + 1 by omega)
    rw [Finset.sum_range_succ l j, ← hA_def, ← hS_def] at hsplit
    have h₂ : ∑ k ∈ Finset.Ico (j + 1) (L + 1 + 1), sdist (q k) (q (k + 1)) < π := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (show j + 1 < L + 1 + 1 by omega), hqs_j1, hshift]
      linarith
    have h := hemisphere_of_split (L + 1 + 1) (j + 1) (by omega) q hq hshort_q hclosed_q h₁ h₂
    refine ⟨q 0 + q (j + 1), fun i => ?_⟩
    have hi := i.isLt
    rw [real_inner_comm, ← hpn i]
    by_cases hij : i.val ≤ j
    · rw [← hq_le i.val hij]
      exact h i.val (by omega)
    · have h' := hq_gt (i.val + 1) (by omega)
      rw [show i.val + 1 - 1 = i.val by omega] at h'
      rw [← h']
      exact h (i.val + 1) (by omega)

set_option maxHeartbeats 800000 in
theorem walk_axis (L : ℕ) (w : Fin (L + 1) → E3) (hw : ∀ i, ‖w i‖ = 1)
    (hturn : ∀ i, 0 < ⟪cross (w i) (w (i + 1)), w (i - 1)⟫)
    (hsum : ∑ i, (π - ocorner (w i) (w (i + 1)) (w (i - 1))) < 2 * π) :
    ∃ z : E3, ∀ i, 0 < ⟪cross z (w i), w (i + 1)⟫ := by
  -- Define the poles m i = normalized cross product of consecutive w's
  set m := λ i => ‖cross (w i) (w (i + 1))‖⁻¹ • cross (w i) (w (i + 1)) with hm
  have hm_norm : ∀ i, ‖m i‖ = 1 := by
    intro i
    dsimp [m]
    have hcross_ne_zero : cross (w i) (w (i + 1)) ≠ 0 := by
      intro hzero
      have hzero_inner : ⟪cross (w i) (w (i + 1)), w (i - 1)⟫ = 0 := by simp [hzero]
      have hpos := hturn i
      linarith
    have hpos_norm : 0 < ‖cross (w i) (w (i + 1))‖ := norm_pos_iff.mpr hcross_ne_zero
    calc
      ‖‖cross (w i) (w (i + 1))‖⁻¹ • cross (w i) (w (i + 1))‖
          = ‖‖cross (w i) (w (i + 1))‖⁻¹‖ * ‖cross (w i) (w (i + 1))‖ := by exact norm_smul _ _
      _ = |‖cross (w i) (w (i + 1))‖⁻¹| * ‖cross (w i) (w (i + 1))‖ := by rw [Real.norm_eq_abs]
      _ = (‖cross (w i) (w (i + 1))‖⁻¹) * ‖cross (w i) (w (i + 1))‖ := by
        rw [abs_of_pos (inv_pos_of_pos hpos_norm)]
      _ = 1 := by field_simp [ne_of_gt hpos_norm]
  have h_sdist_eq : ∀ i, sdist (m (i - 1)) (m i) = π - ocorner (w i) (w (i + 1)) (w (i - 1)) := by
    intro i
    have h := pole_sdist (w (i - 1)) (w i) (w (i + 1)) (hw i) (hturn i)
    simpa [m, sub_add_cancel] using h
  -- Helper lemma for Fin arithmetic
  have h_one_add_one_eq_two : (1 : Fin (L + 1)) + 1 = 2 := by
    simpa using (one_add_one_eq_two (R := Fin (L + 1)))
  have h_fin_add : ∀ (x : Fin (L + 1)), (x + 1) + 1 = x + 2 := by
    intro x
    calc
      (x + 1) + 1 = x + (1 + 1) := by rw [add_assoc]
      _ = x + 2 := by rw [h_one_add_one_eq_two]
  have h_fin_sub : ∀ (x : Fin (L + 1)), (x + 1) - 1 = x := by
    intro x; abel
  have hshort : ∀ i, sdist (m i) (m (i + 1)) < π := by
    intro i
    have h_eq : sdist (m i) (m (i + 1)) = π - ocorner (w (i + 1)) (w (i + 1 + 1)) (w i) := by
      have h := h_sdist_eq (i + 1)
      rw [h_fin_sub i] at h
      exact h
    rw [h_eq]
    have h := hturn (i + 1)
    rw [h_fin_sub i] at h
    have h_ocorner_pos_lt_pi := (ocorner_pos_lt_pi_iff (w (i + 1)) (w (i + 1 + 1)) (w i)).mpr h
    linarith
  have hsum' : ∑ i, sdist (m i) (m (i + 1)) < 2 * π := by
    calc
      ∑ i, sdist (m i) (m (i + 1)) = ∑ i, sdist (m (i - 1)) (m i) := by
        -- Reindex: i ↦ i-1 (using inverse of finRotate which adds 1)
        have h := (Equiv.sum_comp ((finRotate (L + 1)).symm)
          (λ j => sdist (m j) (m (j + 1)))).symm
        -- h: ∑ x, sdist (m x) (m (x+1)) = ∑ x, sdist (m (x-1)) (m ((x-1)+1))
        -- But ((x-1)+1) = x by sub_add_cancel
        simpa [sub_add_cancel] using h
      _ = ∑ i, (π - ocorner (w i) (w (i + 1)) (w (i - 1))) := by simp [h_sdist_eq]
      _ < 2 * π := hsum
  obtain ⟨z, hz⟩ := polygon_hemisphere L m hm_norm hshort hsum'
  refine ⟨z, λ i => ?_⟩
  have hz_i : 0 < ⟪z, m i⟫ := hz i
  dsimp [m] at hz_i
  have hcross_ne_zero : cross (w i) (w (i + 1)) ≠ 0 := by
    intro hzero
    have hzero_inner : ⟪cross (w i) (w (i + 1)), w (i - 1)⟫ = 0 := by simp [hzero]
    have hpos := hturn i
    linarith
  have hpos_norm : 0 < ‖cross (w i) (w (i + 1))‖ := norm_pos_iff.mpr hcross_ne_zero
  have h_inner_pos : 0 < ⟪z, cross (w i) (w (i + 1))⟫ := by
    have hcalc : 0 < (‖cross (w i) (w (i + 1))‖⁻¹) * ⟪z, cross (w i) (w (i + 1))⟫ := by
      calc
        0 < ⟪z, ‖cross (w i) (w (i + 1))‖⁻¹ • cross (w i) (w (i + 1))⟫ := hz_i
        _ = ⟪z, (‖cross (w i) (w (i + 1))‖⁻¹) • cross (w i) (w (i + 1))⟫ := rfl
        _ = (‖cross (w i) (w (i + 1))‖⁻¹) * ⟪z, cross (w i) (w (i + 1))⟫ := by rw [inner_smul_right]
    have h_inv_pos : 0 < ‖cross (w i) (w (i + 1))‖⁻¹ := inv_pos_of_pos hpos_norm
    exact (mul_pos_iff_of_pos_left h_inv_pos).mp hcalc
  rw [← real_inner_comm (cross z (w i)) (w (i + 1)), inner_cross_perm (w (i + 1)) z (w i)]
  exact h_inner_pos

/-! ## Winding numbers about an axis -/

theorem exists_generic (U : Set E3) (hU : IsOpen U) (hne : U.Nonempty) (S : Finset E3)
    (hS : ∀ m ∈ S, m ≠ 0) : ∃ z ∈ U, ∀ m ∈ S, ⟪z, m⟫ ≠ 0 := by
  -- For each nonzero m, the set {z | ⟪z, m⟫ ≠ 0} is open and dense
  have h_open : ∀ m : E3, IsOpen {z : E3 | ⟪z, m⟫ ≠ 0} := by
    intro m
    have h_cont : Continuous (fun z : E3 => ⟪z, m⟫) :=
      continuous_id.inner continuous_const
    have h_closed : IsClosed {z : E3 | ⟪z, m⟫ = 0} :=
      isClosed_eq h_cont continuous_const
    have : {z : E3 | ⟪z, m⟫ ≠ 0} = {z : E3 | ⟪z, m⟫ = 0}ᶜ := by
      ext z; simp
    rw [this]
    exact h_closed.isOpen_compl
  have h_dense : ∀ m : E3, m ≠ 0 → Dense {z : E3 | ⟪z, m⟫ ≠ 0} := by
    intro m hm
    -- Show that the complement {z | ⟪z, m⟫ = 0} has empty interior
    apply (interior_eq_empty_iff_dense_compl (s := {z : E3 | ⟪z, m⟫ = 0})).mp
    by_contra! h_ne
    -- h_ne : (interior {z | ⟪z, m⟫ = 0}).Nonempty
    obtain ⟨z₀, hz₀⟩ := h_ne
    -- z₀ is in the interior, so there's an open ball around z₀ contained in {z | ⟪z, m⟫ = 0}
    have h_int_open : IsOpen (interior {z : E3 | ⟪z, m⟫ = 0}) := isOpen_interior
    rcases Metric.isOpen_iff.mp h_int_open z₀ hz₀ with ⟨ε, hε, hball⟩
    -- hball : Metric.ball z₀ ε ⊆ interior {z | ⟪z, m⟫ = 0}
    have hm_norm_pos : 0 < ‖m‖ := norm_pos_iff.mpr hm
    -- Take z = z₀ + (ε/2) • (m / ‖m‖), which is in the ball
    set z := z₀ + ((ε / 2) / ‖m‖) • m with hz_def
    have hz_ball : z ∈ Metric.ball z₀ ε := by
      rw [Metric.mem_ball, dist_eq_norm, hz_def]
      have hsub : z₀ + ((ε / 2) / ‖m‖) • m - z₀ = ((ε / 2) / ‖m‖) • m := by abel
      rw [hsub]
      -- ‖((ε/2)/‖m‖) • m‖ = |(ε/2)/‖m‖| * ‖m‖ = ((ε/2)/‖m‖) * ‖m‖ = ε/2 < ε
      have hpos_coeff : 0 ≤ (ε / 2) / ‖m‖ := div_nonneg (by linarith) (by linarith)
      calc
        ‖((ε / 2) / ‖m‖) • m‖ = ‖((ε / 2) / ‖m‖)‖ * ‖m‖ := norm_smul _ _
        _ = |(ε / 2) / ‖m‖| * ‖m‖ := by rw [Real.norm_eq_abs]
        _ = ((ε / 2) / ‖m‖) * ‖m‖ := by rw [abs_of_nonneg hpos_coeff]
        _ = ε / 2 := by field_simp [hm_norm_pos.ne']
        _ < ε := by linarith
    have hz_mem_interior : z ∈ interior {z : E3 | ⟪z, m⟫ = 0} := hball hz_ball
    have hz_mem_H : z ∈ {z : E3 | ⟪z, m⟫ = 0} := interior_subset hz_mem_interior
    -- But we can compute ⟪z, m⟫ directly and see it's nonzero
    have hz_inner : ⟪z, m⟫ ≠ 0 := by
      rw [hz_def, inner_add_left, inner_smul_left]
      simp
      have hz₀_inner : ⟪z₀, m⟫ = 0 := by
        have hz₀_mem_H : z₀ ∈ {z : E3 | ⟪z, m⟫ = 0} := interior_subset hz₀
        simpa using hz₀_mem_H
      rw [hz₀_inner, zero_add]
      -- Now we have ((ε/2)/‖m‖) * ‖m‖² ≠ 0
      positivity
    exact hz_inner hz_mem_H
  -- Now the finite intersection of open dense sets is dense
  have h_dense_inter : Dense (⋂ m ∈ (S : Set E3), {z : E3 | ⟪z, m⟫ ≠ 0}) := by
    refine dense_biInter_of_isOpen ?_ ?_ ?_
    · intro m hmS
      exact h_open m
    · -- S is finite, hence countable
      exact Finset.countable_toSet S
    · intro m hmS
      exact h_dense m (hS m hmS)
  -- Since U is nonempty open, it intersects the dense set
  rcases hne with ⟨z₀, hz₀⟩
  have h_inter : (U ∩ (⋂ m ∈ (S : Set E3), {z : E3 | ⟪z, m⟫ ≠ 0})).Nonempty :=
    h_dense_inter.inter_open_nonempty U hU ⟨z₀, hz₀⟩
  rcases h_inter with ⟨z, hzU, hzS⟩
  have hzS' : ∀ (m : E3), m ∈ (S : Set E3) → z ∈ {z : E3 | ⟪z, m⟫ ≠ 0} := by
    simpa [Set.mem_iInter₂] using hzS
  refine ⟨z, hzU, ?_⟩
  intro m hm
  have hm' : m ∈ (S : Set E3) := Finset.mem_coe.mpr hm
  have hz_mem := hzS' m hm'
  simpa using hz_mem

/-- The sign of `oarg` is the sign of the determinant. -/
theorem oarg_mem_of_det (z p q : E3) :
    (0 < ⟪cross z p, q⟫ → 0 < oarg z p q ∧ oarg z p q < π) ∧
      (⟪cross z p, q⟫ < 0 → -π < oarg z p q ∧ oarg z p q < 0) := by
  have h_inner_cross : ⟪z, cross (tdir z p) (tdir z q)⟫ = ⟪cross z p, q⟫ :=
    inner_cross_tdir z p q
  constructor
  · intro hpos
    have him_pos : 0 < ⟪z, cross (tdir z p) (tdir z q)⟫ := by rwa [h_inner_cross]
    have harg_pos : 0 < oarg z p q := by
      dsimp [oarg]
      have h_nonneg : 0 ≤ Complex.arg ⟨⟪tdir z p, tdir z q⟫,
          ⟪z, cross (tdir z p) (tdir z q)⟫⟩ := by
        rw [Complex.arg_nonneg_iff]
        exact le_of_lt him_pos
      have h_ne_zero : Complex.arg ⟨⟪tdir z p, tdir z q⟫,
          ⟪z, cross (tdir z p) (tdir z q)⟫⟩ ≠ 0 := by
        intro h_eq
        have him_zero := (Complex.arg_eq_zero_iff.mp h_eq).2
        linarith
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    have harg_lt_pi : oarg z p q < π := by
      dsimp [oarg]
      rw [Complex.arg_lt_pi_iff]
      right
      intro hzero
      linarith
    exact And.intro harg_pos harg_lt_pi
  · intro hneg
    have him_neg : ⟪z, cross (tdir z p) (tdir z q)⟫ < 0 := by rwa [h_inner_cross]
    have harg_neg : oarg z p q < 0 := by
      dsimp [oarg]
      rw [Complex.arg_neg_iff]
      exact him_neg
    have h_neg_pi_lt : -π < oarg z p q := by
      dsimp [oarg]
      exact Complex.neg_pi_lt_arg _
    exact And.intro h_neg_pi_lt harg_neg

theorem oarg_eq_arg (z e p q : E3) (hz : ‖z‖ = 1) (he : ‖e‖ = 1) (hze : ⟪z, e⟫ = 0) :
    oarg z p q = Complex.arg (conj (tcoord z e p) * tcoord z e q) := by
  dsimp [oarg]
  apply congr_arg Complex.arg
  apply Complex.ext
  · rw [inner_tdir_frame z e p q hz he hze]
    simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  · rw [det_tdir_frame z e p q hz he hze]
    simp [tcoord, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- The arguments of the quotients along a closed sequence of nonzero complex numbers sum to a
multiple of `2π`. -/
theorem sum_arg_closed (m : ℕ) (t : ℕ → ℂ) (ht : ∀ k, t k ≠ 0) (hclosed : t m = t 0) :
    ∃ k : ℤ, ∑ i ∈ Finset.range m, Complex.arg (conj (t i) * t (i + 1)) = 2 * π * k := by
  -- Define w i = conj (t i) * t (i + 1)
  let w : ℕ → ℂ := fun i => conj (t i) * t (i + 1)
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    apply mul_ne_zero
    · exact (star_ne_zero.mpr (ht i))
    · exact ht (i + 1)
  -- Key identity: exp (arg x * I) = x / ‖x‖ for x ≠ 0
  have h_exp_arg (x : ℂ) (hx : x ≠ 0) : Complex.exp ((x.arg : ℂ) * Complex.I) = x / (‖x‖ : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I x
    -- h: ↑‖x‖ * Complex.exp (↑x.arg * Complex.I) = x
    have hnorm : (‖x‖ : ℂ) ≠ 0 := by
      exact mod_cast (norm_ne_zero_iff.mpr hx)
    apply (eq_div_iff_mul_eq hnorm).mpr
    rw [mul_comm]
    exact h
  -- Lemma: a positive real complex number with norm 1 equals 1
  have pos_real_norm_one_eq_one {z : ℂ} (hz_re : 0 ≤ z.re) (hz_im : z.im = 0) (hz_norm : ‖z‖ = 1) : z = 1 := by
    have h_normSq : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz_norm]
      norm_num
    have h_re_sq : z.re * z.re = 1 := by
      rw [Complex.normSq_apply] at h_normSq
      rw [hz_im] at h_normSq
      nlinarith
    have h_re : z.re = 1 := by
      have h_eq : (z.re - 1) * (z.re + 1) = 0 := by
        nlinarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_eq with h | h
      · linarith
      · -- z.re + 1 = 0 → z.re = -1, contradicts hz_re
        linarith
    apply Complex.ext <;> simp [h_re, hz_im]
  -- Handle m = 0 case separately
  by_cases hm : m = 0
  · subst hm
    refine ⟨0, ?_⟩
    simp
  · -- Main proof for m > 0
    have h_prod_shift : (∏ i ∈ Finset.range m, t (i + 1)) = (∏ i ∈ Finset.range m, t i) := by
      have h1 := Finset.prod_range_succ t m
      have h2 := Finset.prod_range_succ' t m
      rw [hclosed] at h1
      -- h1: ∏ i ∈ range (m+1), t i = (∏ i ∈ range m, t i) * t 0
      -- h2: ∏ i ∈ range (m+1), t i = (∏ i ∈ range m, t (i+1)) * t 0
      have h_eq : (∏ i ∈ Finset.range m, t i) * t 0 = (∏ i ∈ Finset.range m, t (i + 1)) * t 0 := by
        rw [← h1, h2]
      have ht0 : t 0 ≠ 0 := ht 0
      exact (mul_right_cancel₀ ht0 h_eq).symm
    have h_prod_w : (∏ i ∈ Finset.range m, w i) = ∏ i ∈ Finset.range m, (‖t i‖ ^ 2 : ℂ) := by
      calc
        (∏ i ∈ Finset.range m, w i) = (∏ i ∈ Finset.range m, (conj (t i) * t (i + 1))) := rfl
        _ = (∏ i ∈ Finset.range m, conj (t i)) * (∏ i ∈ Finset.range m, t (i + 1)) := by
          rw [Finset.prod_mul_distrib]
        _ = ((starRingEnd ℂ) (∏ i ∈ Finset.range m, t i)) * (∏ i ∈ Finset.range m, t (i + 1)) := by
          simp
        _ = ((starRingEnd ℂ) (∏ i ∈ Finset.range m, t i)) * (∏ i ∈ Finset.range m, t i) := by
          rw [h_prod_shift]
        _ = ((∏ i ∈ Finset.range m, (starRingEnd ℂ) (t i))) * (∏ i ∈ Finset.range m, t i) := by
          simp
        _ = ∏ i ∈ Finset.range m, ((starRingEnd ℂ) (t i) * t i) := by
          rw [Finset.prod_mul_distrib]
        _ = ∏ i ∈ Finset.range m, (conj (t i) * t i) := by
          simp
        _ = ∏ i ∈ Finset.range m, (‖t i‖ ^ 2 : ℂ) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Complex.conj_mul']
    -- Now compute the exponential of the sum of arguments
    have h_exp_sum : Complex.exp (((∑ i ∈ Finset.range m, (w i).arg : ℝ) : ℂ) * Complex.I) =
        (∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ)) := by
      calc
        Complex.exp (((∑ i ∈ Finset.range m, (w i).arg : ℝ) : ℂ) * Complex.I) =
            Complex.exp ((∑ i ∈ Finset.range m, ((w i).arg : ℂ)) * Complex.I) := by
          simp [Complex.ofReal_sum]
        _ = Complex.exp (∑ i ∈ Finset.range m, (((w i).arg : ℂ) * Complex.I)) := by
          rw [Finset.sum_mul]
        _ = ∏ i ∈ Finset.range m, Complex.exp (((w i).arg : ℂ) * Complex.I) := by
          rw [Complex.exp_sum]
        _ = ∏ i ∈ Finset.range m, (w i / (‖w i‖ : ℂ)) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [h_exp_arg (w i) (hw i)]
        _ = (∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ)) := by
          rw [Finset.prod_div_distrib]
    -- Show that the quotient is a positive real with norm 1, hence equals 1.
    have hz_norm : ‖(∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ))‖ = 1 := by
      rw [norm_div, Complex.norm_prod, Complex.norm_prod]
      simp_rw [Complex.norm_of_nonneg (norm_nonneg _)]
      have h_prod_ne_zero : (∏ i ∈ Finset.range m, ‖w i‖) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => norm_ne_zero_iff.mpr (hw i)
      exact div_self h_prod_ne_zero
    have hz_real : ((∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ))).im = 0 := by
      rw [h_prod_w]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_prod, ← Complex.ofReal_div, Complex.ofReal_im]
    have hz_pos : 0 ≤ ((∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ))).re := by
      rw [h_prod_w]
      have h_expr : ((∏ i ∈ Finset.range m, (‖t i‖ ^ 2 : ℂ)) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ))).re =
          (∏ i ∈ Finset.range m, ‖t i‖ ^ 2) / (∏ i ∈ Finset.range m, ‖w i‖) := by
        simp [← Complex.ofReal_pow, ← Complex.ofReal_prod, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [h_expr]
      apply div_nonneg
      · apply Finset.prod_nonneg
        intro i _
        positivity
      · apply Finset.prod_nonneg
        intro i _
        exact norm_nonneg _
    have hz_eq_one : (∏ i ∈ Finset.range m, w i) / (∏ i ∈ Finset.range m, (‖w i‖ : ℂ)) = 1 :=
      pos_real_norm_one_eq_one hz_pos hz_real hz_norm
    -- Now we have Complex.exp ((∑ arg : ℂ) * I) = 1
    have h_exp_one : Complex.exp (((∑ i ∈ Finset.range m, (w i).arg : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [h_exp_sum, hz_eq_one]
    -- By Complex.exp_eq_one_iff, there exists n : ℤ such that (∑ arg : ℂ) * I = n * (2 * π * I)
    rcases (Complex.exp_eq_one_iff).mp h_exp_one with ⟨n, hn⟩
    -- hn: ((∑ arg : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * π * Complex.I)
    -- Cancel I (since I ≠ 0)
    have hI_ne_zero : Complex.I ≠ 0 := Complex.I_ne_zero
    have h_sum_eq : ((∑ i ∈ Finset.range m, (w i).arg : ℝ) : ℂ) = (n : ℂ) * (2 * π : ℂ) := by
      apply mul_right_cancel₀ hI_ne_zero
      -- Actually, hn gives: (∑ arg : ℂ) * I = (n : ℂ) * (2 * π * I)
      -- We need to rearrange
      calc
        ((∑ i ∈ Finset.range m, (w i).arg : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * π * Complex.I) := hn
        _ = ((n : ℂ) * (2 * π : ℂ)) * Complex.I := by ring
    -- Now take the real part (or use Complex.ofReal_inj)
    -- Since both sides are real, we can apply Complex.ofReal_inj
    have h_sum_real : (∑ i ∈ Finset.range m, (w i).arg : ℝ) = (n : ℝ) * (2 * π) := by
      apply Complex.ofReal_inj.mp
      simpa [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_comm] using h_sum_eq
    refine ⟨n, ?_⟩
    simpa [w, mul_comm] using h_sum_real

theorem sum_oarg_closed (z : E3) (hz : ‖z‖ = 1) (m : ℕ) (u : ℕ → E3)
    (hu : ∀ k, tdir z (u k) ≠ 0) (hclosed : u m = u 0) :
    ∃ k : ℤ, ∑ i ∈ Finset.range m, oarg z (u i) (u (i + 1)) = 2 * π * k := by
  rcases exists_unit_orthogonal z with ⟨e, he_norm, he_orth⟩
  have hze : ⟪z, e⟫ = 0 := he_orth
  have h_nonzero : ∀ k, tcoord z e (u k) ≠ 0 := by
    intro k
    have h_norm_ne_zero : ‖tcoord z e (u k)‖ ≠ 0 := by
      rw [← norm_tdir_eq_norm_tcoord z e (u k) hz he_norm hze]
      exact norm_ne_zero_iff.mpr (hu k)
    exact norm_ne_zero_iff.mp h_norm_ne_zero
  have h_closed_t : tcoord z e (u m) = tcoord z e (u 0) := by
    rw [hclosed]
  have h_sum := sum_arg_closed m (fun k => tcoord z e (u k)) h_nonzero h_closed_t
  rcases h_sum with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    ∑ i ∈ Finset.range m, oarg z (u i) (u (i + 1))
        = ∑ i ∈ Finset.range m, Complex.arg (conj (tcoord z e (u i)) * tcoord z e (u (i + 1))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [oarg_eq_arg z e (u i) (u (i + 1)) hz he_norm hze]
    _ = 2 * π * k := hk

theorem sum_oarg_mem (z : E3) (hz : ‖z‖ = 1) (L : ℕ) (w : Fin (L + 1) → E3)
    (hw : ∀ i, tdir z (w i) ≠ 0) :
    ∃ k : ℤ, ∑ i, oarg z (w i) (w (i + 1)) = 2 * π * k := by
  set u : ℕ → E3 := fun k => w (Fin.ofNat (L + 1) k) with hu_def
  have hu : ∀ k, tdir z (u k) ≠ 0 := by
    intro k
    dsimp [u]
    exact hw (Fin.ofNat (L + 1) k)
  have hclosed : u (L + 1) = u 0 := by
    dsimp [u]
    simp
  obtain ⟨k, hk⟩ := sum_oarg_closed z hz (L + 1) u hu hclosed
  refine ⟨k, ?_⟩
  calc
    (∑ i : Fin (L + 1), oarg z (w i) (w (i + 1)))
        = (∑ i : Fin (L + 1), oarg z (u i.val) (u (i.val + 1))) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have h1 : w i = u i.val := by
        dsimp [u]
        congr
        ext; simp
      have h2 : w (i + 1) = u (i.val + 1) := by
        dsimp [u]
        congr
        ext; simp [Fin.val_add]
      simp [h1, h2]
    _ = (∑ i ∈ Finset.range (L + 1), oarg z (u i) (u (i + 1))) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => oarg z (u k) (u (k + 1))) (L + 1)]
    _ = 2 * π * k := hk

/-- An integer multiple `2πk` in the open interval of radius `2π` about `2πn` has `k = n`. -/
theorem int_eq_of_two_pi_mul (k n : ℤ) (x : ℝ) (hx : x = 2 * π * k)
    (h1 : 2 * π * ((n : ℝ) - 1) < x) (h2 : x < 2 * π * ((n : ℝ) + 1)) : k = n := by
  have hπ : 0 < 2 * π := by positivity
  rw [hx] at h1 h2
  have h1' : ((n : ℝ) - 1) < k := lt_of_mul_lt_mul_left h1 hπ.le
  have h2' : (k : ℝ) < n + 1 := lt_of_mul_lt_mul_left h2 hπ.le
  have h3 : n - 1 < k := by exact_mod_cast h1'
  have h4 : k < n + 1 := by exact_mod_cast h2'
  omega

theorem triangle_oarg (z a b q : E3) (hz : ‖z‖ = 1) (h₁ : ⟪cross z a, b⟫ ≠ 0)
    (h₂ : ⟪cross z b, q⟫ ≠ 0) (h₃ : ⟪cross z q, a⟫ ≠ 0) :
    oarg z a b + oarg z b q + oarg z q a =
      if 0 < ⟪cross z a, b⟫ ∧ 0 < ⟪cross z b, q⟫ ∧ 0 < ⟪cross z q, a⟫ then 2 * π
      else if ⟪cross z a, b⟫ < 0 ∧ ⟪cross z b, q⟫ < 0 ∧ ⟪cross z q, a⟫ < 0 then -(2 * π)
      else 0 := by
  have htd : ∀ p r : E3, ⟪cross z p, r⟫ ≠ 0 → tdir z p ≠ 0 ∧ tdir z r ≠ 0 := by
    intro p r h
    constructor
    · intro h0
      apply h
      rw [← inner_cross_tdir, h0]
      simp [cross]
    · intro h0
      apply h
      rw [← inner_cross_tdir, h0]
      simp [cross]
  obtain ⟨ha, hb⟩ := htd a b h₁
  obtain ⟨-, hq⟩ := htd b q h₂
  obtain ⟨k, hk⟩ := sum_oarg_mem z hz 2 ![a, b, q] (by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hq)
  have hsum : oarg z a b + oarg z b q + oarg z q a = 2 * π * k := by
    rw [← hk, Fin.sum_univ_three]
    simp
  have hπ := Real.pi_pos
  -- each oriented angle lies in `(-π, π)` and has the sign of its determinant
  have hsign : ∀ {s d : ℝ}, d ≠ 0 → (0 < d → 0 < s ∧ s < π) → (d < 0 → -π < s ∧ s < 0) →
      -π < s ∧ s < π ∧ (0 ≤ s → 0 < d) ∧ (s ≤ 0 → d < 0) := by
    intro s d hd hp hn
    rcases lt_or_gt_of_ne hd with h | h
    · obtain ⟨h1, h2⟩ := hn h
      exact ⟨h1, by linarith, fun hs => by linarith, fun _ => h⟩
    · obtain ⟨h1, h2⟩ := hp h
      exact ⟨by linarith, h2, fun _ => h, fun hs => by linarith⟩
  obtain ⟨l1, u1, p1, n1⟩ := hsign h₁ (oarg_mem_of_det z a b).1 (oarg_mem_of_det z a b).2
  obtain ⟨l2, u2, p2, n2⟩ := hsign h₂ (oarg_mem_of_det z b q).1 (oarg_mem_of_det z b q).2
  obtain ⟨l3, u3, p3, n3⟩ := hsign h₃ (oarg_mem_of_det z q a).1 (oarg_mem_of_det z q a).2
  obtain ⟨o1, -⟩ := oarg_mem_of_det z a b
  obtain ⟨o2, -⟩ := oarg_mem_of_det z b q
  obtain ⟨o3, -⟩ := oarg_mem_of_det z q a
  obtain ⟨-, m1⟩ := oarg_mem_of_det z a b
  obtain ⟨-, m2⟩ := oarg_mem_of_det z b q
  obtain ⟨-, m3⟩ := oarg_mem_of_det z q a
  split_ifs with hP hN
  · have hk1 := int_eq_of_two_pi_mul k 1 _ hsum
      (by push_cast; linarith [(o1 hP.1).1, (o2 hP.2.1).1, (o3 hP.2.2).1])
      (by push_cast; linarith)
    rw [hsum, hk1]
    push_cast
    ring
  · have hk1 := int_eq_of_two_pi_mul k (-1) _ hsum
      (by push_cast; linarith)
      (by push_cast; linarith [(m1 hN.1).2, (m2 hN.2.1).2, (m3 hN.2.2).2])
    rw [hsum, hk1]
    push_cast
    ring
  · have hneg : oarg z a b < 0 ∨ oarg z b q < 0 ∨ oarg z q a < 0 := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hP ⟨p1 h.1, p2 h.2.1, p3 h.2.2⟩
    have hpos : 0 < oarg z a b ∨ 0 < oarg z b q ∨ 0 < oarg z q a := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hN ⟨n1 h.1, n2 h.2.1, n3 h.2.2⟩
    have hk0 := int_eq_of_two_pi_mul k 0 _ hsum
      (by push_cast; rcases hpos with h | h | h <;> linarith)
      (by push_cast; rcases hneg with h | h | h <;> linarith)
    rw [hsum, hk0]
    simp

theorem injective_of_winding_one (z : E3) (hz : ‖z‖ = 1) (L : ℕ) (w : Fin (L + 1) → E3)
    (hpos : ∀ i, 0 < ⟪cross z (w i), w (i + 1)⟫)
    (hsum : ∑ i, oarg z (w i) (w (i + 1)) = 2 * π) : Function.Injective w := by
  set W : ℕ → E3 := fun k => w (k : Fin (L + 1)) with hW
  have hWsucc : ∀ k : ℕ, W (k + 1) = w ((k : Fin (L + 1)) + 1) := by
    intro k
    simp only [hW, Nat.cast_succ]
  have hWpos : ∀ k : ℕ, 0 < ⟪cross z (W k), W (k + 1)⟫ := fun k => by
    rw [hWsucc]
    exact hpos _
  have hterm : ∀ k : ℕ, 0 < oarg z (W k) (W (k + 1)) :=
    fun k => ((oarg_mem_of_det z (W k) (W (k + 1))).1 (hWpos k)).1
  have htdir : ∀ k : ℕ, tdir z (W k) ≠ 0 := by
    intro k h
    have h' := hWpos k
    rw [← inner_cross_tdir, h] at h'
    simp [cross] at h'
  have hfull : ∑ k ∈ Finset.range (L + 1), oarg z (W k) (W (k + 1)) = 2 * π := by
    rw [← hsum, ← Fin.sum_univ_eq_sum_range (fun k => oarg z (W k) (W (k + 1)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hWsucc]
    simp only [hW, Fin.cast_val_eq_self]
  have key : ∀ i j : Fin (L + 1), i.val < j.val → w i = w j → False := by
    intro i j hlt hij
    have hb : j.val ≤ L := Nat.lt_succ_iff.mp j.isLt
    have hWa : W i.val = w i := by simp only [hW, Fin.cast_val_eq_self]
    have hWb : W j.val = w j := by simp only [hW, Fin.cast_val_eq_self]
    obtain ⟨n, hn⟩ := sum_oarg_closed z hz (j.val - i.val) (fun k => W (i.val + k))
      (fun k => htdir (i.val + k))
      (by simp only [Nat.add_sub_cancel' hlt.le, add_zero]; rw [hWb, hWa, hij])
    have hIco : ∑ k ∈ Finset.Ico i.val j.val, oarg z (W k) (W (k + 1)) = 2 * π * n := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact hn
    have hpos' : 0 < ∑ k ∈ Finset.Ico i.val j.val, oarg z (W k) (W (k + 1)) :=
      Finset.sum_pos (fun k _ => hterm k) ⟨i.val, Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩⟩
    have hlt' : ∑ k ∈ Finset.Ico i.val j.val, oarg z (W k) (W (k + 1)) < 2 * π := by
      rw [← hfull, ← Finset.sum_range_add_sum_Ico _ (show i.val ≤ L + 1 by omega),
        ← Finset.sum_Ico_consecutive _ hlt.le (show j.val ≤ L + 1 by omega)]
      have h1 : 0 ≤ ∑ k ∈ Finset.range i.val, oarg z (W k) (W (k + 1)) :=
        Finset.sum_nonneg fun k _ => (hterm k).le
      have h2 : 0 < ∑ k ∈ Finset.Ico j.val (L + 1), oarg z (W k) (W (k + 1)) :=
        Finset.sum_pos (fun k _ => hterm k) ⟨j.val, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
      linarith
    rw [hIco] at hpos' hlt'
    have hpi := Real.pi_pos
    have hn0 : (0 : ℝ) < n := by nlinarith
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have h0 : (0 : ℤ) < n := by exact_mod_cast hn0
    have h1 : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact key i j h hij
  · exact key j i h hij.symm

end Tammes15
