import Tammes15.FaceChain.Basic
import Tammes15.TwoConn.Farm
import Tammes15.Trigrows.Points
import Tammes15.Trigrows.Sdist

/-!
# Lemma threeconn in cone form

Section 3 of the paper, Lemma threeconn, from the combinatorial faces of an angular rotation system:
strict support (`StrictSupportFace`), corners in `(0, π)` and simple face walks. A vertex of a face
other than the ends of its corner at `u` lies strictly inside that corner (`face_vertex_sector`);
no neighbour of `u` lies strictly inside a corner (`sector_no_neighbor`) and distinct corners at `u`
are disjoint (`sector_disjoint`), so two faces through `u` and `v` have `v` at an end of their
corners at `u` (`face_meet`). If `{u, v}` separates `G`, the rotation at `u` changes component on
both arcs between two neighbours in different parts (`two_inner_changes`), and the face through
such a corner passes through `v` (`face_passes`); this makes `u v` an edge bordering three faces,
or two faces meet without an edge, both impossible (`threeconn`).
-/

open Real Matrix WithLp InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15.FaceChain

open Tammes15.Vendor.EM8.SquareAntiprismVerification

theorem det_trans (u a p q r : E3) (hp : 0 < ⟪cross u a, p⟫)
    (hq : 0 < ⟪cross u a, q⟫) (hr : 0 < ⟪cross u a, r⟫) (hpq : 0 < ⟪cross u p, q⟫)
    (hqr : 0 < ⟪cross u q, r⟫) : 0 < ⟪cross u p, r⟫ := by
  have plucker : ⟪cross u a, p⟫ * ⟪cross u q, r⟫ - ⟪cross u a, q⟫ * ⟪cross u p, r⟫ + ⟪cross u a, r⟫ * ⟪cross u p, q⟫ = 0 := by
    dsimp [cross]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.vec3_dotProduct, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring_nf
  have hsum : 0 < ⟪cross u a, p⟫ * ⟪cross u q, r⟫ + ⟪cross u a, r⟫ * ⟪cross u p, q⟫ :=
    add_pos (mul_pos hp hqr) (mul_pos hr hpq)
  have hpos : 0 < ⟪cross u a, q⟫ * ⟪cross u p, r⟫ := by
    linarith
  exact pos_of_mul_pos_right hpos (by linarith)

theorem sector_no_neighbor {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0) (hR : IsAngular R x)
    (e k : G.Dart) (hk : k.fst = e.fst) (hke : k ≠ e) :
    ¬ (0 < ⟪cross (x e.fst) (x e.snd), x k.snd⟫ ∧
      0 < ⟪cross (x e.fst) (x k.snd), x (R.rot e).snd⟫) := by
  intro h
  rcases h with ⟨h1, h2⟩
  set u := x e.fst with hu
  set a := x e.snd with ha
  set b := x (R.rot e).snd with hb
  set k' := x k.snd with hk'
  have hu_norm : ‖u‖ = 1 := hx e.fst
  have ha_tdir : tdir u a ≠ 0 := by
    rw [hu, ha]
    exact htd e
  have hk'_tdir : tdir u k' ≠ 0 := by
    rw [hu, hk']
    -- need to use hk : k.fst = e.fst
    have : k.fst = e.fst := hk
    -- htd k gives tdir (x k.fst) (x k.snd) ≠ 0
    -- but we need tdir (x e.fst) (x k.snd) ≠ 0
    -- Since k.fst = e.fst, this follows
    simpa [hk] using htd k
  have hb_tdir : tdir u b ≠ 0 := by
    rw [hu, hb]
    have : (R.rot e).fst = e.fst := R.rot_fst e
    simpa [this] using htd (R.rot e)
  have hα_pos : 0 < ocorner u a k' ∧ ocorner u a k' < π := by
    apply (Tammes15.ocorner_pos_lt_pi_iff u a k').mpr
    -- need to show 0 < ⟪cross u a, k'⟫
    -- but h1 says 0 < ⟪cross (x e.fst) (x e.snd), x k.snd⟫
    simpa [hu, ha, hk'] using h1
  have hβ_pos : 0 < ocorner u k' b ∧ ocorner u k' b < π := by
    apply (Tammes15.ocorner_pos_lt_pi_iff u k' b).mpr
    simpa [hu, hk', hb] using h2
  rcases hα_pos with ⟨hα_pos', hα_lt_pi⟩
  rcases hβ_pos with ⟨hβ_pos', hβ_lt_pi⟩
  set α := ocorner u a k' with hα_def
  set β := ocorner u k' b with hβ_def
  have h_sum_nonneg : 0 ≤ α + β := by linarith
  have h_sum_lt_two_pi : α + β < 2 * π := by linarith
  have h_sum_mem_Ico : α + β ∈ Set.Ico (0 : ℝ) (0 + (2 * π)) := by
    rw [zero_add]
    exact ⟨h_sum_nonneg, h_sum_lt_two_pi⟩
  have h_add_eq : ocorner u a b = toIcoMod Real.two_pi_pos 0 (α + β) := by
    rw [hα_def, hβ_def]
    exact Tammes15.ocorner_add u a k' b hu_norm ha_tdir hk'_tdir hb_tdir
  have h_toIcoMod_eq : toIcoMod Real.two_pi_pos 0 (α + β) = α + β := by
    rw [toIcoMod_eq_self Real.two_pi_pos]
    exact h_sum_mem_Ico
  have h_ab_gt_α : ocorner u a k' < ocorner u a b := by
    rw [h_add_eq, h_toIcoMod_eq, hα_def]
    linarith
  have h_ang : ocorner u a b ≤ ocorner u a k' := by
    -- from hR : IsAngular R x
    -- hR e k hk hke : ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ≤ ocorner (x e.fst) (x e.snd) (x k.snd)
    have := hR e k hk hke
    simpa [hu, ha, hb, hk'] using this
  linarith

theorem par_neighbors {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (d : ℝ) (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d)
    (htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0)
    (f g : G.Dart) (hfg : f.fst = g.fst) (hne : f ≠ g)
    (h0 : ⟪cross (x f.fst) (x f.snd), x g.snd⟫ = 0) (w : E3) :
    ¬ (0 < ⟪cross (x f.fst) (x f.snd), w⟫ ∧ 0 < ⟪cross (x f.fst) (x g.snd), w⟫) := by
  set u := x f.fst with hu
  set a := x f.snd with ha
  set b := x g.snd with hb
  set A := tdir u a with hA
  set B := tdir u b with hB
  have hu_norm : ‖u‖ = 1 := hx f.fst
  have ha_norm : ‖a‖ = 1 := hx f.snd
  have hb_norm : ‖b‖ = 1 := hx g.snd
  have hB_ne_zero : B ≠ 0 := by
    rw [hB]
    have h := htd g
    rw [hfg.symm] at h
    simpa [hu, hb] using h
  have hA_ne_zero : A ≠ 0 := by
    rw [hA]
    simpa [hu, ha] using htd f
  -- cross v v = 0
  have h_cross_self : ∀ (v : E3), cross v v = 0 := by
    intro v
    dsimp [cross]
    simp [cross_self]
  -- cross v (tdir v w) = cross v w
  have h_cross_tdir_eq : ∀ (v w : E3), cross v (tdir v w) = cross v w := by
    intro v w
    dsimp [tdir, cross]
    simp [cross_self, LinearMap.map_sub]
  -- triple product expansion: cross u (cross v w) = ⟪u, w⟫ • v - ⟪v, u⟫ • w
  have h_cross_cross_eq : ∀ (u v w : E3), cross u (cross v w) = ⟪u, w⟫ • v - ⟪v, u⟫ • w := by
    intro u v w
    dsimp [cross]
    have h := cross_cross_eq_smul_sub_smul' (ofLp u) (ofLp v) (ofLp w)
    have h_dot1 : (ofLp u) ⬝ᵥ (ofLp w) = ⟪u, w⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp
    have h_dot2 : (ofLp v) ⬝ᵥ (ofLp u) = ⟪v, u⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp
    rw [h_dot1, h_dot2] at h
    apply_fun toLp 2 at h
    simpa [cross, LinearMap.map_sub, LinearMap.map_smul] using h
  -- ⟪u, u⟫ = 1
  have hu_inner_self : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu_norm]
    norm_num
  -- ⟪u, tdir u a⟫ = 0 and ⟪u, tdir u b⟫ = 0
  have h_tdir_orthogonal : ⟪u, tdir u a⟫ = 0 := by
    dsimp [tdir]
    rw [inner_sub_right, inner_smul_right, hu_inner_self, mul_one, sub_self]
  have h_tdir_orthogonal_B : ⟪u, tdir u b⟫ = 0 := by
    dsimp [tdir]
    rw [inner_sub_right, inner_smul_right, hu_inner_self, mul_one, sub_self]
  -- cross u (cross A B) = 0
  have h_cross_u_cross_AB : cross u (cross A B) = 0 := by
    rw [h_cross_cross_eq u A B, hA, hB]
    have h1 : ⟪tdir u a, u⟫ = 0 := by rw [real_inner_comm, h_tdir_orthogonal]
    rw [h_tdir_orthogonal_B, h1]
    simp
  -- cross u (cross u Z) = ⟪u, Z⟫ • u - (‖u‖ ^ 2) • Z
  have h_cross_u_cross_u_Z : ∀ (Z : E3), cross u (cross u Z) = (⟪u, Z⟫ • u) - ((‖u‖ ^ 2) • Z) := by
    intro Z
    rw [h_cross_cross_eq u u Z]
    rw [real_inner_self_eq_norm_sq, hu_norm]
  -- cross A B = 0
  have h_cross_AB_zero : cross A B = 0 := by
    have h_eq : (⟪u, cross A B⟫ • u) - ((‖u‖ ^ 2) • cross A B) = 0 := by
      calc
        (⟪u, cross A B⟫ • u) - ((‖u‖ ^ 2) • cross A B) = cross u (cross u (cross A B)) := by
          rw [h_cross_u_cross_u_Z (cross A B)]
        _ = cross u 0 := by rw [h_cross_u_cross_AB]
        _ = 0 := by
          dsimp [cross]
          simp
    have h_inner_zero : ⟪u, cross A B⟫ = 0 := by
      rw [hA, hB]
      rw [inner_cross_tdir]
      exact h0
    rw [h_inner_zero] at h_eq
    rw [hu_norm] at h_eq
    have h0_smul : (0 : ℝ) • u = (0 : E3) := by simp
    have h1_sq : ((1 : ℝ) ^ 2) = (1 : ℝ) := by norm_num
    rw [h0_smul, h1_sq] at h_eq
    have h_neg : -(cross A B) = 0 := by
      simpa using h_eq
    simpa using neg_eq_zero.mp h_neg
  -- Now: cross A (cross A B) = 0, which gives ⟪A, B⟫ • A = ‖A‖² • B
  have h_eq_AB : ⟪A, B⟫ • A = (‖A‖ ^ 2) • B := by
    have h_cross_A_cross_AB : cross A (cross A B) = 0 := by
      rw [h_cross_AB_zero]
      dsimp [cross]
      simp
    rw [h_cross_cross_eq A A B] at h_cross_A_cross_AB
    have hA_inner_self : ⟪A, A⟫ = ‖A‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
    rw [hA_inner_self] at h_cross_A_cross_AB
    exact sub_eq_zero.mp h_cross_A_cross_AB
  -- Let t := ⟪A, B⟫ / (‖A‖ ^ 2). Since ‖A‖² > 0, we can divide.
  have h_norm_A_sq_pos : 0 < ‖A‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hA_ne_zero) 2
  set t := ⟪A, B⟫ / (‖A‖ ^ 2) with ht
  have hB_eq_tA : B = t • A := by
    calc
      B = (1 / (‖A‖ ^ 2)) • ((‖A‖ ^ 2) • B) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ h_norm_A_sq_pos.ne', one_smul]
      _ = (1 / (‖A‖ ^ 2)) • (⟪A, B⟫ • A) := by rw [← h_eq_AB, smul_comm]
      _ = ((⟪A, B⟫ / (‖A‖ ^ 2)) • A) := by
        simp [div_eq_inv_mul, mul_smul]
      _ = t • A := by rw [ht]
  -- Now we have two cases: t ≤ 0 or t > 0
  by_cases ht_nonpos : t ≤ 0
  · -- t ≤ 0: then ⟪cross u b, w⟫ = t * ⟪cross u a, w⟫ ≤ 0, contradiction
    intro h
    rcases h with ⟨hpos1, hpos2⟩
    have h_cross_u_b_eq : cross u b = cross u B := by
      rw [hB, h_cross_tdir_eq u b]
    have h_cross_u_a_eq : cross u a = cross u A := by
      rw [hA, h_cross_tdir_eq u a]
    have h_cross_u_B : cross u B = t • cross u A := by
      rw [hB_eq_tA]
      dsimp [cross]
      simp
    have hpos2' : 0 < ⟪t • cross u A, w⟫ := by
      rw [h_cross_u_b_eq, h_cross_u_B] at hpos2
      exact hpos2
    rw [inner_smul_left] at hpos2'
    have h_star : (starRingEnd ℝ) t = t := by simp
    rw [h_star] at hpos2'
    rw [← h_cross_u_a_eq] at hpos2'
    have h_nonpos : t * ⟪cross u a, w⟫ ≤ 0 := by
      nlinarith
    nlinarith
  · -- t > 0: then ocornor u a b = 0, leading to a = b, contradiction with hne
    have ht_pos : 0 < t := lt_of_not_ge ht_nonpos
    have h_inner_ua_eq_ub : ⟪u, a⟫ = ⟪u, b⟫ := by
      have e1 : sdist u a = d := hG f.fst f.snd f.adj
      have e2 : sdist u b = d := by
        have := hG g.fst g.snd g.adj
        rw [← hfg] at this
        exact this
      rw [← cos_sdist u a hu_norm ha_norm, ← cos_sdist u b hu_norm hb_norm, e1, e2]
    have h_ocornor_zero : ocorner u a b = 0 := by
      rw [ocorner, ← hA, ← hB]
      have h_inner_cross_AB : ⟪u, cross A B⟫ = 0 := by
        rw [hA, hB, inner_cross_tdir]
        exact h0
      rw [h_inner_cross_AB]
      have h_inner_AB_pos : 0 < ⟪A, B⟫ := by
        rw [hB_eq_tA]
        rw [inner_smul_right]
        have h_norm_A_sq : ⟪A, A⟫ = ‖A‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
        rw [h_norm_A_sq]
        exact mul_pos ht_pos h_norm_A_sq_pos
      have h_arg_zero : Complex.arg (⟨⟪A, B⟫, (0 : ℝ)⟩ : ℂ) = 0 := by
        have h_nonneg : 0 ≤ ⟪A, B⟫ := le_of_lt h_inner_AB_pos
        simpa [Complex.ofReal] using Complex.arg_ofReal_of_nonneg h_nonneg
      simp [h_arg_zero]
    have ha_eq_b : a = b := by
      apply eq_of_ocorner_eq_zero u a b hu_norm ha_norm hb_norm h_inner_ua_eq_ub ?_ h_ocornor_zero
      rw [← hA]
      exact hA_ne_zero
    have h_snd_eq : f.snd = g.snd := hinj ha_eq_b
    have h_f_eq_g : f = g := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext hfg h_snd_eq
    exact fun _ => hne h_f_eq_g

theorem sector_disjoint {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hinj : Function.Injective x) (d : ℝ) (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d)
    (htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (e₁ e₂ : G.Dart) (h12 : e₁.fst = e₂.fst) (hne : e₁ ≠ e₂) (w : E3) :
    ¬ (0 < ⟪cross (x e₁.fst) (x e₁.snd), w⟫ ∧ 0 < ⟪cross (x e₁.fst) w, x (R.rot e₁).snd⟫ ∧
      0 < ⟪cross (x e₁.fst) (x e₂.snd), w⟫ ∧ 0 < ⟪cross (x e₁.fst) w, x (R.rot e₂).snd⟫) := by
  intro h
  rcases h with ⟨h1, h2, h3, h4⟩
  have hu : x e₁.fst = x e₂.fst := by rw [h12]
  have hb₁ : 0 < ⟪cross (x e₁.fst) (x e₁.snd), x (R.rot e₁).snd⟫ :=
    (ocorner_pos_lt_pi_iff (x e₁.fst) (x e₁.snd) (x (R.rot e₁).snd)).mp (hcorner e₁)
  have hb₂ : 0 < ⟪cross (x e₂.fst) (x e₂.snd), x (R.rot e₂).snd⟫ :=
    (ocorner_pos_lt_pi_iff (x e₂.fst) (x e₂.snd) (x (R.rot e₂).snd)).mp (hcorner e₂)
  have h_cross_antisymm (u a b : E3) : ⟪cross u a, b⟫ = -⟪cross u b, a⟫ := by
    have h1 : ⟪cross u a, b⟫ = (ofLp u ⨯₃ ofLp a) ⬝ᵥ ofLp b := by
      simp [cross, PiLp.inner_apply, dotProduct, mul_comm]
    have h2 : (ofLp u ⨯₃ ofLp a) ⬝ᵥ ofLp b = -((ofLp u ⨯₃ ofLp b) ⬝ᵥ ofLp a) := by
      rw [dotProduct_comm, triple_product_permutation (ofLp b) (ofLp u) (ofLp a),
        ← _root_.cross_anticomm (ofLp b) (ofLp a), dotProduct_neg,
        dotProduct_comm (ofLp u ⨯₃ ofLp b) (ofLp a),
        triple_product_permutation (ofLp a) (ofLp u) (ofLp b)]
    have h3 : -((ofLp u ⨯₃ ofLp b) ⬝ᵥ ofLp a) = -⟪cross u b, a⟫ := by
      simp [cross, PiLp.inner_apply, dotProduct, mul_comm]
    rw [h1, h2, h3]
  by_cases hsign : 0 < ⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫
  · -- case [a₁, a₂] > 0
    have h_det : 0 < ⟪cross (x e₁.fst) (x e₂.snd), x (R.rot e₁).snd⟫ :=
      det_trans (x e₁.fst) (x e₁.snd) (x e₂.snd) w (x (R.rot e₁).snd) hsign h1 hb₁ h3 h2
    have h_sector := sector_no_neighbor R x hx htd hR e₁ e₂ h12.symm hne.symm
    apply h_sector
    exact ⟨hsign, h_det⟩
  · -- case ¬ ([a₁, a₂] > 0)
    by_cases hsign' : 0 < ⟪cross (x e₂.fst) (x e₂.snd), x e₁.snd⟫
    · -- case [a₂, a₁] > 0 (which is equivalent to [a₁, a₂] < 0)
      have h_det : 0 < ⟪cross (x e₂.fst) (x e₁.snd), x (R.rot e₂).snd⟫ :=
        det_trans (x e₂.fst) (x e₂.snd) (x e₁.snd) w (x (R.rot e₂).snd) hsign' (by rwa [← hu]) hb₂
          (by simpa [hu] using h1) (by simpa [hu] using h4)
      have h_sector := sector_no_neighbor R x hx htd hR e₂ e₁ h12 hne
      apply h_sector
      exact ⟨hsign', h_det⟩
    · -- case [a₁, a₂] = 0 (since it's not > 0 and not < 0)
      have h_antisymm_rel : ⟪cross (x e₂.fst) (x e₂.snd), x e₁.snd⟫ = -⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫ := by
        calc
          ⟪cross (x e₂.fst) (x e₂.snd), x e₁.snd⟫ = ⟪cross (x e₁.fst) (x e₂.snd), x e₁.snd⟫ := by rw [← hu]
          _ = -⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫ := by rw [h_cross_antisymm]
      have hzero : ⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫ = 0 := by
        by_contra hne_zero
        have h_lt_or_gt : ⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫ < 0 ∨
          0 < ⟪cross (x e₁.fst) (x e₁.snd), x e₂.snd⟫ := by
          exact lt_or_gt_of_ne hne_zero
        rcases h_lt_or_gt with (hlt | hgt)
        · -- if [a₁, a₂] < 0, then [a₂, a₁] > 0, contradicting hsign'
          have : 0 < ⟪cross (x e₂.fst) (x e₂.snd), x e₁.snd⟫ := by
            linarith [h_antisymm_rel, hlt]
          exact hsign' this
        · -- if [a₁, a₂] > 0, contradicting hsign
          exact hsign hgt
      have h_par := par_neighbors x hx hinj d hG htd e₁ e₂ h12 hne hzero w
      apply h_par
      exact ⟨h1, h3⟩

theorem face_vertex_sector {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hS : StrictSupportFace R x)
    (e : G.Dart) (n : ℕ) (hu : ((R.face ^ n) e).fst ≠ e.fst)
    (ha : ((R.face ^ n) e).fst ≠ e.snd) (hb : ((R.face ^ n) e).fst ≠ (R.rot e).snd) :
    0 < ⟪cross (x e.fst) (x e.snd), x ((R.face ^ n) e).fst⟫ ∧
      0 < ⟪cross (x e.fst) (x ((R.face ^ n) e).fst), x (R.rot e).snd⟫ := by
  set w := (R.face ^ n) e with hw_def
  have h_symm_fst (d : G.Dart) : (SimpleGraph.Dart.symm d).fst = d.snd := rfl
  have h_symm_snd (d : G.Dart) : (SimpleGraph.Dart.symm d).snd = d.fst := rfl
  have h_rot_symm_fst (d : G.Dart) : (R.rot.symm d).fst = d.fst := by
    rw [← R.rot_fst (R.rot.symm d), Equiv.apply_symm_apply]
  have hface_fst : (R.face e).fst = e.snd := by
    calc
      (R.face e).fst = (R.rot.symm (SimpleGraph.Dart.symm e)).fst := rfl
      _ = (SimpleGraph.Dart.symm e).fst := by rw [h_rot_symm_fst]
      _ = e.snd := h_symm_fst e
  have hw_ne_e : w ≠ e := by
    intro h_eq
    apply hu
    rw [h_eq]
  have hw_ne_face_e : w ≠ R.face e := by
    intro h_eq
    apply ha
    rw [← hface_fst, ← h_eq]
  have hfirst : 0 < ⟪cross (x e.fst) (x e.snd), x w.fst⟫ := hS e n hw_ne_e hw_ne_face_e
  set g := (R.rot e).symm with hg_def
  have hface_g : R.face g = e := by
    calc
      R.face g = R.rot.symm (SimpleGraph.Dart.symm ((R.rot e).symm)) := rfl
      _ = R.rot.symm (R.rot e) := by rw [SimpleGraph.Dart.symm_symm]
      _ = e := by rw [Equiv.symm_apply_apply]
  have hg_fst : g.fst = (R.rot e).snd := h_symm_fst (R.rot e)
  have hg_snd : g.snd = e.fst := by
    calc
      g.snd = ((R.rot e).symm).snd := rfl
      _ = (R.rot e).fst := h_symm_snd (R.rot e)
      _ = e.fst := R.rot_fst e
  have h_pow_succ : (R.face ^ (n+1)) g = w := by
    calc
      (R.face ^ (n+1)) g = ((R.face ^ n) * R.face) g := by rw [pow_succ]
      _ = (R.face ^ n) (R.face g) := rfl
      _ = (R.face ^ n) e := by rw [hface_g]
      _ = w := rfl
  have hw_ne_g' : (R.face ^ (n+1)) g ≠ g := by
    rw [h_pow_succ]
    intro h_eq
    apply hb
    rw [← hg_fst, ← h_eq]
  have hw_ne_face_g' : (R.face ^ (n+1)) g ≠ R.face g := by
    rw [h_pow_succ, hface_g]
    intro h_eq
    apply hu
    rw [h_eq]
  have hsecond' : 0 < ⟪cross (x g.fst) (x g.snd), x ((R.face ^ (n+1)) g).fst⟫ :=
    hS g (n+1) hw_ne_g' hw_ne_face_g'
  have hsecond : 0 < ⟪cross (x e.fst) (x w.fst), x (R.rot e).snd⟫ := by
    rw [hg_fst, hg_snd, h_pow_succ] at hsecond'
    -- hsecond' : 0 < ⟪cross (x (R.rot e).snd) (x e.fst), x w.fst⟫
    have h_eq_inner : ⟪cross (x (R.rot e).snd) (x e.fst), x w.fst⟫ =
                      ⟪cross (x e.fst) (x w.fst), x (R.rot e).snd⟫ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ)
        (cross (x (R.rot e).snd) (x e.fst)) (x w.fst)]
      rw [EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ)
        (cross (x e.fst) (x w.fst)) (x (R.rot e).snd)]
      simp [cross]
      rw [triple_product_permutation (ofLp (x w.fst)) (ofLp (x (R.rot e).snd)) (ofLp (x e.fst))]
    rw [h_eq_inner] at hsecond'
    exact hsecond'
  exact And.intro hfirst hsecond

theorem face_meet {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hinj : Function.Injective x) (d : ℝ) (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d)
    (htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hS : StrictSupportFace R x)
    (e₁ e₂ : G.Dart) (h12 : e₁.fst = e₂.fst) (hne : e₁ ≠ e₂) (v : V) (hvu : v ≠ e₁.fst)
    (n₁ n₂ : ℕ) (h₁ : ((R.face ^ n₁) e₁).fst = v) (h₂ : ((R.face ^ n₂) e₂).fst = v) :
    v = e₁.snd ∨ v = (R.rot e₁).snd := by
  by_cases hv1 : v = e₁.snd
  · left; exact hv1
  · by_cases hv2 : v = (R.rot e₁).snd
    · right; exact hv2
    · -- v ≠ e₁.snd and v ≠ (R.rot e₁).snd
      have h_face1 := face_vertex_sector R x hS e₁ n₁ (by rw [h₁]; exact hvu)
        (by rw [h₁]; exact hv1) (by rw [h₁]; exact hv2)
      rcases h_face1 with ⟨hA, hB⟩
      rw [h₁] at hA hB
      -- hA : 0 < ⟪cross (x e₁.fst) (x e₁.snd), x v⟫
      -- hB : 0 < ⟪cross (x e₁.fst) (x v), x (R.rot e₁).snd⟫
      by_cases hv3 : v = e₂.snd
      · -- case v = e₂.snd
        exfalso
        apply sector_no_neighbor R x hx htd hR e₁ e₂ h12.symm hne.symm
        rw [hv3] at hA hB
        exact ⟨hA, hB⟩
      · by_cases hv4 : v = (R.rot e₂).snd
        · -- case v = (R.rot e₂).snd
          exfalso
          have h_rot_ne : R.rot e₂ ≠ e₁ := by
            intro heq
            apply hv1
            calc
              v = (R.rot e₂).snd := hv4
              _ = e₁.snd := by rw [heq]
          have hk : (R.rot e₂).fst = e₁.fst := by
            rw [R.rot_fst, h12]
          apply sector_no_neighbor R x hx htd hR e₁ (R.rot e₂) hk h_rot_ne
          rw [hv4] at hA hB
          exact ⟨hA, hB⟩
        · -- v ≠ e₂.snd and v ≠ (R.rot e₂).snd
          have h_face2 := face_vertex_sector R x hS e₂ n₂
            (by rw [h₂]; rw [← h12]; exact hvu)
            (by rw [h₂]; exact hv3)
            (by rw [h₂]; exact hv4)
          rcases h_face2 with ⟨hC, hD⟩
          rw [h₂] at hC hD
          rw [← h12] at hC hD
          -- hC : 0 < ⟪cross (x e₁.fst) (x e₂.snd), x v⟫
          -- hD : 0 < ⟪cross (x e₁.fst) (x v), x (R.rot e₂).snd⟫
          exfalso
          apply sector_disjoint R x hx hinj d hG htd hR hcorner e₁ e₂ h12 hne (x v)
          exact ⟨hA, hB, hC, hD⟩

theorem face_passes {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G)
    (hwalk : ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
      ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst)
    (u v : V) (e : G.Dart) (he : e.fst = u)
    (hsep : ¬ AvoidReach G u v e.snd (R.rot e).snd) :
    ∃ n, ((R.face ^ n) e).fst = v := by
  -- Finite instance for G.Dart (needed for Function.Injective.mem_periodicPts)
  have h_finite_dart : Finite G.Dart := by
    apply Finite.of_injective (fun d : G.Dart => d.toProd)
    intro a b h
    apply SimpleGraph.Dart.ext
    exact h
  let m := Function.minimalPeriod (R.face : G.Dart → G.Dart) e
  have hm_pos : 0 < m := by
    have hmem : e ∈ Function.periodicPts (R.face : G.Dart → G.Dart) :=
      Function.Injective.mem_periodicPts (R.face.injective) e
    exact Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hm_ge_two : 2 ≤ m := by
    by_contra! h
    have hm_one : m = 1 := by omega
    have h_fixed : Function.IsFixedPt (R.face : G.Dart → G.Dart) e := by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at hm_one
      exact hm_one
    have h_face_fst_eq_snd : ∀ d : G.Dart, (R.face d).fst = d.snd := by
      intro d
      unfold RotSys.face
      have h_symm_fst : ∀ x : G.Dart, (R.rot.symm x).fst = x.fst := by
        intro x
        have h := R.rot_fst (R.rot.symm x)
        simpa [Equiv.apply_symm_apply] using h.symm
      simp [h_symm_fst]
    have h_fst_eq_snd : e.fst = e.snd := by
      calc
        e.fst = (R.face e).fst := by rw [h_fixed]
        _ = e.snd := h_face_fst_eq_snd e
    exact e.fst_ne_snd h_fst_eq_snd
  have h_face_fst_eq_snd : ∀ d : G.Dart, (R.face d).fst = d.snd := by
    intro d
    unfold RotSys.face
    have h_symm_fst : ∀ x : G.Dart, (R.rot.symm x).fst = x.fst := by
      intro x
      have h := R.rot_fst (R.rot.symm x)
      simpa [Equiv.apply_symm_apply] using h.symm
    simp [h_symm_fst]
  have h_face_rot_symm : R.face (R.rot e).symm = e := face_rot_symm R e
  have h_iterate_minimal : (R.face ^ m) e = e :=
    Function.iterate_minimalPeriod (f := R.face) (x := e)
  have hm_one_le : 1 ≤ m := by omega
  have h_pred_eq_symm : (R.face ^ (m - 1)) e = (R.rot e).symm := by
    have h_eq : R.face ((R.face ^ (m - 1)) e) = R.face ((R.rot e).symm) := by
      calc
        R.face ((R.face ^ (m - 1)) e) = ((R.face : Equiv.Perm G.Dart) * (R.face ^ (m - 1))) e := rfl
        _ = ((R.face : Equiv.Perm G.Dart) ^ 1 * (R.face ^ (m - 1))) e := by rw [pow_one]
        _ = ((R.face : Equiv.Perm G.Dart) ^ (1 + (m - 1))) e := by rw [pow_add]
        _ = (R.face ^ m) e := by rw [Nat.add_sub_cancel' hm_one_le]
        _ = e := h_iterate_minimal
        _ = R.face (R.rot e).symm := by rw [h_face_rot_symm]
    exact R.face.injective h_eq
  by_contra! h_no_v
  -- h_no_v : ∀ n, ((R.face ^ n) e).fst ≠ v
  have h_chain : ∀ k, 1 ≤ k → k < m → AvoidReach G u v e.snd (((R.face ^ k) e).fst) := by
    intro k hk1 hkm
    induction' k with k IH
    · linarith
    · -- k.succ
      by_cases hk0 : k = 0
      · -- k.succ = 1
        subst hk0
        unfold AvoidReach
        simpa [h_face_fst_eq_snd, pow_one] using Relation.ReflTransGen.refl (a := e.snd)
      · -- k.succ ≥ 2, so k ≥ 1
        have hk_ge_one : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk0)
        have hk_lt_m : k < m := by omega
        have IH_chain : AvoidReach G u v e.snd (((R.face ^ k) e).fst) :=
          IH hk_ge_one hk_lt_m
        have h_step_adj : G.Adj (((R.face ^ k) e).fst) (((R.face ^ (k.succ)) e).fst) := by
          have h_dart_adj : G.Adj (((R.face ^ k) e).fst) (((R.face ^ k) e).snd) :=
            ((R.face ^ k) e).adj
          have h_face_fst : ((R.face ^ (k.succ)) e).fst = ((R.face ^ k) e).snd := by
            calc
              ((R.face ^ (k.succ)) e).fst = (R.face ((R.face ^ k) e)).fst := by
                simp [pow_succ']
              _ = ((R.face ^ k) e).snd := h_face_fst_eq_snd _
          rw [h_face_fst]
          exact h_dart_adj
        have h_ne_u_k : ((R.face ^ k) e).fst ≠ u := by
          have h := hwalk e 0 k (by omega) (by omega)
          -- h : ((R.face ^ 0) e).fst ≠ ((R.face ^ k) e).fst
          simpa [he] using h.symm
        have h_ne_v_k : ((R.face ^ k) e).fst ≠ v := h_no_v k
        have h_ne_u_k1 : ((R.face ^ (k.succ)) e).fst ≠ u := by
          have h := hwalk e 0 (k.succ) (by omega) (by omega)
          simpa [he] using h.symm
        have h_ne_v_k1 : ((R.face ^ (k.succ)) e).fst ≠ v := h_no_v (k.succ)
        unfold AvoidReach at IH_chain ⊢
        apply Relation.ReflTransGen.tail IH_chain
        exact ⟨h_step_adj, h_ne_u_k, h_ne_v_k, h_ne_u_k1, h_ne_v_k1⟩
  have hm1_lt_m : m - 1 < m := by
    omega
  have h1_le_m1 : 1 ≤ m - 1 := by
    omega
  have h_chain_result : AvoidReach G u v e.snd (((R.face ^ (m - 1)) e).fst) :=
    h_chain (m - 1) h1_le_m1 hm1_lt_m
  have h_pred_fst_eq_rot_snd : ((R.face ^ (m - 1)) e).fst = (R.rot e).snd := by
    calc
      ((R.face ^ (m - 1)) e).fst = (R.rot e).symm.fst := by rw [h_pred_eq_symm]
      _ = (R.rot e).snd := by simp
  rw [h_pred_fst_eq_rot_snd] at h_chain_result
  exact hsep h_chain_result

theorem linear_change {β : Type} (g : ℕ → β) (i j : ℕ) (hij : i ≤ j)
    (h : g i ≠ g j) : ∃ k, i ≤ k ∧ k < j ∧ g k ≠ g (k + 1) := by
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := Nat.le_zero.mp hij
      subst hi0
      exact absurd rfl h
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with (rfl | hi_lt)
      · exfalso; exact h rfl
      · have hi_le_j : i ≤ j := Nat.le_of_lt_succ hi_lt
        by_cases h_eq : g i = g j
        · have hne : g j ≠ g (j + 1) := by
            intro heq; apply h; rw [h_eq, heq]
          exact ⟨j, hi_le_j, Nat.lt_succ_self j, hne⟩
        · rcases ih i hi_le_j h_eq with ⟨k, hk_le, hk_lt, hk_ne⟩
          exact ⟨k, hk_le, Nat.lt_of_lt_of_le hk_lt (Nat.le_succ j), hk_ne⟩

theorem two_inner_changes {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (R : RotSys G) (u v a b : V) (ha : G.Adj u a) (hb : G.Adj u b)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : ¬ AvoidReach G u v a b) :
    ∃ c₁ c₂ : G.Dart, c₁.fst = u ∧ c₂.fst = u ∧ c₁ ≠ c₂ ∧
      c₁.snd ≠ v ∧ (R.rot c₁).snd ≠ v ∧
      ¬ AvoidReach G u v c₁.snd (R.rot c₁).snd ∧ ¬ AvoidReach G u v c₂.snd (R.rot c₂).snd := by
  classical
  -- `AvoidReach` is an equivalence relation
  have hsymm : ∀ p q, AvoidReach G u v p q → AvoidReach G u v q p := by
    intro p q h
    unfold AvoidReach at h ⊢
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hst
      exact Relation.ReflTransGen.head ⟨h1.symm, h4, h5, h2, h3⟩ ih
  have htrans : ∀ p q r, AvoidReach G u v p q → AvoidReach G u v q r → AvoidReach G u v p r :=
    fun p q r h1 h2 => Relation.ReflTransGen.trans h1 h2
  have hrefl : ∀ p, AvoidReach G u v p p := fun p => Relation.ReflTransGen.refl
  have hnotv : ∀ p, p ≠ v → ¬ AvoidReach G u v p v := by
    intro p hp h
    unfold AvoidReach at h
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
    · exact hp h.symm
    · exact hc.2.2.2.2 rfl
  set T := R.rot with hT
  let ea : G.Dart := ⟨(u, a), ha⟩
  let eb : G.Dart := ⟨(u, b), hb⟩
  set k := Function.minimalPeriod T ea with hk
  have hkpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts
    (Function.Injective.mem_periodicPts T.injective ea)
  have hperk : (T ^ k) ea = ea := by
    rw [Equiv.Perm.coe_pow]; exact Function.isPeriodicPt_minimalPeriod T ea
  have hstep : ∀ i, T ((T ^ i) ea) = (T ^ (i + 1)) ea := by
    intro i; rw [pow_succ', Equiv.Perm.mul_apply]
  have hfst : ∀ i, ((T ^ i) ea).fst = u := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← hstep, hT, R.rot_fst, ← hT, ih]
  have hinj : ∀ i j, i < k → j < k → (T ^ i) ea = (T ^ j) ea → i = j := by
    intro i j hi hj h
    refine Function.iterate_injOn_Iio_minimalPeriod (f := ⇑T) (x := ea) hi hj ?_
    simp only [← Equiv.Perm.coe_pow]
    exact h
  -- `eb` is on the rotation orbit of `ea`
  obtain ⟨j, hjk, hj⟩ : ∃ j, j < k ∧ (T ^ j) ea = eb := by
    obtain ⟨m, hm⟩ := (R.rot_cycle ea eb rfl).exists_nat_pow_eq
    refine ⟨m % k, Nat.mod_lt _ hkpos, ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow]
    exact hm
  have hj0 : j ≠ 0 := by
    rintro rfl
    have : b = a := (congrArg (fun e : G.Dart => e.snd) hj).symm
    exact hab (this ▸ hrefl a)
  set g : ℕ → V := fun i => ((T ^ i) ea).snd with hg
  have hg0 : g 0 = a := rfl
  have hgj : g j = b := by simp only [hg, hj]; rfl
  have hgk : g k = a := by simp only [hg, hperk]; rfl
  -- a change of class between two indices of different class
  have hchange : ∀ (p : V) (i i' : ℕ), i ≤ i' → AvoidReach G u v p (g i) →
      ¬ AvoidReach G u v p (g i') →
      ∃ l, i ≤ l ∧ l < i' ∧ ¬ AvoidReach G u v (g l) (g (l + 1)) := by
    intro p i i' hii' hi hi'
    obtain ⟨l, hl1, hl2, hl⟩ := linear_change (fun n => AvoidReach G u v p (g n)) i i' hii'
      (fun h => hi' (h ▸ hi))
    refine ⟨l, hl1, hl2, fun hr => hl ?_⟩
    exact propext ⟨fun h => htrans _ _ _ h hr, fun h => htrans _ _ _ h (hsymm _ _ hr)⟩
  obtain ⟨l₁, -, hl₁j, hc₁⟩ := hchange a 0 j (Nat.zero_le _) (hg0 ▸ hrefl a) (hgj ▸ hab)
  obtain ⟨l₂, hjl₂, hl₂k, hc₂⟩ := hchange b j k hjk.le (hgj ▸ hrefl b)
    (fun h => hab (hsymm _ _ (hgk ▸ h)))
  have hne : (T ^ l₁) ea ≠ (T ^ l₂) ea := fun h => by
    have := hinj l₁ l₂ (by omega) hl₂k h
    omega
  -- one of the two arcs has no vertex `v`
  have hfree : (∀ i, i ≤ j → g i ≠ v) ∨ (∀ i, j ≤ i → i ≤ k → g i ≠ v) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨i₁, hi₁, hv₁⟩, ⟨i₂, hi₂, hi₂', hv₂⟩⟩ := hcon
    have h1 : i₁ ≠ j := fun h => hbv (by rw [← hgj, ← h]; exact hv₁)
    have h2 : i₂ ≠ k := fun h => hav (by rw [← hgk, ← h]; exact hv₂)
    have hd : (T ^ i₁) ea = (T ^ i₂) ea :=
      SimpleGraph.Dart.ext _ _ (Prod.ext ((hfst i₁).trans (hfst i₂).symm) (hv₁.trans hv₂.symm))
    have := hinj i₁ i₂ (by omega) (by omega) hd
    omega
  rcases hfree with hf | hf
  · refine ⟨(T ^ l₁) ea, (T ^ l₂) ea, hfst _, hfst _, hne, hf l₁ hl₁j.le, ?_, ?_, ?_⟩
    · rw [hstep]; exact hf (l₁ + 1) hl₁j
    · rw [hstep]; exact hc₁
    · rw [hstep]; exact hc₂
  · refine ⟨(T ^ l₂) ea, (T ^ l₁) ea, hfst _, hfst _, fun h => hne h.symm, hf l₂ hjl₂ hl₂k.le,
      ?_, ?_, ?_⟩
    · rw [hstep]; exact hf (l₂ + 1) (by omega) hl₂k
    · rw [hstep]; exact hc₂
    · rw [hstep]; exact hc₁

theorem split_neighbors {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (h2 : KConnected G 2) (u v : V) (huv : u ≠ v) (p q : V)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v)
    (hpq : ¬ AvoidReach G u v p q) :
    ∃ a b, G.Adj u a ∧ G.Adj u b ∧ a ≠ v ∧ b ≠ v ∧ ¬ AvoidReach G u v a b := by
  -- From KConnected G 2, the graph with v removed is connected
  have hconn : (G.induce (({v} : Finset V) : Set V)ᶜ).Connected := h2.2 {v} (by simp)
  let s : Set V := (({v} : Finset V) : Set V)ᶜ
  have hp_mem : p ∈ s := by
    dsimp [s]
    simpa using hpv
  have hq_mem : q ∈ s := by
    dsimp [s]
    simpa using hqv
  -- Helper lemma: given x, y in s with ¬ AvoidReach G u v x y, find a neighbor a of u
  -- such that AvoidReach G u v x a and a ≠ v
  have h_exists_neighbor (x y : V) (hx : x ∈ s) (hy : y ∈ s) (hxy : ¬ AvoidReach G u v x y)
      (hx_ne_u : x ≠ u) : ∃ a, G.Adj u a ∧ a ≠ v ∧ AvoidReach G u v x a := by
    have hreach_xy : (G.induce s).Reachable (⟨x, hx⟩ : ↥s) (⟨y, hy⟩ : ↥s) := hconn (⟨x, hx⟩ : ↥s) (⟨y, hy⟩ : ↥s)
    obtain ⟨W⟩ := hreach_xy
    let Sx : Set (↥s) := {z | AvoidReach G u v x z.val}
    have hxSx : (⟨x, hx⟩ : ↥s) ∈ Sx := by
      dsimp [Sx]; exact Relation.ReflTransGen.refl
    have hySx : (⟨y, hy⟩ : ↥s) ∉ Sx := by
      dsimp [Sx]; exact hxy
    obtain ⟨d, hd_darts, hd_fst, hd_snd⟩ :=
      SimpleGraph.Walk.exists_boundary_dart W Sx hxSx hySx
    have hd_fst_avoid : AvoidReach G u v x d.fst.val := hd_fst
    have hd_snd_not_avoid : ¬ AvoidReach G u v x d.snd.val := hd_snd
    have hd_adj : G.Adj d.fst.val d.snd.val :=
      SimpleGraph.induce_adj.mp d.adj
    have hd_fst_ne_v : d.fst.val ≠ v := by
      intro h_eq; have := d.fst.property; rw [h_eq] at this; simpa [s] using this
    have hd_snd_ne_v : d.snd.val ≠ v := by
      intro h_eq; have := d.snd.property; rw [h_eq] at this; simpa [s] using this
    -- Lemma: AvoidReach never reaches u
    have avoidreach_ne_u {a b : V} (h : AvoidReach G u v a b) (hb : b = u) (ha : a ≠ u) : False := by
      rw [hb] at h
      cases h with
      | refl => exact ha rfl
      | tail h_avoid h_adj => exact h_adj.2.2.2.1 rfl
    -- Case analysis on whether d.fst.val = u or d.snd.val = u
    by_cases h_fst_u : d.fst.val = u
    · exfalso; exact avoidreach_ne_u hd_fst_avoid h_fst_u hx_ne_u
    · by_cases h_snd_u : d.snd.val = u
      · -- d.snd.val = u, so d.fst.val is a neighbor of u
        have h_adj_u : G.Adj u d.fst.val := by
          rw [h_snd_u] at hd_adj
          exact hd_adj.symm
        exact ⟨d.fst.val, h_adj_u, hd_fst_ne_v, hd_fst_avoid⟩
      · -- d.fst.val ≠ u and d.snd.val ≠ u, then we can extend the path
        have h_avoid_snd : AvoidReach G u v x d.snd.val :=
          Relation.ReflTransGen.tail hd_fst_avoid ⟨hd_adj, h_fst_u, hd_fst_ne_v, h_snd_u, hd_snd_ne_v⟩
        exfalso; exact hd_snd_not_avoid h_avoid_snd
  -- Symmetry lemma for AvoidReach
  have avoidreach_symm {a b : V} (h : AvoidReach G u v a b) : AvoidReach G u v b a := by
    -- The underlying relation r i j := G.Adj i j ∧ i ≠ u ∧ i ≠ v ∧ j ≠ u ∧ j ≠ v is symmetric
    have r_symm {i j : V} (hij : G.Adj i j ∧ i ≠ u ∧ i ≠ v ∧ j ≠ u ∧ j ≠ v) :
        G.Adj j i ∧ j ≠ u ∧ j ≠ v ∧ i ≠ u ∧ i ≠ v :=
      ⟨hij.1.symm, hij.2.2.2.1, hij.2.2.2.2, hij.2.1, hij.2.2.1⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h_avoid h_adj ih =>
      -- h_avoid : r* a b, h_adj : r b c, ih : r* b a
      -- Need: r* c a
      -- r c b from r_symm h_adj, then trans with ih
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (r_symm h_adj)) ih
  -- Get neighbor a from p
  obtain ⟨a, ha_adj_u, ha_ne_v, ha_avoid⟩ := h_exists_neighbor p q hp_mem hq_mem hpq hpu
  -- Get neighbor b from q (using symmetry: ¬ AvoidReach G u v q p follows from hpq)
  have hqp : ¬ AvoidReach G u v q p := by
    intro h; apply hpq; exact avoidreach_symm h
  obtain ⟨b, hb_adj_u, hb_ne_v, hb_avoid⟩ := h_exists_neighbor q p hq_mem hp_mem hqp hqu
  -- Now we need to show ¬ AvoidReach G u v a b
  have h_not_avoid_ab : ¬ AvoidReach G u v a b := by
    intro h_ab
    apply hpq
    -- From ha_avoid: AvoidReach p a, h_ab: AvoidReach a b, hb_avoid: AvoidReach q b
    -- Need: AvoidReach p q
    have h_pb : AvoidReach G u v p b := Relation.ReflTransGen.trans ha_avoid h_ab
    have h_bq : AvoidReach G u v b q := avoidreach_symm hb_avoid
    exact Relation.ReflTransGen.trans h_pb h_bq
  exact ⟨a, b, ha_adj_u, hb_adj_u, ha_ne_v, hb_ne_v, h_not_avoid_ab⟩

private lemma avoidReach_reachable_compl {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {a b : V} (ha : a ∉ ({u, v} : Finset V)) (hb : b ∉ ({u, v} : Finset V))
    (h : AvoidReach G u v a b) : (G.induce (↑({u, v} : Finset V) : Set V)ᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl =>
      exact SimpleGraph.Reachable.refl _
  | tail hprefix hlast ih =>
      rename_i b' c'
      rcases hlast with ⟨hadj, hb'_ne_u, hb'_ne_v, hc'_ne_u, hc'_ne_v⟩
      have hb'_mem : b' ∉ ({u, v} : Finset V) := by
        simp [hb'_ne_u, hb'_ne_v]
      have ih_reach : (G.induce (↑({u, v} : Finset V) : Set V)ᶜ).Reachable ⟨a, ha⟩ ⟨b', hb'_mem⟩ :=
        ih hb'_mem
      have hadj_induce : (G.induce (↑({u, v} : Finset V) : Set V)ᶜ).Adj ⟨b', hb'_mem⟩ ⟨c', hb⟩ := by
        rw [SimpleGraph.induce_adj]
        exact hadj
      exact ih_reach.trans (SimpleGraph.Adj.reachable hadj_induce)

theorem induce_connected_of_avoid {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (u v : V) (hne : ∃ w, w ≠ u ∧ w ≠ v)
    (h : ∀ p q, p ≠ u → p ≠ v → q ≠ u → q ≠ v → AvoidReach G u v p q) :
    (G.induce (↑({u, v} : Finset V) : Set V)ᶜ).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · -- Preconnected: any two vertices in the complement are reachable
    intro p q
    have hp_mem : p.val ∉ ({u, v} : Finset V) := by
      intro hmem; apply p.property; simpa using hmem
    have hp_ne_u : p.val ≠ u := by
      intro heq; apply hp_mem; simp [heq]
    have hp_ne_v : p.val ≠ v := by
      intro heq; apply hp_mem; simp [heq]
    have hq_mem : q.val ∉ ({u, v} : Finset V) := by
      intro hmem; apply q.property; simpa using hmem
    have hq_ne_u : q.val ≠ u := by
      intro heq; apply hq_mem; simp [heq]
    have hq_ne_v : q.val ≠ v := by
      intro heq; apply hq_mem; simp [heq]
    have havoid : AvoidReach G u v p.val q.val :=
      h p.val q.val hp_ne_u hp_ne_v hq_ne_u hq_ne_v
    have hreach_val : (G.induce (↑({u, v} : Finset V) : Set V)ᶜ).Reachable
        ⟨p.val, hp_mem⟩ ⟨q.val, hq_mem⟩ :=
      avoidReach_reachable_compl hp_mem hq_mem havoid
    simpa [Subtype.eta] using hreach_val
  · -- Nonempty: there is a vertex in the complement of {u, v}
    rcases hne with ⟨w, hwu, hwv⟩
    refine Set.Nonempty.to_subtype ?_
    refine ⟨w, ?_⟩
    simp [hwu, hwv]

theorem kConnected_three_of {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (h2 : KConnected G 2) (hcard : 3 < Fintype.card V)
    (hsplit : ∀ u v : V, u ≠ v → ∀ p q, p ≠ u → p ≠ v → q ≠ u → q ≠ v → AvoidReach G u v p q) :
    KConnected G 3 := by
  refine ⟨hcard, ?_⟩
  intro S hcardS
  by_cases h : S.card < 2
  · exact h2.2 S h
  · have hcard2 : S.card = 2 := by omega
    rcases (Finset.card_eq_two.mp hcard2) with ⟨u, v, huv, hS⟩
    have hne : ∃ w, w ≠ u ∧ w ≠ v := by
      have hcard_uv : ({u, v} : Finset V).card = 2 := by
        simp [huv]
      have hcard_total : ({u, v} : Finset V).card < (Finset.univ : Finset V).card := by
        simpa [hcard_uv] using (by omega : 2 < Fintype.card V)
      rcases Finset.exists_mem_notMem_of_card_lt_card hcard_total with ⟨w, hw, hw_not⟩
      refine ⟨w, ?_, ?_⟩
      · intro h_eq; apply hw_not; simpa [h_eq] using hw
      · intro h_eq; apply hw_not; simpa [h_eq] using hw
    have h_avoid : ∀ p q, p ≠ u → p ≠ v → q ≠ u → q ≠ v → AvoidReach G u v p q :=
      hsplit u v huv
    rw [hS]
    exact Tammes15.FaceChain.induce_connected_of_avoid u v hne h_avoid

theorem card_gt_three {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h2 : KConnected G 2)
    (hdeg : ∀ a, 3 ≤ G.degree a) : 3 < Fintype.card V := by
  have hcard_pos : 0 < Fintype.card V := by
    have h2card : 2 < Fintype.card V := h2.1
    omega
  have h_nonempty : Nonempty V := Fintype.card_pos_iff.mp hcard_pos
  obtain ⟨a⟩ := h_nonempty
  have h_deg_lt : G.degree a < Fintype.card V := SimpleGraph.degree_lt_card_verts a
  have h_deg_ge : 3 ≤ G.degree a := hdeg a
  omega

/-- Lemma threeconn in cone form. -/
theorem threeconn {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotSys G) (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hinj : Function.Injective x) (d : ℝ) (hG : ∀ a b, G.Adj a b → sdist (x a) (x b) = d)
    (htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hS : StrictSupportFace R x) (hdeg : ∀ a, 3 ≤ G.degree a) (h2 : KConnected G 2)
    (hwalk : ∀ e : G.Dart, ∀ m n : ℕ, m < n → n < Function.minimalPeriod R.face e →
      ((R.face ^ m) e).fst ≠ ((R.face ^ n) e).fst) :
    KConnected G 3 := by
  refine kConnected_three_of h2 (card_gt_three h2 hdeg) ?_
  intro u v huv p q hpu hpv hqu hqv
  by_contra hpq
  obtain ⟨a, b, ha, hb, hav, hbv, hab⟩ := split_neighbors h2 u v huv p q hpu hpv hqu hqv hpq
  obtain ⟨c₁, c₂, hc₁, hc₂, hne, hc₁v, hrc₁v, hs₁, hs₂⟩ :=
    two_inner_changes R u v a b ha hb hav hbv hab
  obtain ⟨n₁, hn₁⟩ := face_passes R hwalk u v c₁ hc₁ hs₁
  have hvu : v ≠ c₁.fst := by rw [hc₁]; exact huv.symm
  by_cases huv' : G.Adj u v
  · let ev : G.Dart := ⟨(u, v), huv'⟩
    have hev : ((R.face ^ 1) ev).fst = v := by
      rw [pow_one, face_fst]
    have hne' : c₁ ≠ ev := fun h => hc₁v (by rw [h])
    rcases face_meet R x hx hinj d hG htd hR hcorner hS c₁ ev (by rw [hc₁]) hne' v hvu n₁ 1
      hn₁ hev with h | h
    · exact hc₁v h.symm
    · exact hrc₁v h.symm
  · obtain ⟨n₂, hn₂⟩ := face_passes R hwalk u v c₂ hc₂ hs₂
    rcases face_meet R x hx hinj d hG htd hR hcorner hS c₁ c₂ (hc₁.trans hc₂.symm) hne v hvu
      n₁ n₂ hn₁ hn₂ with h | h
    · apply huv'
      have := c₁.adj
      rwa [hc₁, ← h] at this
    · apply huv'
      have := (R.rot c₁).adj
      rwa [R.rot_fst, hc₁, ← h] at this

end Tammes15.FaceChain
