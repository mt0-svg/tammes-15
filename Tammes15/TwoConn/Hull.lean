import Tammes15.TwoConn.Farm
import Tammes15.Draw.Angular

/-!
# The hull graph at a vertex: links, exposed pairs and the successor plane

Steps S1 to S3 of the proof of Corollary twoconn by the convex hull (paper, Section 3, Corollary
twoconn and Lemma hull). For a finite injective family `x` of unit vectors not contained in a
closed hemisphere (`hB`, which the corner hypothesis gives by `no_closed_hemisphere`), the link of
a vertex `v` is the stereographic image `linkSet x v` of the other points in the plane `(x v)⊥`;
it has `0` strictly inside, its exposed points are the hull neighbours of `v`
(`exposedPair_iff_link`), these have nonzero and pairwise distinct directions and there are at
least three of them. For an angular rotation `rho` of the hull graph, the successor of a hull
dart spans with it a supporting plane of the point set (`hull_step`, from gift wrapping in the
link), and the hull graph is connected (`hull_connected`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## S1: vertex facts of an angular rotation system with positive corners -/

theorem ocorner_pos_of_ne {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (R : RotSys G) (x : V → E3) (hR : IsAngular R x)
    (hpos : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd))
    (e f : G.Dart) (hf : f.fst = e.fst) (hfe : f ≠ e) :
    0 < ocorner (x e.fst) (x e.snd) (x f.snd) :=
  lt_of_lt_of_le (hpos e) (hR e f hf hfe)

/-- Lemma B: the points lie in no closed hemisphere. -/
theorem not_closed_hemisphere {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hne : ∀ v, ∃ w, G.Adj v w) (R : RotSys G) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π) :
    ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫ :=
  fun e he => no_closed_hemisphere G x hx hinj hne
    (fun v t ht ht0 => exists_pos_of_corner_lt_pi R x hx hR hcorner v (hne v) t ht ht0) e he

/-! ## S2: the link of a vertex -/

section Link

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The stereographic image of `x z` from `x v`, a vector of the plane `(x v)⊥` pointing from
`x v` towards `x z`. -/
noncomputable def link (x : V → E3) (v z : V) : E3 := (1 - ⟪x v, x z⟫)⁻¹ • tdir (x v) (x z)

/-- The link of `v`: the stereographic images of the other points. -/
noncomputable def linkSet (x : V → E3) (v : V) : Finset E3 :=
  (Finset.univ.erase v).image (link x v)

omit [Fintype V] [DecidableEq V] in
theorem inner_lt_one_of_ne (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    {v z : V} (h : z ≠ v) : ⟪x v, x z⟫ < 1 := by
  have hle : ⟪x v, x z⟫ ≤ 1 := by
    calc
      ⟪x v, x z⟫ ≤ ‖x v‖ * ‖x z‖ := real_inner_le_norm (x v) (x z)
      _ = 1 * 1 := by rw [hx v, hx z]
      _ = 1 := by norm_num
  by_contra! heq
  have heq' : ⟪x v, x z⟫ = 1 := by linarith
  have hnorm0 : ‖x v - x z‖ = 0 := by
    have hsq : ‖x v - x z‖ ^ 2 = 0 := by
      calc
        ‖x v - x z‖ ^ 2 = ‖x v‖ ^ 2 - 2 * ⟪x v, x z⟫ + ‖x z‖ ^ 2 := by
          rw [norm_sub_sq_real (x v) (x z)]
        _ = 1 ^ 2 - 2 * 1 + 1 ^ 2 := by rw [hx v, hx z, heq']
        _ = 0 := by norm_num
    nlinarith
  have hsub0 : x v - x z = 0 := by
    rw [norm_eq_zero] at hnorm0
    exact hnorm0
  have heq_vec : x v = x z := sub_eq_zero.mp hsub0
  have heq_vz : v = z := hinj heq_vec
  exact h heq_vz.symm

omit [Fintype V] [DecidableEq V] in
theorem inner_link (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (v z : V) : ⟪x v, link x v z⟫ = 0 := by
  dsimp [link, tdir]
  have hnorm : ⟪x v, x v⟫ = 1 := by
    calc
      ⟪x v, x v⟫ = ‖x v‖ ^ 2 := real_inner_self_eq_norm_sq (x v)
      _ = 1 ^ 2 := by rw [hx v]
      _ = 1 := by norm_num
  rw [inner_smul_right]
  have hinner : ⟪x v, x z - ⟪x v, x z⟫ • (x v)⟫ = 0 := by
    calc
      ⟪x v, x z - ⟪x v, x z⟫ • (x v)⟫ = ⟪x v, x z⟫ - ⟪x v, ⟪x v, x z⟫ • (x v)⟫ := by rw [inner_sub_right]
      _ = ⟪x v, x z⟫ - (⟪x v, x z⟫ * ⟪x v, x v⟫) := by rw [inner_smul_right]
      _ = ⟪x v, x z⟫ - (⟪x v, x z⟫ * 1) := by rw [hnorm]
      _ = ⟪x v, x z⟫ - ⟪x v, x z⟫ := by simp
      _ = 0 := by simp
  rw [hinner, mul_zero]

omit [Fintype V] [DecidableEq V] in
theorem inner_link_eq (x : V → E3) (_hx : ∀ v, ‖x v‖ = 1) (v z : V) (e : E3)
    (he : ⟪x v, e⟫ = 0) : ⟪link x v z, e⟫ = (1 - ⟪x v, x z⟫)⁻¹ * ⟪x z, e⟫ := by
  unfold link tdir
  calc
    ⟪(1 - ⟪x v, x z⟫)⁻¹ • (x z - ⟪x v, x z⟫ • x v), e⟫
        = (1 - ⟪x v, x z⟫)⁻¹ * ⟪x z - ⟪x v, x z⟫ • x v, e⟫ := by
      rw [inner_smul_left]
      simp
    _ = (1 - ⟪x v, x z⟫)⁻¹ * (⟪x z, e⟫ - ⟪⟪x v, x z⟫ • x v, e⟫) := by
      rw [inner_sub_left]
    _ = (1 - ⟪x v, x z⟫)⁻¹ * (⟪x z, e⟫ - ⟪x v, x z⟫ * ⟪x v, e⟫) := by
      rw [inner_smul_left]
      simp
    _ = (1 - ⟪x v, x z⟫)⁻¹ * (⟪x z, e⟫ - ⟪x v, x z⟫ * 0) := by
      rw [he]
    _ = (1 - ⟪x v, x z⟫)⁻¹ * ⟪x z, e⟫ := by
      ring

omit [Fintype V] [DecidableEq V] in
theorem link_inj (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x) (v : V)
    {a b : V} (ha : a ≠ v) (hb : b ≠ v) (h : link x v a = link x v b) : a = b := by
  set t_a := ⟪x v, x a⟫ with ht_a
  set t_b := ⟪x v, x b⟫ with ht_b
  have ht_a_lt_one : t_a < 1 := inner_lt_one_of_ne x hx hinj ha
  have ht_b_lt_one : t_b < 1 := inner_lt_one_of_ne x hx hinj hb
  have ht_a_ne_one : t_a ≠ 1 := by linarith
  have ht_b_ne_one : t_b ≠ 1 := by linarith
  have h_pos_a : 0 < 1 - t_a := by linarith
  have h_pos_b : 0 < 1 - t_b := by linarith
  have h_ne_zero_a : 1 - t_a ≠ 0 := by linarith
  have h_ne_zero_b : 1 - t_b ≠ 0 := by linarith
  have h_norm_tdir_a_sq : ‖tdir (x v) (x a)‖ ^ 2 = 1 - t_a ^ 2 := by
    dsimp [tdir]
    rw [norm_sub_pow_two_real]
    have hx_v : ‖x v‖ = 1 := hx v
    have hx_a : ‖x a‖ = 1 := hx a
    have h_inner_self_v : ⟪x v, x v⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx_v]
      norm_num
    have h_inner_self_a : ⟪x a, x a⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx_a]
      norm_num
    have h_inner_comm : ⟪x a, x v⟫ = t_a := by
      rw [ht_a, real_inner_comm]
    simp [hx_v, hx_a, ht_a, h_inner_comm, inner_smul_right, norm_smul]
    ring_nf
  have h_norm_tdir_b_sq : ‖tdir (x v) (x b)‖ ^ 2 = 1 - t_b ^ 2 := by
    dsimp [tdir]
    rw [norm_sub_pow_two_real]
    have hx_v : ‖x v‖ = 1 := hx v
    have hx_b : ‖x b‖ = 1 := hx b
    have h_inner_self_v : ⟪x v, x v⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx_v]
      norm_num
    have h_inner_self_b : ⟪x b, x b⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx_b]
      norm_num
    have h_inner_comm : ⟪x b, x v⟫ = t_b := by
      rw [ht_b, real_inner_comm]
    simp [hx_v, hx_b, ht_b, h_inner_comm, inner_smul_right, norm_smul]
    ring_nf
  -- From h : link x v a = link x v b, take norm_sq of both sides
  have h_norm_sq_eq : ‖link x v a‖ ^ 2 = ‖link x v b‖ ^ 2 := by rw [h]
  -- Expand both sides to get equation relating t_a and t_b
  have h_eq : (1 + t_a) * (1 - t_b) = (1 + t_b) * (1 - t_a) := by
    dsimp [link] at h_norm_sq_eq
    -- h_norm_sq_eq : ‖(1 - ⟪x v, x a⟫)⁻¹ • tdir (x v) (x a)‖ ^ 2 = ‖(1 - ⟪x v, x b⟫)⁻¹ • tdir (x v) (x b)‖ ^ 2
    rw [← ht_a, ← ht_b] at h_norm_sq_eq
    -- h_norm_sq_eq : ‖(1 - t_a)⁻¹ • tdir (x v) (x a)‖ ^ 2 = ‖(1 - t_b)⁻¹ • tdir (x v) (x b)‖ ^ 2
    have h_norm_sq_a : ‖(1 - t_a)⁻¹ • tdir (x v) (x a)‖ ^ 2 = ((1 - t_a)⁻¹) ^ 2 * ‖tdir (x v) (x a)‖ ^ 2 := by
      calc
        ‖(1 - t_a)⁻¹ • tdir (x v) (x a)‖ ^ 2 = (‖(1 - t_a)⁻¹‖ * ‖tdir (x v) (x a)‖) ^ 2 := by rw [norm_smul]
        _ = ‖(1 - t_a)⁻¹‖ ^ 2 * ‖tdir (x v) (x a)‖ ^ 2 := by ring
        _ = |(1 - t_a)⁻¹| ^ 2 * ‖tdir (x v) (x a)‖ ^ 2 := by rw [Real.norm_eq_abs]
        _ = ((1 - t_a)⁻¹) ^ 2 * ‖tdir (x v) (x a)‖ ^ 2 := by
          rw [abs_of_pos (inv_pos_of_pos (by linarith : 0 < 1 - t_a))]
    have h_norm_sq_b : ‖(1 - t_b)⁻¹ • tdir (x v) (x b)‖ ^ 2 = ((1 - t_b)⁻¹) ^ 2 * ‖tdir (x v) (x b)‖ ^ 2 := by
      calc
        ‖(1 - t_b)⁻¹ • tdir (x v) (x b)‖ ^ 2 = (‖(1 - t_b)⁻¹‖ * ‖tdir (x v) (x b)‖) ^ 2 := by rw [norm_smul]
        _ = ‖(1 - t_b)⁻¹‖ ^ 2 * ‖tdir (x v) (x b)‖ ^ 2 := by ring
        _ = |(1 - t_b)⁻¹| ^ 2 * ‖tdir (x v) (x b)‖ ^ 2 := by rw [Real.norm_eq_abs]
        _ = ((1 - t_b)⁻¹) ^ 2 * ‖tdir (x v) (x b)‖ ^ 2 := by
          rw [abs_of_pos (inv_pos_of_pos (by linarith : 0 < 1 - t_b))]
    rw [h_norm_sq_a, h_norm_sq_b] at h_norm_sq_eq
    rw [h_norm_tdir_a_sq, h_norm_tdir_b_sq] at h_norm_sq_eq
    -- h_norm_sq_eq : ((1 - t_a)⁻¹) ^ 2 * (1 - t_a ^ 2) = ((1 - t_b)⁻¹) ^ 2 * (1 - t_b ^ 2)
    -- Multiply both sides by (1 - t_a)^2 * (1 - t_b)^2
    field_simp [h_ne_zero_a, h_ne_zero_b] at h_norm_sq_eq
    -- h_norm_sq_eq : (1 - t_a ^ 2) * (1 - t_b) ^ 2 = (1 - t_a) ^ 2 * (1 - t_b ^ 2)
    -- Factor and cancel
    have h_eq' : (1 + t_a) * (1 - t_b) = (1 + t_b) * (1 - t_a) := by
      have h_factor_a : 1 - t_a ^ 2 = (1 - t_a) * (1 + t_a) := by ring
      have h_factor_b : 1 - t_b ^ 2 = (1 - t_b) * (1 + t_b) := by ring
      rw [h_factor_a, h_factor_b] at h_norm_sq_eq
      -- h_norm_sq_eq : ((1 - t_a) * (1 + t_a)) * (1 - t_b) ^ 2 = (1 - t_a) ^ 2 * ((1 - t_b) * (1 + t_b))
      -- Rearrange to factor out (1 - t_a) * (1 - t_b)
      have h_factor : ((1 - t_a) * (1 + t_a)) * (1 - t_b) ^ 2 - (1 - t_a) ^ 2 * ((1 - t_b) * (1 + t_b)) = 0 := by
        linarith
      have h_factor_id : ((1 - t_a) * (1 + t_a)) * (1 - t_b) ^ 2 - (1 - t_a) ^ 2 * ((1 - t_b) * (1 + t_b)) = (1 - t_a) * (1 - t_b) * ((1 + t_a) * (1 - t_b) - (1 - t_a) * (1 + t_b)) := by
        ring
      rw [h_factor_id] at h_factor
      -- h_factor : (1 - t_a) * (1 - t_b) * ((1 + t_a) * (1 - t_b) - (1 - t_a) * (1 + t_b)) = 0
      have h_zero : (1 + t_a) * (1 - t_b) - (1 - t_a) * (1 + t_b) = 0 := by
        rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h1 | h2
        · -- h1 : (1 - t_a) * (1 - t_b) = 0
          rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h3 | h4
          · -- h3 : 1 - t_a = 0
            exact absurd h3 h_ne_zero_a
          · -- h4 : 1 - t_b = 0
            exact absurd h4 h_ne_zero_b
        · -- h2 : (1 + t_a) * (1 - t_b) - (1 - t_a) * (1 + t_b) = 0
          exact h2
      linarith
    exact h_eq'
  -- From h_eq, deduce t_a = t_b
  have ht_eq : t_a = t_b := by
    nlinarith
  -- Now substitute t_a = t_b into h
  have h_tdir_eq : tdir (x v) (x a) = tdir (x v) (x b) := by
    dsimp [link] at h
    rw [← ht_a, ← ht_b] at h
    -- h : (1 - t_a)⁻¹ • tdir (x v) (x a) = (1 - t_b)⁻¹ • tdir (x v) (x b)
    rw [ht_eq] at h
    -- h : (1 - t_b)⁻¹ • tdir (x v) (x a) = (1 - t_b)⁻¹ • tdir (x v) (x b)
    -- Multiply both sides by (1 - t_b)
    have h_mul := congrArg (fun w => (1 - t_b) • w) h
    -- h_mul : (1 - t_b) • ((1 - t_b)⁻¹ • tdir (x v) (x a)) = (1 - t_b) • ((1 - t_b)⁻¹ • tdir (x v) (x b))
    simp [smul_smul] at h_mul
    -- h_mul : ((1 - t_b) * (1 - t_b)⁻¹) • tdir (x v) (x a) = ((1 - t_b) * (1 - t_b)⁻¹) • tdir (x v) (x b)
    have h_inv_mul : (1 - t_b) * (1 - t_b)⁻¹ = 1 := by field_simp [h_ne_zero_b]
    rw [h_inv_mul] at h_mul
    simp at h_mul
    exact h_mul
  -- Now from h_tdir_eq, expand tdir
  have hxa_eq_xb : x a = x b := by
    dsimp [tdir] at h_tdir_eq
    -- h_tdir_eq : x a - ⟪x v, x a⟫ • x v = x b - ⟪x v, x b⟫ • x v
    rw [← ht_a, ← ht_b] at h_tdir_eq
    -- h_tdir_eq : x a - t_a • x v = x b - t_b • x v
    rw [ht_eq] at h_tdir_eq
    -- h_tdir_eq : x a - t_b • x v = x b - t_b • x v
    -- Rewrite as x a + (-(t_b • x v)) = x b + (-(t_b • x v))
    have h_add : x a + (-(t_b • x v)) = x b + (-(t_b • x v)) := by
      simpa [sub_eq_add_neg] using h_tdir_eq
    exact add_right_cancel h_add
  -- Finally, apply hinj
  exact hinj hxa_eq_xb

omit [Fintype V] [DecidableEq V] in
theorem link_transfer (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    {v z : V} (hz : z ≠ v) (N : E3) :
    ⟪x z, N⟫ - ⟪x v, N⟫ = (1 - ⟪x v, x z⟫) * (⟪link x v z, N⟫ - ⟪x v, N⟫) := by
  have h_inner_ne_one : ⟪x v, x z⟫ ≠ 1 := by
    intro h_eq
    have h_eq_vec : x v = x z := by
      have h_norm_sq_zero : ‖x v - x z‖ ^ 2 = (0 : ℝ) := by
        calc
          ‖x v - x z‖ ^ 2 = ‖x v‖ ^ 2 - 2 * RCLike.re (inner ℝ (x v) (x z)) + ‖x z‖ ^ 2 := by
            rw [norm_sub_sq (𝕜 := ℝ)]
          _ = ‖x v‖ ^ 2 - 2 * RCLike.re ((1 : ℝ)) + ‖x z‖ ^ 2 := by rw [h_eq]
          _ = ‖x v‖ ^ 2 - 2 * (1 : ℝ) + ‖x z‖ ^ 2 := by simp
          _ = ((1 : ℝ) ^ 2) - 2 * (1 : ℝ) + ((1 : ℝ) ^ 2) := by simp [hx v, hx z]
          _ = (0 : ℝ) := by norm_num
      have h_norm_zero : ‖x v - x z‖ = 0 := by
        have h_nonneg : 0 ≤ ‖x v - x z‖ := norm_nonneg _
        nlinarith
      have h_sub_zero : x v - x z = 0 := norm_eq_zero.mp h_norm_zero
      exact eq_of_sub_eq_zero h_sub_zero
    exact hz (hinj h_eq_vec.symm)
  calc
    ⟪x z, N⟫ - ⟪x v, N⟫ = (1 - ⟪x v, x z⟫) * (⟪(1 - ⟪x v, x z⟫)⁻¹ • tdir (x v) (x z), N⟫ - ⟪x v, N⟫) := by
      apply stereo_identity (x v) (x z) N h_inner_ne_one
    _ = (1 - ⟪x v, x z⟫) * (⟪link x v z, N⟫ - ⟪x v, N⟫) := by
      simp [link]

omit [Fintype V] [DecidableEq V] in
theorem det_link (x : V → E3) (v a b : V) :
    ⟪cross (x v) (link x v a), link x v b⟫ =
      (1 - ⟪x v, x a⟫)⁻¹ * (1 - ⟪x v, x b⟫)⁻¹ * ⟪cross (x v) (x a), x b⟫ := by
  unfold link tdir
  simp [cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem mem_linkSet (x : V → E3) (v : V) (y : E3) :
    y ∈ linkSet x v ↔ ∃ z, z ≠ v ∧ link x v z = y := by
  simp [linkSet, Finset.mem_image, Finset.mem_erase]

/-- C.1: hull neighbours of `v` are the exposed points of its link. -/
theorem exposedPair_iff_link (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    {v z : V} (hz : z ≠ v) :
    ExposedPair x v z ↔
      ∃ n : E3, ∀ y ∈ linkSet x v, y ≠ link x v z → ⟪y, n⟫ < ⟪link x v z, n⟫ := by
  constructor
  · intro h
    rcases h with ⟨hvz_ne, N, hN_eq, hN_lt⟩
    refine ⟨N, ?_⟩
    intro y hy hy_ne
    rcases ((mem_linkSet x v y).mp hy) with ⟨w, hw_ne, hw_eq⟩
    have hwz_ne : w ≠ z := by
      intro heq
      apply hy_ne
      calc
        y = link x v w := hw_eq.symm
        _ = link x v z := by rw [heq]
    have h_lt : ⟪x w, N⟫ < ⟪x v, N⟫ := hN_lt w hw_ne hwz_ne
    have h_transfer := link_transfer x hx hinj hw_ne N
    have h_inner_lt : ⟪x v, x w⟫ < 1 := inner_lt_one_of_ne x hx hinj hw_ne
    have h_pos : 0 < 1 - ⟪x v, x w⟫ := by linarith
    have h_diff_neg : ⟪link x v w, N⟫ - ⟪x v, N⟫ < 0 := by
      have h_lhs : ⟪x w, N⟫ - ⟪x v, N⟫ < 0 := by linarith
      nlinarith
    have h_link_lt : ⟪link x v w, N⟫ < ⟪x v, N⟫ := by linarith
    have h_inner_lt_z : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj hz
    have h_pos_z : 0 < 1 - ⟪x v, x z⟫ := by linarith
    have h_link_eq : ⟪link x v z, N⟫ = ⟪x v, N⟫ := by
      have h_transfer_z := link_transfer x hx hinj hz N
      have h_zero : ⟪x z, N⟫ - ⟪x v, N⟫ = 0 := by linarith
      nlinarith
    calc
      ⟪y, N⟫ = ⟪link x v w, N⟫ := by rw [hw_eq]
      _ < ⟪x v, N⟫ := h_link_lt
      _ = ⟪link x v z, N⟫ := by rw [h_link_eq]
  · intro h
    rcases h with ⟨n, hn⟩
    have hvz_ne : v ≠ z := Ne.symm hz
    set k := ⟪link x v z, n⟫ with hk_def
    set N := n + (k - ⟪x v, n⟫) • x v with hN_def
    have hNv : ⟪x v, N⟫ = k := by
      dsimp [N]
      calc
        ⟪x v, n + (k - ⟪x v, n⟫) • x v⟫ = ⟪x v, n⟫ + ⟪x v, (k - ⟪x v, n⟫) • x v⟫ := by
          rw [inner_add_right]
        _ = ⟪x v, n⟫ + (k - ⟪x v, n⟫) * ⟪x v, x v⟫ := by rw [inner_smul_right]
        _ = ⟪x v, n⟫ + (k - ⟪x v, n⟫) * (‖x v‖ ^ 2) := by
          have htemp : ⟪x v, x v⟫ = ‖x v‖ ^ 2 := real_inner_self_eq_norm_sq (x v)
          rw [htemp]
        _ = ⟪x v, n⟫ + (k - ⟪x v, n⟫) * (1 ^ 2) := by rw [hx v]
        _ = ⟪x v, n⟫ + (k - ⟪x v, n⟫) * 1 := by norm_num
        _ = ⟪x v, n⟫ + (k - ⟪x v, n⟫) := by ring
        _ = k := by ring
    have hNz : ⟪x z, N⟫ = k := by
      have h_transfer := link_transfer x hx hinj hz N
      have h_transfer_z : ⟪x z, N⟫ - ⟪x v, N⟫ = (1 - ⟪x v, x z⟫) * (⟪link x v z, N⟫ - ⟪x v, N⟫) := h_transfer
      rw [hNv] at h_transfer_z
      have h_link_N : ⟪link x v z, N⟫ = k := by
        dsimp [N]
        calc
          ⟪link x v z, n + (k - ⟪x v, n⟫) • x v⟫ = ⟪link x v z, n⟫ + ⟪link x v z, (k - ⟪x v, n⟫) • x v⟫ := by
            rw [inner_add_right]
          _ = ⟪link x v z, n⟫ + (k - ⟪x v, n⟫) * ⟪link x v z, x v⟫ := by rw [inner_smul_right]
          _ = ⟪link x v z, n⟫ + (k - ⟪x v, n⟫) * 0 := by
            rw [← real_inner_comm (link x v z) (x v), inner_link x hx v z]
          _ = ⟪link x v z, n⟫ := by ring
          _ = k := hk_def
      rw [h_link_N] at h_transfer_z
      have h_factor_pos : 0 < 1 - ⟪x v, x z⟫ := by
        have h_lt : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj hz
        linarith
      nlinarith
    have hN_eq : ⟪x v, N⟫ = ⟪x z, N⟫ := by rw [hNv, hNz]
    refine ⟨hvz_ne, N, hN_eq, ?_⟩
    intro w hw_ne hwz_ne
    have h_transfer := link_transfer x hx hinj hw_ne N
    rw [hNv] at h_transfer
    have h_link_N : ⟪link x v w, N⟫ = ⟪link x v w, n⟫ := by
      dsimp [N]
      calc
        ⟪link x v w, n + (k - ⟪x v, n⟫) • x v⟫ = ⟪link x v w, n⟫ + ⟪link x v w, (k - ⟪x v, n⟫) • x v⟫ := by
          rw [inner_add_right]
        _ = ⟪link x v w, n⟫ + (k - ⟪x v, n⟫) * ⟪link x v w, x v⟫ := by rw [inner_smul_right]
        _ = ⟪link x v w, n⟫ + (k - ⟪x v, n⟫) * 0 := by
          rw [← real_inner_comm (link x v w) (x v), inner_link x hx v w]
        _ = ⟪link x v w, n⟫ := by ring
    rw [h_link_N] at h_transfer
    have h_factor_pos : 0 < 1 - ⟪x v, x w⟫ := by
      have h_lt : ⟪x v, x w⟫ < 1 := inner_lt_one_of_ne x hx hinj hw_ne
      linarith
    have h_link_lt : ⟪link x v w, n⟫ < k := by
      have hmem : link x v w ∈ linkSet x v := by
        apply (mem_linkSet x v (link x v w)).mpr
        exact ⟨w, hw_ne, rfl⟩
      have h_ne : link x v w ≠ link x v z := by
        intro heq
        apply hwz_ne
        exact link_inj x hx hinj v hw_ne hz heq
      have h_lt_n := hn (link x v w) hmem h_ne
      rw [hk_def] at h_lt_n
      exact h_lt_n
    have h_diff_neg : ⟪x w, N⟫ - k < 0 := by
      nlinarith
    linarith

/-- C.2: `0` lies strictly inside the link. -/
theorem link_inside (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (v : V) :
    ∀ e : E3, ⟪x v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ linkSet x v, 0 < ⟪y, e⟫ := by
  intro e he he0
  rcases hB e he0 with ⟨a, ha⟩
  have ha_ne_v : a ≠ v := by
    intro heq
    rw [heq] at ha
    rw [he] at ha
    linarith
  refine ⟨link x v a, ((mem_linkSet x v (link x v a)).mpr ⟨a, ha_ne_v, rfl⟩), ?_⟩
  rw [inner_link_eq x hx v a e he]
  have hinner_lt_one : ⟪x v, x a⟫ < 1 := inner_lt_one_of_ne x hx hinj ha_ne_v
  have hpos' : 0 < 1 - ⟪x v, x a⟫ := by linarith
  have hpos_inv : 0 < (1 - ⟪x v, x a⟫)⁻¹ := inv_pos.mpr hpos'
  exact mul_pos hpos_inv ha

end Link

/-! ## Exposed points of a finite planar set with `0` strictly inside -/

/-- An exposing functional is positive at the exposed point. -/
theorem exposed_inner_pos (v : E3) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫) (p n : E3) (_hp : p ∈ P)
    (hpn : ∀ y ∈ P, y ≠ p → ⟪y, n⟫ < ⟪p, n⟫) : 0 < ⟪p, n⟫ := by
  by_contra! hle
  -- hle : ⟪p, n⟫ ≤ 0
  set n' := n - (⟪v, n⟫ / ⟪v, v⟫) • v with hn'_def
  have hvn' : ⟪v, n'⟫ = 0 := by
    dsimp [n']
    rw [inner_sub_right, inner_smul_right]
    by_cases hv0 : ⟪v, v⟫ = 0
    · have hv0' : v = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hv0
      simp [hv0']
    · field_simp [hv0]
      ring
  have hyn'_eq_yn : ∀ y ∈ P, ⟪y, n'⟫ = ⟪y, n⟫ := by
    intro y hy
    dsimp [n']
    rw [inner_sub_right, inner_smul_right, real_inner_comm v y, hP y hy, mul_zero, sub_zero]
  by_cases hn'0 : n' = 0
  · -- then n is parallel to v, and all y ∈ P have ⟪y, n⟫ = 0
    have hyn0 : ∀ y ∈ P, ⟪y, n⟫ = 0 := by
      intro y hy
      rw [← hyn'_eq_yn y hy, hn'0, inner_zero_right]
    -- hpn forces every y ∈ P to equal p
    have hP_singleton : ∀ y ∈ P, y = p := by
      intro y hy
      by_contra! hne
      have hlt := hpn y hy hne
      have heq := hyn0 y hy
      linarith
    -- find a nonzero vector e orthogonal to v
    have h_exists_e : ∃ e : E3, e ≠ 0 ∧ ⟪v, e⟫ = 0 := by
      by_cases hv0 : v = 0
      · refine ⟨(EuclideanSpace.basisFun (Fin 3) ℝ) 0, ?_, ?_⟩
        · exact ((EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.ne_zero 0)
        · simp [hv0]
      · let b := EuclideanSpace.basisFun (Fin 3) ℝ
        let e1 := b 0
        let e2 := b 1
        have he1_ne_zero : e1 ≠ 0 := b.orthonormal.ne_zero 0
        have he2_ne_zero : e2 ≠ 0 := b.orthonormal.ne_zero 1
        by_cases h_v_e1 : ⟪v, e1⟫ ≠ 0
        · -- e = e2 - (⟪v, e2⟫ / ⟪v, e1⟫) • e1 is nonzero and orthogonal to v
          set e := e2 - (⟪v, e2⟫ / ⟪v, e1⟫) • e1 with he_def
          have h_ortho : ⟪v, e⟫ = 0 := by
            dsimp [e]
            rw [inner_sub_right, inner_smul_right]
            field_simp [h_v_e1]
            ring
          have h_ne_zero : e ≠ 0 := by
            intro hzero
            have h_inner := congrArg (fun x => ⟪x, e1⟫) hzero
            dsimp [e] at h_inner
            rw [inner_sub_left, real_inner_smul_left] at h_inner
            have h_e1_e1 : ⟪e1, e1⟫ = 1 := b.inner_eq_one 0
            have h_e2_e1 : ⟪e2, e1⟫ = 0 := by
              rw [b.inner_eq_ite 1 0]
              simp
            rw [h_e2_e1, h_e1_e1] at h_inner
            -- h_inner : 0 - (⟪v, e2⟫ / ⟪v, e1⟫) * 1 = ⟪0, e1⟫
            rw [inner_zero_left] at h_inner
            -- h_inner : 0 - (⟪v, e2⟫ / ⟪v, e1⟫) * 1 = 0
            have h_div_zero : ⟪v, e2⟫ / ⟪v, e1⟫ = 0 := by
              nlinarith
            have h_v_e2_zero : ⟪v, e2⟫ = 0 := by
              rcases div_eq_zero_iff.mp h_div_zero with h | h
              · exact h
              · exfalso; exact h_v_e1 h
            -- Then e = e2, which is nonzero
            have h_eq_e2 : e = e2 := by
              dsimp [e]
              rw [h_div_zero, zero_smul, sub_zero]
            rw [h_eq_e2] at hzero
            exact he2_ne_zero hzero
          exact ⟨e, h_ne_zero, h_ortho⟩
        · -- ⟪v, e1⟫ = 0, so e1 itself works
          refine ⟨e1, he1_ne_zero, ?_⟩
          simpa using h_v_e1
    rcases h_exists_e with ⟨e, he0, hve⟩
    -- hin gives 0 < ⟪p, e⟫ (since e ≠ 0 and ⟪v, e⟫ = 0)
    have hpos_e := hin e hve he0
    rcases hpos_e with ⟨y, hy, hpos⟩
    have hy_eq_p : y = p := hP_singleton y hy
    rw [hy_eq_p] at hpos
    -- hin also gives 0 < ⟪p, -e⟫ = -⟪p, e⟫, contradiction
    have hve_neg : ⟪v, -e⟫ = 0 := by
      simpa [inner_neg_right] using congrArg Neg.neg hve
    have hneg_ne_zero : -e ≠ 0 := by
      intro hzero; apply he0; simpa using neg_eq_zero.mp hzero
    have hpos_neg := hin (-e) hve_neg hneg_ne_zero
    rcases hpos_neg with ⟨z, hz, hpos_neg'⟩
    have hz_eq_p : z = p := hP_singleton z hz
    rw [hz_eq_p] at hpos_neg'
    have h_neg : ⟪p, -e⟫ = -⟪p, e⟫ := by simp
    rw [h_neg] at hpos_neg'
    linarith
  · -- n' ≠ 0, use hin to get a contradiction
    have hpos := hin n' hvn' hn'0
    rcases hpos with ⟨y, hy, hpos⟩
    have hyn_le : ⟪y, n⟫ ≤ 0 := by
      by_cases hy_eq_p : y = p
      · rw [hy_eq_p]; exact hle
      · have hlt := hpn y hy hy_eq_p
        linarith
    rw [hyn'_eq_yn y hy] at hpos
    linarith

/-- Two exposed points on one ray from `0` coincide. -/
theorem exposed_ray_eq (v : E3) (P : Finset E3) (hP : ∀ y ∈ P, ⟪v, y⟫ = 0)
    (hin : ∀ e : E3, ⟪v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ P, 0 < ⟪y, e⟫) (p q : E3) (hp : p ∈ P)
    (hq : q ∈ P) (hpx : ∃ n : E3, ∀ y ∈ P, y ≠ p → ⟪y, n⟫ < ⟪p, n⟫)
    (hqx : ∃ n : E3, ∀ y ∈ P, y ≠ q → ⟪y, n⟫ < ⟪q, n⟫) (t : ℝ) (ht : 0 < t)
    (hpq : q = t • p) : q = p := by
  rcases hpx with ⟨n, hn⟩
  rcases hqx with ⟨m, hm⟩
  have hp_pos : 0 < ⟪p, n⟫ := exposed_inner_pos v P hP hin p n hp hn
  have hq_pos : 0 < ⟪q, m⟫ := exposed_inner_pos v P hP hin q m hq hm
  by_cases hpq_eq : p = q
  · exact hpq_eq.symm
  · have ht_ne_one : t ≠ 1 := by
      intro heq
      apply hpq_eq
      calc
        p = (1 : ℝ) • p := by simp
        _ = t • p := by rw [heq]
        _ = q := hpq.symm
    by_cases hlt : t < 1
    · have h_lt : ⟪p, m⟫ < ⟪q, m⟫ := hm p hp hpq_eq
      have hq_inner : ⟪q, m⟫ = t * ⟪p, m⟫ := by
        rw [hpq, inner_smul_left]
        simp
      rw [hq_inner] at h_lt
      have hp_pos_m : 0 < ⟪p, m⟫ := by
        have : 0 < t * ⟪p, m⟫ := by
          rw [← hq_inner]
          exact hq_pos
        exact pos_of_mul_pos_right this ht.le
      nlinarith
    · have hlt' : 1 < t := by
        by_contra! hle
        apply ht_ne_one
        linarith
      have h_lt : ⟪q, n⟫ < ⟪p, n⟫ := hn q hq (Ne.symm hpq_eq)
      have hq_inner : ⟪q, n⟫ = t * ⟪p, n⟫ := by
        rw [hpq, inner_smul_left]
        simp
      rw [hq_inner] at h_lt
      nlinarith

/-! ## C.3 and C.4: directions and degrees of the hull graph -/

section Hull

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem hull_tdir_ne_zero (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) {v a : V} (h : ExposedPair x v a) :
    tdir (x v) (x a) ≠ 0 := by
  rcases h with ⟨hne, N, hN_eq, hN_lt⟩
  by_contra hzero
  have hzero' : x a - ⟪x v, x a⟫ • (x v) = 0 := hzero
  have heq : x a = ⟪x v, x a⟫ • (x v) := eq_of_sub_eq_zero hzero'
  set c := ⟪x v, x a⟫ with hc_def
  have hxa_norm_sq : ‖x a‖ ^ 2 = c ^ 2 := by
    calc
      ‖x a‖ ^ 2 = ⟪x a, x a⟫ := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪c • (x v), c • (x v)⟫ := by rw [heq]
      _ = (starRingEnd ℝ c) * ⟪x v, c • (x v)⟫ := by rw [inner_smul_left]
      _ = (starRingEnd ℝ c) * (c * ⟪x v, x v⟫) := by rw [inner_smul_right]
      _ = c * (c * ⟪x v, x v⟫) := by simp
      _ = c ^ 2 * ⟪x v, x v⟫ := by ring
      _ = c ^ 2 * ‖x v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = c ^ 2 * (1 ^ 2) := by rw [hx v]
      _ = c ^ 2 := by norm_num
  have hc_sq_eq_one : c ^ 2 = 1 := by
    rw [← hxa_norm_sq, hx a]
    norm_num
  have hc_cases : c = 1 ∨ c = -1 := by
    have h_factor : (c - 1) * (c + 1) = 0 := by
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with (h1 | h2)
    · left; linarith
    · right; linarith
  rcases hc_cases with (hc | hc)
  · -- c = 1, so x a = x v, contradicting hne
    have hxa_eq_xv : x a = x v := by
      rw [heq, hc, one_smul]
    have ha_eq_v : a = v := hinj hxa_eq_xv
    exact hne ha_eq_v.symm
  · -- c = -1, so x a = -x v
    have hxa_eq_neg_xv : x a = -x v := by
      rw [heq, hc, neg_one_smul]
    have hN_inner_zero : ⟪x v, N⟫ = 0 := by
      rw [hxa_eq_neg_xv] at hN_eq
      rw [inner_neg_left] at hN_eq
      linarith
    by_cases hNzero : N = 0
    · -- N = 0: then ExposedPair gives no constraint beyond v ≠ a,
      -- but hB with an orthogonal vector yields a contradiction
      have h_all_eq : ∀ z : V, z = v ∨ z = a := by
        intro z
        by_cases hz_v : z = v
        · left; exact hz_v
        · by_cases hz_a : z = a
          · right; exact hz_a
          · have h_lt := hN_lt z hz_v hz_a
            rw [hNzero] at h_lt
            simp at h_lt
      -- Get a nonzero vector orthogonal to x v
      have h_orth := exists_ne_zero_dotProduct_eq_zero (x v).ofLp
      rcases h_orth with ⟨b, hb_ne_zero, hb_dot⟩
      set e : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm b with he_def
      have he_ne_zero : e ≠ 0 := by
        rw [he_def]
        intro hzero_e
        apply hb_ne_zero
        apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective
        rw [hzero_e, map_zero]
      have h_orth_inner : ⟪e, x v⟫ = 0 := by
        rw [he_def]
        calc
          ⟪(EuclideanSpace.equiv (Fin 3) ℝ).symm b, x v⟫ = b ⬝ᵥ (x v).ofLp := by
            simp [PiLp.inner_apply, dotProduct, mul_comm, EuclideanSpace.equiv]
          _ = 0 := hb_dot
      rcases hB e he_ne_zero with ⟨a', ha'⟩
      rcases h_all_eq a' with (ha'_eq_v | ha'_eq_a)
      · rw [ha'_eq_v] at ha'
        -- ha' : 0 < ⟪x v, e⟫
        have : ⟪x v, e⟫ = 0 := by
          rw [real_inner_comm, h_orth_inner]
        rw [this] at ha'
        linarith
      · rw [ha'_eq_a] at ha'
        -- ha' : 0 < ⟪x a, e⟫ = ⟪-x v, e⟫ = -⟪x v, e⟫
        rw [hxa_eq_neg_xv] at ha'
        rw [inner_neg_left] at ha'
        have : ⟪x v, e⟫ = 0 := by
          rw [real_inner_comm, h_orth_inner]
        rw [this] at ha'
        linarith
    · -- N ≠ 0, use hB and hN_lt
      rcases hB N hNzero with ⟨a', ha'⟩
      by_cases ha'_eq_v : a' = v
      · rw [ha'_eq_v] at ha'
        rw [hN_inner_zero] at ha'
        linarith
      · by_cases ha'_eq_a : a' = a
        · rw [ha'_eq_a] at ha'
          -- ha' : 0 < ⟪x a, N⟫
          rw [← hN_eq] at ha'
          rw [hN_inner_zero] at ha'
          linarith
        · have h_lt := hN_lt a' ha'_eq_v ha'_eq_a
          rw [hN_inner_zero] at h_lt
          linarith

theorem hull_ocorner_pos (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) {v a b : V} (ha : ExposedPair x v a)
    (hb : ExposedPair x v b) (hab : a ≠ b) : 0 < ocorner (x v) (x a) (x b) := by
  have hv_norm : ‖x v‖ = 1 := hx v
  have ha_ne_v : a ≠ v := Ne.symm ha.1
  have hb_ne_v : b ≠ v := Ne.symm hb.1
  have hpos_inner_a : ⟪x v, x a⟫ < 1 := inner_lt_one_of_ne x hx hinj ha_ne_v
  have hpos_inner_b : ⟪x v, x b⟫ < 1 := inner_lt_one_of_ne x hx hinj hb_ne_v
  have htdir_ne_zero_a : tdir (x v) (x a) ≠ 0 := hull_tdir_ne_zero x hx hinj hB ha
  have htdir_ne_zero_b : tdir (x v) (x b) ≠ 0 := hull_tdir_ne_zero x hx hinj hB hb
  have h_ocorner_nonneg : 0 ≤ ocorner (x v) (x a) (x b) := by
    have hmem := toIcoMod_mem_Ico two_pi_pos 0
      (Complex.arg ⟨⟪tdir (x v) (x a), tdir (x v) (x b)⟫, ⟪x v, cross (tdir (x v) (x a)) (tdir (x v) (x b))⟫⟩)
    exact hmem.1
  by_contra! hzero
  have hzero' : ocorner (x v) (x a) (x b) = 0 := by linarith
  have hsame : SameRay ℝ (tdir (x v) (x a)) (tdir (x v) (x b)) :=
    sameRay_of_ocorner_eq_zero (x v) (x a) (x b) hv_norm hzero'
  rcases SameRay.exists_pos_left hsame htdir_ne_zero_a htdir_ne_zero_b with ⟨r, hrpos, heq⟩
  have hpos_denom_a : 0 < 1 - ⟪x v, x a⟫ := by linarith
  have hpos_denom_b : 0 < 1 - ⟪x v, x b⟫ := by linarith
  have h_tdir_eq : tdir (x v) (x a) = (1 - ⟪x v, x a⟫) • link x v a := by
    dsimp [link]
    rw [smul_smul]
    field_simp [hpos_denom_a.ne.symm]
    simp
  have hlink_eq : link x v b = ((r * (1 - ⟪x v, x a⟫)) / (1 - ⟪x v, x b⟫)) • link x v a := by
    calc
      link x v b = (1 - ⟪x v, x b⟫)⁻¹ • tdir (x v) (x b) := rfl
      _ = (1 - ⟪x v, x b⟫)⁻¹ • (r • tdir (x v) (x a)) := by rw [heq]
      _ = ((1 - ⟪x v, x b⟫)⁻¹ * r) • tdir (x v) (x a) := by rw [smul_smul]
      _ = (r * (1 - ⟪x v, x b⟫)⁻¹) • tdir (x v) (x a) := by ring
      _ = (r * (1 - ⟪x v, x b⟫)⁻¹) • ((1 - ⟪x v, x a⟫) • link x v a) := by rw [h_tdir_eq]
      _ = ((r * (1 - ⟪x v, x b⟫)⁻¹) * (1 - ⟪x v, x a⟫)) • link x v a := by rw [smul_smul]
      _ = ((r * (1 - ⟪x v, x a⟫)) / (1 - ⟪x v, x b⟫)) • link x v a := by ring
  have hs_pos : 0 < (r * (1 - ⟪x v, x a⟫)) / (1 - ⟪x v, x b⟫) := by
    refine div_pos (mul_pos hrpos hpos_denom_a) hpos_denom_b
  have hmem_link_a : link x v a ∈ linkSet x v := by
    rw [mem_linkSet]
    exact ⟨a, ha_ne_v, rfl⟩
  have hmem_link_b : link x v b ∈ linkSet x v := by
    rw [mem_linkSet]
    exact ⟨b, hb_ne_v, rfl⟩
  have hP : ∀ y ∈ linkSet x v, ⟪x v, y⟫ = 0 := by
    intro y hy
    rcases (mem_linkSet x v y).mp hy with ⟨z, hz_ne_v, hy_eq⟩
    rw [← hy_eq]
    exact inner_link x hx v z
  have hin : ∀ e : E3, ⟪x v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ linkSet x v, 0 < ⟪y, e⟫ :=
    link_inside x hx hinj hB v
  rcases ((exposedPair_iff_link x hx hinj ha_ne_v).mp ha) with ⟨na, hna⟩
  rcases ((exposedPair_iff_link x hx hinj hb_ne_v).mp hb) with ⟨nb, hnb⟩
  have h_ray_eq : link x v b = link x v a :=
    exposed_ray_eq (x v) (linkSet x v) hP hin (link x v a) (link x v b)
      hmem_link_a hmem_link_b ⟨na, hna⟩ ⟨nb, hnb⟩
      ((r * (1 - ⟪x v, x a⟫)) / (1 - ⟪x v, x b⟫)) hs_pos hlink_eq
  have hab_eq : a = b := link_inj x hx hinj v ha_ne_v hb_ne_v h_ray_eq.symm
  exact hab hab_eq

theorem hull_three_le_degree (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (v : V) : 3 ≤ (hullGraph x).degree v := by
  have hP : ∀ y ∈ linkSet x v, ⟪x v, y⟫ = 0 := by
    intro y hy
    rcases (mem_linkSet x v y).mp hy with ⟨z, hz_ne, hz_eq⟩
    rw [← hz_eq]
    exact inner_link x hx v z
  have hin' : ∀ e : E3, ⟪x v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ linkSet x v, 0 < ⟪y, e⟫ := by
    intro e he_zero he_ne
    rcases link_inside x hx hinj hB v e he_zero he_ne with ⟨y, hy, hy_pos⟩
    exact ⟨y, hy, hy_pos⟩
  rcases exists_three_exposed (x v) (linkSet x v) hP hin' with
    ⟨a, haP, b, hbP, c, hcP, ha_ne_b, ha_ne_c, hb_ne_c, h_exposed⟩
  rcases (mem_linkSet x v a).mp haP with ⟨za, hza_ne, hza_eq⟩
  rcases (mem_linkSet x v b).mp hbP with ⟨zb, hzb_ne, hzb_eq⟩
  rcases (mem_linkSet x v c).mp hcP with ⟨zc, hzc_ne, hzc_eq⟩
  have hza_ne_zb : za ≠ zb := by
    intro h_eq
    apply ha_ne_b
    calc
      a = link x v za := (hza_eq.symm)
      _ = link x v zb := by rw [h_eq]
      _ = b := hzb_eq
  have hza_ne_zc : za ≠ zc := by
    intro h_eq
    apply ha_ne_c
    calc
      a = link x v za := (hza_eq.symm)
      _ = link x v zc := by rw [h_eq]
      _ = c := hzc_eq
  have hzb_ne_zc : zb ≠ zc := by
    intro h_eq
    apply hb_ne_c
    calc
      b = link x v zb := (hzb_eq.symm)
      _ = link x v zc := by rw [h_eq]
      _ = c := hzc_eq
  have hza_adj : (hullGraph x).Adj v za := by
    rw [hullGraph_adj]
    rw [exposedPair_iff_link x hx hinj hza_ne]
    rw [hza_eq]
    exact h_exposed a (by simp)
  have hzb_adj : (hullGraph x).Adj v zb := by
    rw [hullGraph_adj]
    rw [exposedPair_iff_link x hx hinj hzb_ne]
    rw [hzb_eq]
    exact h_exposed b (by simp)
  have hzc_adj : (hullGraph x).Adj v zc := by
    rw [hullGraph_adj]
    rw [exposedPair_iff_link x hx hinj hzc_ne]
    rw [hzc_eq]
    exact h_exposed c (by simp)
  have hza_mem : za ∈ (hullGraph x).neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hza_adj
  have hzb_mem : zb ∈ (hullGraph x).neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hzb_adj
  have hzc_mem : zc ∈ (hullGraph x).neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hzc_adj
  have h_subset : ({za, zb, zc} : Finset V) ⊆ (hullGraph x).neighborFinset v := by
    intro z hz
    simp [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl | rfl)
    · exact hza_mem
    · exact hzb_mem
    · exact hzc_mem
  have h_card_three : ({za, zb, zc} : Finset V).card = 3 := by
    simp [hza_ne_zb, hza_ne_zc, hzb_ne_zc]
  have h_card_le : ({za, zb, zc} : Finset V).card ≤ ((hullGraph x).neighborFinset v).card :=
    Finset.card_le_card h_subset
  rw [h_card_three] at h_card_le
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h_card_le
  exact h_card_le

theorem hull_distinctDirs (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) : DistinctDirs (hullGraph x) x := by
  refine ⟨?_, ?_⟩
  · intro v w h_adj
    have h_exp : ExposedPair x v w := (hullGraph_adj x v w).mp h_adj
    exact hull_tdir_ne_zero x hx hinj hB h_exp
  · intro v a b h_adj_a h_adj_b h_ne
    have h_exp_a : ExposedPair x v a := (hullGraph_adj x v a).mp h_adj_a
    have h_exp_b : ExposedPair x v b := (hullGraph_adj x v b).mp h_adj_b
    have h_pos := hull_ocorner_pos x hx hinj hB h_exp_a h_exp_b h_ne
    exact ne_of_gt h_pos

theorem hull_rot_pos (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
    (_hrho : IsAngular rho x) (d : (hullGraph x).Dart) :
    0 < ocorner (x d.fst) (x d.snd) (x (rho.rot d).snd) := by
  have hdeg := hull_three_le_degree x hx hinj hB d.fst
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b, a ≠ b ∧ (hullGraph x).Adj d.fst a ∧
      (hullGraph x).Adj d.fst b := by
    have h1 : 1 < ((hullGraph x).neighborFinset d.fst).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
    exact ⟨a, b, hab, (SimpleGraph.mem_neighborFinset _ _ _).mp ha,
      (SimpleGraph.mem_neighborFinset _ _ _).mp hb⟩
  have hne := rot_ne_self rho d a b hab ha hb
  have hfst : (rho.rot d).fst = d.fst := rho.rot_fst d
  have hsnd : d.snd ≠ (rho.rot d).snd := fun h =>
    hne (SimpleGraph.Dart.ext _ _ (Prod.ext hfst h.symm))
  have hexp2 : ExposedPair x d.fst (rho.rot d).snd := by
    have h := (rho.rot d).adj
    rw [hfst] at h
    exact h
  exact hull_ocorner_pos x hx hinj hB d.adj hexp2 hsnd

/-! ## S3: the successor plane of a hull dart (Lemma C) and connectivity (Lemma E) -/

/-- The successor of `d` is the hull neighbour `y` counterclockwise from `d.snd` within `π` with
no hull neighbour strictly between. -/
theorem hull_rot_snd_eq (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
    (hrho : IsAngular rho x) (d : (hullGraph x).Dart) (y : V) (hy : ExposedPair x d.fst y)
    (hdy : 0 < ⟪cross (x d.fst) (x d.snd), x y⟫)
    (hbetween : ∀ w, ExposedPair x d.fst w →
      ¬ (0 < ⟪cross (x d.fst) (x d.snd), x w⟫ ∧ 0 < ⟪cross (x d.fst) (x w), x y⟫)) :
    (rho.rot d).snd = y := by
  set v := d.fst with hv
  set u := d.snd with hu
  set w := (rho.rot d).snd with hw
  have hwfst : (rho.rot d).fst = v := rho.rot_fst d
  have hlt : ∀ a b : E3, ocorner (x v) a b < 2 * π := fun a b => by
    have h := (toIcoMod_mem_Ico two_pi_pos (0 : ℝ)
      (Complex.arg ⟨⟪tdir (x v) a, tdir (x v) b⟫, ⟪x v, cross (tdir (x v) a) (tdir (x v) b)⟫⟩)).2
    rw [zero_add] at h
    exact h
  have hyu : y ≠ u := by
    intro h
    rw [h] at hdy
    have h0 : ⟪cross (x v) (x u), x u⟫ = 0 := by
      rw [real_inner_comm]
      exact inner_cross_right_self _ _
    linarith
  obtain ⟨hθy0, hθyπ⟩ := (ocorner_pos_lt_pi_iff (x v) (x u) (x y)).mpr hdy
  have hθw0 : 0 < ocorner (x v) (x u) (x w) := hull_rot_pos x hx hinj hB rho hrho d
  have hθwy : ocorner (x v) (x u) (x w) ≤ ocorner (x v) (x u) (x y) :=
    hrho d ⟨(v, y), hy⟩ rfl (fun h => hyu (congrArg (fun e : (hullGraph x).Dart => e.snd) h))
  have hdw : 0 < ⟪cross (x v) (x u), x w⟫ :=
    (ocorner_pos_lt_pi_iff (x v) (x u) (x w)).mp ⟨hθw0, by linarith⟩
  by_contra hwy
  have hexw : ExposedPair x v w := by
    have h := (rho.rot d).adj
    rw [hwfst] at h
    exact h
  have hc0 : 0 < ocorner (x v) (x w) (x y) := hull_ocorner_pos x hx hinj hB hexw hy hwy
  have hc2 : ocorner (x v) (x w) (x y) < 2 * π := hlt _ _
  have hadd := ocorner_add (x v) (x u) (x w) (x y) (hx v)
    (hull_tdir_ne_zero x hx hinj hB d.adj) (hull_tdir_ne_zero x hx hinj hB hexw)
    (hull_tdir_ne_zero x hx hinj hB hy)
  obtain ⟨-, z, hz⟩ := (toIcoMod_eq_iff two_pi_pos).mp hadd.symm
  rw [zsmul_eq_mul] at hz
  have hπ := Real.pi_pos
  have hz1 : (z : ℝ) < 1 := by
    by_contra h
    rw [not_lt] at h
    have : (1 : ℝ) * (2 * π) ≤ (z : ℝ) * (2 * π) := mul_le_mul_of_nonneg_right h (by linarith)
    linarith
  have hz2 : (-1 : ℝ) < z := by
    by_contra h
    rw [not_lt] at h
    have : (z : ℝ) * (2 * π) ≤ (-1) * (2 * π) := mul_le_mul_of_nonneg_right h (by linarith)
    linarith
  have hz0 : z = 0 := by
    have h1 : z < 1 := by exact_mod_cast hz1
    have h2 : -1 < z := by exact_mod_cast hz2
    omega
  rw [hz0, Int.cast_zero, zero_mul, add_zero] at hz
  have hwy' : 0 < ⟪cross (x v) (x w), x y⟫ :=
    (ocorner_pos_lt_pi_iff (x v) (x w) (x y)).mp ⟨hc0, by linarith⟩
  exact hbetween w hexw ⟨hdw, hwy'⟩

/-- Lemma C: a hull dart, its successor and a supporting plane through the three points. -/
theorem hull_step (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
    (hrho : IsAngular rho x) (d : (hullGraph x).Dart) :
    0 < ⟪cross (x d.fst) (x d.snd), x (rho.rot d).snd⟫ ∧
      ∃ m : E3, (∀ z, ⟪x z, m⟫ ≤ 1) ∧ ⟪x d.fst, m⟫ = 1 ∧ ⟪x d.snd, m⟫ = 1 ∧
        ⟪x (rho.rot d).snd, m⟫ = 1 ∧
        ∀ z, ⟪x z, m⟫ = 1 → z ≠ d.fst → z ≠ d.snd → z ≠ (rho.rot d).snd →
          0 < ⟪cross (x d.fst) (x d.snd), x z⟫ ∧
            0 < ⟪cross (x d.fst) (x z), x (rho.rot d).snd⟫ := by
  set v := d.fst with hv
  set u := d.snd with hu
  have hvu : ExposedPair x v u := d.adj
  have hu_ne_v : u ≠ v := hvu.1.symm
  have hv_ne_u : v ≠ u := hvu.1
  have hx_v_norm : ‖x v‖ = 1 := hx v
  have hx_v_ne_zero : x v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx_v_norm
    linarith
  have hp_mem : link x v u ∈ linkSet x v := by
    rw [mem_linkSet]
    exact ⟨u, hu_ne_v, rfl⟩
  have hpx : ∃ n : E3, ∀ y ∈ linkSet x v, y ≠ link x v u → ⟪y, n⟫ < ⟪link x v u, n⟫ := by
    have h_iff := (exposedPair_iff_link x hx hinj hu_ne_v).mp hvu
    rcases h_iff with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro y hy hne
    exact hn y hy hne
  have hP : ∀ y ∈ linkSet x v, ⟪x v, y⟫ = 0 := by
    intro y hy
    rw [mem_linkSet] at hy
    rcases hy with ⟨z, hz_ne_v, hy_eq⟩
    rw [← hy_eq]
    exact inner_link x hx v z
  have hin_link : ∀ e : E3, ⟪x v, e⟫ = 0 → e ≠ 0 → ∃ y ∈ linkSet x v, 0 < ⟪y, e⟫ :=
    link_inside x hx hinj hB v
  rcases gift_wrap (x v) hx_v_ne_zero (linkSet x v) hP hin_link (link x v u) hp_mem hpx with
    ⟨s, hs, n, hn_v, hpos_cross, hpos_p_n, h_s_n, h_le, h_between, h_exposed_s, h_no_exposed_between⟩
  -- Step 2: s = link x v y with y ≠ v
  have hs_mem : s ∈ linkSet x v := hs
  rw [mem_linkSet] at hs_mem
  rcases hs_mem with ⟨y, hy_ne_v, hs_eq⟩
  -- hs_eq : link x v y = s
  -- y is a hull neighbour of v (exposedPair_iff_link using h_exposed_s)
  have hy_exposed : ExposedPair x v y := by
    rw [exposedPair_iff_link x hx hinj hy_ne_v]
    rcases h_exposed_s with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro w hw hw_ne
    -- hw_ne : w ≠ link x v y, hm expects w ≠ s
    have hw_ne_s : w ≠ s := by
      rw [← hs_eq]
      exact hw_ne
    have h_ineq := hm w hw hw_ne_s
    -- h_ineq : ⟪w, m⟫ < ⟪s, m⟫
    -- But the goal is ⟪w, m⟫ < ⟪link x v y, m⟫
    rw [hs_eq]
    exact h_ineq
  -- 0 < ⟪cross (x v) (x u), x y⟫ (by det_link)
  have hpos_cross_xy : 0 < ⟪cross (x v) (x u), x y⟫ := by
    have hpos_cross' : 0 < ⟪cross (x v) (link x v u), link x v y⟫ := by
      rw [hs_eq]
      exact hpos_cross
    have h_det := det_link x v u y
    have h_factor1_pos : 0 < (1 - ⟪x v, x u⟫)⁻¹ := by
      have h_lt : ⟪x v, x u⟫ < 1 := inner_lt_one_of_ne x hx hinj hu_ne_v
      have h_pos : 0 < 1 - ⟪x v, x u⟫ := by linarith
      exact inv_pos.mpr h_pos
    have h_factor2_pos : 0 < (1 - ⟪x v, x y⟫)⁻¹ := by
      have h_lt : ⟪x v, x y⟫ < 1 := inner_lt_one_of_ne x hx hinj hy_ne_v
      have h_pos : 0 < 1 - ⟪x v, x y⟫ := by linarith
      exact inv_pos.mpr h_pos
    have h_pos_prod : 0 < (1 - ⟪x v, x u⟫)⁻¹ * (1 - ⟪x v, x y⟫)⁻¹ :=
      mul_pos h_factor1_pos h_factor2_pos
    rw [h_det] at hpos_cross'
    contrapose! hpos_cross'
    nlinarith
  -- Step 3: Apply hull_rot_snd_eq to get (rho.rot d).snd = y
  have h_rot_snd_eq : (rho.rot d).snd = y := by
    apply hull_rot_snd_eq x hx hinj hB rho hrho d y hy_exposed hpos_cross_xy
    intro w hw_exposed h_and
    rcases h_and with ⟨h_cross_uw, h_cross_wy⟩
    -- Convert to link space using det_link
    have hw_ne_v : w ≠ v := by
      -- hw_exposed.1 : d.toProd.1 ≠ w, but v := d.fst := d.toProd.1
      -- So hw_exposed.1 : v ≠ w, and we need w ≠ v
      exact Ne.symm hw_exposed.1
    have h_cross_uw_link : 0 < ⟪cross (x v) (link x v u), link x v w⟫ := by
      have h_det := det_link x v u w
      have h_factors_pos : 0 < (1 - ⟪x v, x u⟫)⁻¹ * (1 - ⟪x v, x w⟫)⁻¹ := by
        have h1 : 0 < (1 - ⟪x v, x u⟫)⁻¹ := by
          have h_lt : ⟪x v, x u⟫ < 1 := inner_lt_one_of_ne x hx hinj hu_ne_v
          exact inv_pos.mpr (by linarith)
        have h2 : 0 < (1 - ⟪x v, x w⟫)⁻¹ := by
          have h_lt : ⟪x v, x w⟫ < 1 := inner_lt_one_of_ne x hx hinj hw_ne_v
          exact inv_pos.mpr (by linarith)
        exact mul_pos h1 h2
      rw [h_det]
      nlinarith
    have h_cross_wy_link : 0 < ⟪cross (x v) (link x v w), s⟫ := by
      rw [← hs_eq]
      have h_det := det_link x v w y
      have h_factors_pos : 0 < (1 - ⟪x v, x w⟫)⁻¹ * (1 - ⟪x v, x y⟫)⁻¹ := by
        have h1 : 0 < (1 - ⟪x v, x w⟫)⁻¹ := by
          have h_lt : ⟪x v, x w⟫ < 1 := inner_lt_one_of_ne x hx hinj hw_ne_v
          exact inv_pos.mpr (by linarith)
        have h2 : 0 < (1 - ⟪x v, x y⟫)⁻¹ := by
          have h_lt : ⟪x v, x y⟫ < 1 := inner_lt_one_of_ne x hx hinj hy_ne_v
          exact inv_pos.mpr (by linarith)
        exact mul_pos h1 h2
      rw [h_det]
      nlinarith
    -- Now use h_no_exposed_between
    have h_link_w_exposed : ∃ m : E3, ∀ z ∈ linkSet x v, z ≠ link x v w → ⟪z, m⟫ < ⟪link x v w, m⟫ := by
      have h_iff := (exposedPair_iff_link x hx hinj hw_ne_v).mp hw_exposed
      rcases h_iff with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      intro z hz hz_ne
      exact hm z hz hz_ne
    have h_link_w_mem : link x v w ∈ linkSet x v := by
      rw [mem_linkSet]
      exact ⟨w, hw_ne_v, rfl⟩
    have h_contra := h_no_exposed_between (link x v w) h_link_w_mem h_link_w_exposed
    apply h_contra
    exact ⟨h_cross_uw_link, h_cross_wy_link⟩
  -- Now we have (rho.rot d).snd = y
  rw [h_rot_snd_eq]
  -- Goal: 0 < ⟪cross (x v) (x u), x y⟫ ∧ ∃ m, ...
  refine ⟨hpos_cross_xy, ?_⟩
  -- Step 4: Construct m
  set k := ⟪link x v u, n⟫ with hk_def
  have hk_pos : 0 < k := hpos_p_n
  set N := n + k • (x v) with hN_def
  have h_inner_self : ⟪x v, x v⟫ = 1 := by
    calc
      ⟪x v, x v⟫ = ‖x v‖ ^ 2 := real_inner_self_eq_norm_sq (x v)
      _ = 1 ^ 2 := by rw [hx_v_norm]
      _ = 1 := by norm_num
  have hN_inner_v : ⟪x v, N⟫ = k := by
    rw [hN_def, inner_add_right, inner_smul_right, hn_v, h_inner_self]
    ring
  have hN_inner_link : ∀ z : V, ⟪link x v z, N⟫ = ⟪link x v z, n⟫ := by
    intro z
    rw [hN_def, inner_add_right, inner_smul_right]
    rw [real_inner_comm (x v) (link x v z), inner_link x hx v z]
    ring
  set m := k⁻¹ • N with hm_def
  have hm_inner_v : ⟪x v, m⟫ = 1 := by
    rw [hm_def, inner_smul_right, hN_inner_v]
    field_simp [ne_of_gt hk_pos]
  have hm_inner_u : ⟪x u, m⟫ = 1 := by
    rw [hm_def, inner_smul_right]
    by_cases h_eq : u = v
    · exfalso; exact hv_ne_u h_eq.symm
    · have h_transfer := link_transfer x hx hinj h_eq N
      rw [hN_inner_v, hN_inner_link u] at h_transfer
      have hzero : ⟪link x v u, n⟫ - k = 0 := by rw [hk_def]; ring
      rw [hzero] at h_transfer
      have h_transfer' : ⟪x u, N⟫ = k := by linarith
      rw [h_transfer']
      field_simp [ne_of_gt hk_pos]
  have hm_inner_y : ⟪x y, m⟫ = 1 := by
    rw [hm_def, inner_smul_right]
    have h_transfer := link_transfer x hx hinj hy_ne_v N
    rw [hN_inner_v, hN_inner_link y] at h_transfer
    rw [← hs_eq] at h_s_n
    rw [hk_def] at h_s_n
    have hzero : ⟪link x v y, n⟫ - k = 0 := by linarith
    rw [hzero] at h_transfer
    have h_transfer' : ⟪x y, N⟫ = k := by linarith
    rw [h_transfer']
    field_simp [ne_of_gt hk_pos]
  have hm_le_one : ∀ z, ⟪x z, m⟫ ≤ 1 := by
    intro z
    rw [hm_def, inner_smul_right]
    by_cases h_eq : z = v
    · subst h_eq
      rw [hN_inner_v]
      have hcalc : k⁻¹ * k = 1 := by field_simp [ne_of_gt hk_pos]
      rw [hcalc]
    · have h_transfer := link_transfer x hx hinj h_eq N
      rw [hN_inner_v, hN_inner_link z] at h_transfer
      have h_factor_pos : 0 < 1 - ⟪x v, x z⟫ := by
        have h_lt : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj h_eq
        linarith
      have h_link_mem : link x v z ∈ linkSet x v := by
        rw [mem_linkSet]
        exact ⟨z, h_eq, rfl⟩
      have h_link_le : ⟪link x v z, n⟫ ≤ k := h_le (link x v z) h_link_mem
      have h_rhs_nonpos : (1 - ⟪x v, x z⟫) * (⟪link x v z, n⟫ - k) ≤ 0 := by
        have h_diff_nonpos : ⟪link x v z, n⟫ - k ≤ 0 := by linarith
        nlinarith
      have hN_le_k : ⟪x z, N⟫ ≤ k := by linarith
      calc
        k⁻¹ * ⟪x z, N⟫ ≤ k⁻¹ * k := by gcongr
        _ = 1 := by field_simp [ne_of_gt hk_pos]
  refine ⟨m, hm_le_one, hm_inner_v, hm_inner_u, hm_inner_y, ?_⟩
  -- Step 5: The last condition
  intro z hz_eq_one hz_ne_v hz_ne_u hz_ne_y
  have hN_eq_k : ⟪x z, N⟫ = k := by
    rw [hm_def, inner_smul_right] at hz_eq_one
    field_simp [ne_of_gt hk_pos] at hz_eq_one
    exact hz_eq_one
  have h_link_eq_k : ⟪link x v z, n⟫ = k := by
    have h_transfer := link_transfer x hx hinj hz_ne_v N
    rw [hN_inner_v, hN_eq_k] at h_transfer
    rw [hN_inner_link z] at h_transfer
    have h_factor_pos : 0 < 1 - ⟪x v, x z⟫ := by
      have h_lt : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj hz_ne_v
      linarith
    have h_zero : (1 - ⟪x v, x z⟫) * (⟪link x v z, n⟫ - k) = 0 := by linarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_zero with h | h
    · linarith
    · linarith
  have h_link_ne_p : link x v z ≠ link x v u := by
    intro heq
    apply hz_ne_u
    exact link_inj x hx hinj v hz_ne_v hu_ne_v heq
  have h_link_ne_s : link x v z ≠ s := by
    intro heq
    apply hz_ne_y
    rw [← hs_eq] at heq
    exact (link_inj x hx hinj v (a := y) (b := z) hy_ne_v hz_ne_v heq.symm).symm
  have h_link_mem : link x v z ∈ linkSet x v := by
    rw [mem_linkSet]
    exact ⟨z, hz_ne_v, rfl⟩
  have h_link_eq_p_n : ⟪link x v z, n⟫ = ⟪link x v u, n⟫ := by
    rw [h_link_eq_k, hk_def]
  have h_cross_pos := h_between (link x v z) h_link_mem h_link_eq_p_n h_link_ne_p h_link_ne_s
  rcases h_cross_pos with ⟨h_cross1, h_cross2⟩
  -- h_cross1 : 0 < ⟪cross (x v) (link x v u), link x v z⟫
  -- h_cross2 : 0 < ⟪cross (x v) (link x v z), s⟫
  -- Convert to x-space using det_link
  have h_cross1_x : 0 < ⟪cross (x v) (x u), x z⟫ := by
    have h_det := det_link x v u z
    have h_factors_pos : 0 < (1 - ⟪x v, x u⟫)⁻¹ * (1 - ⟪x v, x z⟫)⁻¹ := by
      have h1 : 0 < (1 - ⟪x v, x u⟫)⁻¹ := by
        have h_lt : ⟪x v, x u⟫ < 1 := inner_lt_one_of_ne x hx hinj hu_ne_v
        exact inv_pos.mpr (by linarith)
      have h2 : 0 < (1 - ⟪x v, x z⟫)⁻¹ := by
        have h_lt : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj hz_ne_v
        exact inv_pos.mpr (by linarith)
      exact mul_pos h1 h2
    rw [h_det] at h_cross1
    contrapose! h_cross1
    nlinarith
  have h_cross2_x : 0 < ⟪cross (x v) (x z), x y⟫ := by
    have h_det := det_link x v z y
    rw [hs_eq] at h_det
    have h_factors_pos : 0 < (1 - ⟪x v, x z⟫)⁻¹ * (1 - ⟪x v, x y⟫)⁻¹ := by
      have h1 : 0 < (1 - ⟪x v, x z⟫)⁻¹ := by
        have h_lt : ⟪x v, x z⟫ < 1 := inner_lt_one_of_ne x hx hinj hz_ne_v
        exact inv_pos.mpr (by linarith)
      have h2 : 0 < (1 - ⟪x v, x y⟫)⁻¹ := by
        have h_lt : ⟪x v, x y⟫ < 1 := inner_lt_one_of_ne x hx hinj hy_ne_v
        exact inv_pos.mpr (by linarith)
      exact mul_pos h1 h2
    rw [h_det] at h_cross2
    contrapose! h_cross2
    nlinarith
  exact ⟨h_cross1_x, h_cross2_x⟩

/-- Lemma E, the step: from `v ≠ w` a hull edge climbs towards `w`. -/
theorem hull_step_up (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
    (_hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) {v w : V} (hvw : v ≠ w) :
    ∃ y, ExposedPair x v y ∧ ⟪x v, x w⟫ < ⟪x y, x w⟫ := by
  have hw_ne_v : w ≠ v := Ne.symm hvw
  have h_inner_lt_one : ⟪x v, x w⟫ < 1 := inner_lt_one_of_ne x hx hinj hw_ne_v
  have h_pos : 0 < 1 - ⟪x v, x w⟫ := by linarith
  -- linkSet x v is nonempty because it contains link x v w
  have h_mem : link x v w ∈ linkSet x v := by
    rw [mem_linkSet]
    exact ⟨w, hw_ne_v, rfl⟩
  have h_nonempty : (linkSet x v).Nonempty := ⟨link x v w, h_mem⟩
  -- get an exposed maximizer s of ⟪·, x w⟫ over linkSet x v
  rcases exists_exposed_max (linkSet x v) h_nonempty (x w) with ⟨s, hs, h_le, n, hn⟩
  -- s is in linkSet, so s = link x v y for some y ≠ v
  rcases (mem_linkSet x v s).mp hs with ⟨y, hy_ne_v, hy_eq⟩
  -- from link_transfer at w, we get a key inequality
  have h_transfer_w : ⟪x w, x w⟫ - ⟪x v, x w⟫ = (1 - ⟪x v, x w⟫) * (⟪link x v w, x w⟫ - ⟪x v, x w⟫) :=
    link_transfer x hx hinj hw_ne_v (x w)
  have h_norm_w : ⟪x w, x w⟫ = 1 := by
    calc
      ⟪x w, x w⟫ = ‖x w‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 ^ 2 := by rw [hx w]
      _ = 1 := by norm_num
  have h_key : 1 = ⟪link x v w, x w⟫ - ⟪x v, x w⟫ := by
    rw [h_norm_w] at h_transfer_w
    have h_eq : 1 - ⟪x v, x w⟫ = (1 - ⟪x v, x w⟫) * (⟪link x v w, x w⟫ - ⟪x v, x w⟫) := by
      simpa using h_transfer_w
    have h_factor : (1 - ⟪x v, x w⟫) * ((⟪link x v w, x w⟫ - ⟪x v, x w⟫) - 1) = 0 := by
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with (hA | hB)
    · linarith
    · linarith
  have h_link_gt : ⟪x v, x w⟫ < ⟪link x v w, x w⟫ := by
    linarith
  have h_s_ge : ⟪link x v w, x w⟫ ≤ ⟪s, x w⟫ := h_le (link x v w) h_mem
  have h_s_gt : ⟪x v, x w⟫ < ⟪s, x w⟫ := by
    linarith
  -- apply link_transfer at y
  have h_transfer_y : ⟪x y, x w⟫ - ⟪x v, x w⟫ = (1 - ⟪x v, x y⟫) * (⟪s, x w⟫ - ⟪x v, x w⟫) := by
    calc
      ⟪x y, x w⟫ - ⟪x v, x w⟫ = (1 - ⟪x v, x y⟫) * (⟪link x v y, x w⟫ - ⟪x v, x w⟫) :=
        link_transfer x hx hinj hy_ne_v (x w)
      _ = (1 - ⟪x v, x y⟫) * (⟪s, x w⟫ - ⟪x v, x w⟫) := by rw [hy_eq]
  have h_inner_lt_one_y : ⟪x v, x y⟫ < 1 := inner_lt_one_of_ne x hx hinj hy_ne_v
  have h_pos_y : 0 < 1 - ⟪x v, x y⟫ := by linarith
  have h_diff_pos : 0 < ⟪s, x w⟫ - ⟪x v, x w⟫ := by linarith
  have h_inner_gt : ⟪x v, x w⟫ < ⟪x y, x w⟫ := by
    have h_pos_prod : 0 < (1 - ⟪x v, x y⟫) * (⟪s, x w⟫ - ⟪x v, x w⟫) :=
      mul_pos h_pos_y h_diff_pos
    have h_pos_diff : 0 < ⟪x y, x w⟫ - ⟪x v, x w⟫ := by
      rw [h_transfer_y]
      exact h_pos_prod
    linarith
  -- now prove ExposedPair x v y
  have h_exposed : ExposedPair x v y := by
    rw [exposedPair_iff_link x hx hinj hy_ne_v]
    refine ⟨n, λ y' hy' hy'_ne => ?_⟩
    rw [hy_eq] at hy'_ne
    have h_lt := hn y' hy' hy'_ne
    rw [hy_eq]
    exact h_lt
  exact ⟨y, h_exposed, h_inner_gt⟩

/-- Lemma E: the hull graph is connected. -/
theorem hull_connected [Nonempty V] (x : V → E3) (hx : ∀ v, ‖x v‖ = 1)
    (hinj : Function.Injective x) (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) :
    (hullGraph x).Connected := by
  apply SimpleGraph.Connected.mk
  intro v w
  -- For each v, prove Reachable v w by strong induction on μ(v) = |{z | ⟪x v, x w⟫ < ⟪x z, x w⟫}|
  let μ (v : V) : ℕ := ((Finset.univ : Finset V).filter fun z => ⟪x v, x w⟫ < ⟪x z, x w⟫).card
  have hμ_def (v : V) : μ v = ((Finset.univ : Finset V).filter fun z => ⟪x v, x w⟫ < ⟪x z, x w⟫).card := rfl
  -- Use strong induction on ℕ with a predicate that quantifies over V
  let P (n : ℕ) : Prop := ∀ (v' : V), μ v' = n → (hullGraph x).Reachable v' w
  have hP_step : ∀ n, (∀ m < n, P m) → P n := by
    intro n IH v' hv'
    by_cases h_eq : v' = w
    · subst h_eq; exact SimpleGraph.Reachable.refl _
    · have h_step := hull_step_up x hx hinj hB h_eq
      rcases h_step with ⟨y, hy_exp, hy_lt⟩
      have h_adj : (hullGraph x).Adj v' y := by
        rw [hullGraph_adj]
        exact hy_exp
      -- Show μ y < μ v'
      let S (v : V) : Finset V := (Finset.univ : Finset V).filter fun z => ⟪x v, x w⟫ < ⟪x z, x w⟫
      have hS_subset : S y ⊆ S v' := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        rcases hz with ⟨hz_univ, hz_lt⟩
        exact ⟨hz_univ, lt_trans hy_lt hz_lt⟩
      have hy_notin_Sy : y ∉ S y := by
        rw [Finset.mem_filter]
        intro ⟨_, h⟩; exact lt_irrefl _ h
      have hy_in_Sv' : y ∈ S v' := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ y, hy_lt⟩
      have h_not_subset : ¬ S v' ⊆ S y := by
        intro h; apply hy_notin_Sy; exact h hy_in_Sv'
      have hS_ssubset : S y ⊂ S v' := by
        rw [Finset.ssubset_def]
        exact ⟨hS_subset, h_not_subset⟩
      have hμ_lt : μ y < μ v' := by
        rw [hμ_def y, hμ_def v']
        exact Finset.card_lt_card hS_ssubset
      have hμ_lt_n : μ y < n := by
        rw [← hv']
        exact hμ_lt
      have h_reach_y : (hullGraph x).Reachable y w := IH (μ y) hμ_lt_n y rfl
      exact h_adj.reachable.trans h_reach_y
  have hPμv : P (μ v) := Nat.strong_induction_on (μ v) hP_step
  exact hPμv v rfl

end Hull

end Tammes15
