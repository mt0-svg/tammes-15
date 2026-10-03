import Tammes15.TwoConn.Regions

/-!
# Fan cones of the facets

Three steps of the proof of Corollary A.6 by the convex hull (paper,
Lemma A.5 and Corollary A.6). Every point of a facet plane is a vertex of the facet
(`vertex_complete`), so a plane carries one facet (`orbit_eq_of_polar_eq`). Seen from its first
vertex, the other vertices of a facet turn counterclockwise (`fan_det_pos`), and the open cones over
the fan triangles of all facets are pairwise disjoint (`cone_unique`).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification (PermutationCycle PermutationOrbit
  permutationOrbitSetoid orbitPermutationCycle orbitPermutationCycle_class)

namespace Tammes15

open scoped Classical
open Fin.NatCast

/-! ## Linear algebra -/

theorem inner_cross_swap3 (p v r : E3) : ⟪p, cross v r⟫ = -⟪cross v p, r⟫ := by
  rw [real_inner_comm, inner_cross_cyc, cross_swap v p, inner_neg_left]

/-- A sign change of a sequence of reals, from positive at `1` to nonpositive at `n`. -/
theorem exists_sign_change (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (h1 : 0 < g 1) (hgn : g n ≤ 0) :
    ∃ a, 1 ≤ a ∧ a < n ∧ 0 < g a ∧ g (a + 1) ≤ 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [zero_add] at hgn
      linarith
    · by_cases h : g n ≤ 0
      · obtain ⟨a, ha1, han, hga, hga'⟩ := ih hpos h
        exact ⟨a, ha1, by omega, hga, hga'⟩
      · exact ⟨n, hpos, by omega, lt_of_not_ge h, hgn⟩

/-- Strict convexity of the sphere against a Cramer decomposition: a point of the plane of three
unit vectors, with the signs of a point of their closed triangle away from two sides, lies strictly
inside the ball. -/
theorem norm_lt_one_of_cramer (a b c y m : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hac : a ≠ c) (hD : 0 < ⟪cross a b, c⟫) (h₀ : 0 < ⟪cross y b, c⟫) (h₁ : 0 ≤ ⟪cross a y, c⟫)
    (h₂ : 0 < ⟪cross a b, y⟫) (ham : ⟪a, m⟫ = 1) (hbm : ⟪b, m⟫ = 1) (hcm : ⟪c, m⟫ = 1)
    (hym : ⟪y, m⟫ = 1) : ‖y‖ < 1 := by
  have hy := cramer3 a b c y hD.ne'
  set D := ⟪cross a b, c⟫
  have hs : ⟪cross y b, c⟫ / D + ⟪cross a y, c⟫ / D + ⟪cross a b, y⟫ / D = 1 := by
    have h := congrArg (fun w => ⟪w, m⟫) hy
    simp only [inner_add_left, real_inner_smul_left, ham, hbm, hcm, hym, mul_one] at h
    linarith
  have hlt := norm_lt_one_of_comb a c b ha hc hb hac (⟪cross y b, c⟫ / D) (⟪cross a b, y⟫ / D)
    (⟪cross a y, c⟫ / D) (div_pos h₀ hD) (div_pos h₂ hD) (div_nonneg h₁ hD.le) (by linarith)
  rw [hy]
  convert hlt using 2
  abel

/-- The open cone over a triangle, by the signs of the three sides seen from `z`. -/
def InCone (z t₀ t₁ t₂ : E3) : Prop :=
  0 < ⟪cross z t₀, t₁⟫ ∧ 0 < ⟪cross z t₁, t₂⟫ ∧ 0 < ⟪cross z t₂, t₀⟫

theorem cone_coeffs (z t₀ t₁ t₂ : E3) (hD : 0 < ⟪cross t₀ t₁, t₂⟫) (h : InCone z t₀ t₁ t₂) :
    ∃ l₀ l₁ l₂ : ℝ, 0 < l₀ ∧ 0 < l₁ ∧ 0 < l₂ ∧ z = l₀ • t₀ + l₁ • t₁ + l₂ • t₂ := by
  refine ⟨_, _, _, div_pos h.2.1 hD, div_pos ?_ hD, div_pos ?_ hD, cramer3 t₀ t₁ t₂ z hD.ne'⟩
  · rw [inner_cross_cyc t₂ t₀ z, inner_cross_cyc z t₂ t₀]
    exact h.2.2
  · rw [inner_cross_cyc z t₀ t₁]
    exact h.1

/-- Two cone decompositions of one point over triangles of two supporting planes: the vertices of
the first triangle lie on the second plane. -/
theorem cone_level (z t₀ t₁ t₂ s₀ s₁ s₂ m m' : E3) (l₀ l₁ l₂ k₀ k₁ k₂ : ℝ) (hl₀ : 0 < l₀)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hz : z = l₀ • t₀ + l₁ • t₁ + l₂ • t₂) (hz' : z = k₀ • s₀ + k₁ • s₁ + k₂ • s₂)
    (ht₀ : ⟪t₀, m⟫ = 1) (ht₁ : ⟪t₁, m⟫ = 1) (ht₂ : ⟪t₂, m⟫ = 1)
    (hs₀ : ⟪s₀, m'⟫ = 1) (hs₁ : ⟪s₁, m'⟫ = 1) (hs₂ : ⟪s₂, m'⟫ = 1)
    (ht₀' : ⟪t₀, m'⟫ ≤ 1) (ht₁' : ⟪t₁, m'⟫ ≤ 1) (ht₂' : ⟪t₂, m'⟫ ≤ 1)
    (hs₀' : ⟪s₀, m⟫ ≤ 1) (hs₁' : ⟪s₁, m⟫ ≤ 1) (hs₂' : ⟪s₂, m⟫ ≤ 1) :
    ⟪t₀, m'⟫ = 1 ∧ ⟪t₁, m'⟫ = 1 ∧ ⟪t₂, m'⟫ = 1 := by
  have e₁ := congrArg (fun w => ⟪w, m⟫) hz
  have e₂ := congrArg (fun w => ⟪w, m⟫) hz'
  have e₃ := congrArg (fun w => ⟪w, m'⟫) hz
  have e₄ := congrArg (fun w => ⟪w, m'⟫) hz'
  simp only [inner_add_left, real_inner_smul_left] at e₁ e₂ e₃ e₄
  rw [ht₀, ht₁, ht₂] at e₁
  rw [hs₀, hs₁, hs₂] at e₄
  have a₀ := mul_le_mul_of_nonneg_left hs₀' hk₀.le
  have a₁ := mul_le_mul_of_nonneg_left hs₁' hk₁.le
  have a₂ := mul_le_mul_of_nonneg_left hs₂' hk₂.le
  have b₀ := mul_le_mul_of_nonneg_left ht₀' hl₀.le
  have b₁ := mul_le_mul_of_nonneg_left ht₁' hl₁.le
  have b₂ := mul_le_mul_of_nonneg_left ht₂' hl₂.le
  have c₀ : l₀ * ⟪t₀, m'⟫ = l₀ * 1 := by linarith
  have c₁ : l₁ * ⟪t₁, m'⟫ = l₁ * 1 := by linarith
  have c₂ : l₂ * ⟪t₂, m'⟫ = l₂ * 1 := by linarith
  exact ⟨mul_left_cancel₀ hl₀.ne' c₀, mul_left_cancel₀ hl₁.ne' c₁, mul_left_cancel₀ hl₂.ne' c₂⟩

/-- Transitivity of the counterclockwise order seen from `v`, for points of a plane through `v`
at level `1`. -/
theorem det_pos_sphere (v a b q m : E3) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hq : ‖q‖ = 1) (hva : a ≠ v) (hvb : b ≠ v) (hvq : q ≠ v) (hvm : ⟪v, m⟫ = 1)
    (ham : ⟪a, m⟫ = 1) (hbm : ⟪b, m⟫ = 1) (hqm : ⟪q, m⟫ = 1) (hab : 0 < ⟪cross v a, b⟫)
    (hbq : 0 < ⟪cross v b, q⟫) : 0 < ⟪cross v a, q⟫ := by
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have horth : ∀ w, ⟪v, tdir v w⟫ = 0 := fun w => by
    rw [tdir, inner_sub_right, real_inner_smul_right, hvv, mul_one, sub_self]
  have hpos : ∀ w, ‖w‖ = 1 → w ≠ v → ⟪w, m⟫ = 1 → 0 < ⟪tdir v w, m⟫ := fun w hw hwv hwm => by
    have hlt : ⟪v, w⟫ < 1 := (inner_lt_one_iff_real_of_norm_eq_one hv hw).mpr (Ne.symm hwv)
    rw [tdir, inner_sub_left, real_inner_smul_left, hwm, hvm, mul_one]
    linarith
  have hdet : ∀ w w', ⟪cross v (tdir v w), tdir v w'⟫ = ⟪cross v w, w'⟫ := fun w w' => by
    rw [← inner_cross_cyc, real_inner_comm, inner_cross_tdir]
  have h := det_pos_trans v m (tdir v a) (tdir v b) (tdir v q) (horth a) (horth b) (horth q)
    (hpos a ha hva ham) (hpos b hb hvb hbm) (hpos q hq hvq hqm) (by rw [hdet]; exact hab)
    (by rw [hdet]; exact hbq)
  rwa [hdet] at h

/-! ## Face cycles of the hull rotation, read cyclically -/

section FanCones

variable {V : Type} [Fintype V] [DecidableEq V]
variable (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
  (hrho : IsAngular rho x)

/-- The vertex at position `k` of a face cycle of `rho`, read cyclically. -/
noncomputable def cvert (C : PermutationCycle rho.face) (k : ℕ) : V :=
  (C.point (k : Fin (C.size + 1))).fst

/-- The point at position `k` of a face cycle of `rho`. -/
noncomputable def cpt (C : PermutationCycle rho.face) (k : ℕ) : E3 := x (cvert x rho C k)

/-- The polar of the plane of a face cycle of `rho`. -/
noncomputable def cpolar (C : PermutationCycle rho.face) : E3 := facetPolar x rho (C.point 0)

theorem cvert_size (C : PermutationCycle rho.face) :
    cvert x rho C (C.size + 1) = cvert x rho C 0 := by
  unfold cvert
  rw [Fin.natCast_self, Nat.cast_zero]

theorem cvert_snd (C : PermutationCycle rho.face) (k : ℕ) :
    (C.point (k : Fin (C.size + 1))).snd = cvert x rho C (k + 1) := by
  unfold cvert
  rw [Nat.cast_succ, cycle_fst_succ x rho C]

include hx hinj hB hrho

theorem cvert_mem (C : PermutationCycle rho.face) (k : ℕ) :
    ⟪cpt x rho C k, cpolar x rho C⟫ = 1 := by
  unfold cpt cvert cpolar
  rw [← cycle_polar x hx hinj hB rho hrho C (k : Fin (C.size + 1))]
  exact (isFacetPolar_facetPolar x hx hinj hB rho hrho _).2.1

theorem cpolar_le (C : PermutationCycle rho.face) (z : V) : ⟪x z, cpolar x rho C⟫ ≤ 1 :=
  (isFacetPolar_facetPolar x hx hinj hB rho hrho _).1 z

/-- D2 along a face cycle. -/
theorem cvert_strict (C : PermutationCycle rho.face) (k : ℕ) (z : V)
    (hz : ⟪x z, cpolar x rho C⟫ = 1) (h₁ : z ≠ cvert x rho C k) (h₂ : z ≠ cvert x rho C (k + 1)) :
    0 < ⟪cross (cpt x rho C k) (cpt x rho C (k + 1)), x z⟫ := by
  have h := facetPolar_strict x hx hinj hB rho hrho (C.point (k : Fin (C.size + 1))) z
    (by rw [cycle_polar x hx hinj hB rho hrho]; exact hz) h₁ (by rw [cvert_snd]; exact h₂)
  rw [cvert_snd] at h
  exact h

/-- D3 along a face cycle. -/
theorem cvert_inj (C : PermutationCycle rho.face) {j k : ℕ} (hj : j ≤ C.size) (hk : k ≤ C.size)
    (h : cvert x rho C j = cvert x rho C k) : j = k := by
  have h' := congrArg Fin.val (cycle_fst_injective x hx hinj hB rho hrho C h)
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h'

theorem cpt_ne (C : PermutationCycle rho.face) {j k : ℕ} (hj : j ≤ C.size) (hk : k ≤ C.size)
    (hjk : j ≠ k) : cpt x rho C j ≠ cpt x rho C k :=
  fun h => hjk (cvert_inj x hx hinj hB rho hrho C hj hk (hinj h))

/-- D3': consecutive fan triangles turn counterclockwise. -/
theorem fan_step (C : PermutationCycle rho.face) (a : ℕ) (h₁ : 1 ≤ a) (h₂ : a + 1 ≤ C.size) :
    0 < ⟪cross (cpt x rho C 0) (cpt x rho C a), cpt x rho C (a + 1)⟫ := by
  have h := cvert_strict x hx hinj hB rho hrho C a (cvert x rho C 0)
    (cvert_mem x hx hinj hB rho hrho C 0)
    (fun h => by have := cvert_inj x hx hinj hB rho hrho C (by omega) (by omega) h; omega)
    (fun h => by have := cvert_inj x hx hinj hB rho hrho C (by omega) (by omega) h; omega)
  rw [inner_cross_cyc] at h
  exact h

/-- Every vertex on the plane of a facet is a vertex of the facet. -/
theorem vertex_complete (C : PermutationCycle rho.face) (z : V) (hz : ⟪x z, cpolar x rho C⟫ = 1) :
    ∃ k ≤ C.size, cvert x rho C k = z := by
  by_contra hno
  push Not at hno
  have hs := cycle_size_ge_two x hx hinj hB rho hrho C
  have hg1 : 0 < ⟪cross (cpt x rho C 0) (cpt x rho C 1), x z⟫ :=
    cvert_strict x hx hinj hB rho hrho C 0 z hz (fun h => hno 0 (by omega) h.symm)
      (fun h => hno 1 (by omega) h.symm)
  have hgn : ⟪cross (cpt x rho C 0) (cpt x rho C C.size), x z⟫ < 0 := by
    have h := cvert_strict x hx hinj hB rho hrho C C.size z hz
      (fun h => hno C.size le_rfl h.symm)
      (by rw [cvert_size]; exact fun h => hno 0 (by omega) h.symm)
    unfold cpt at h ⊢
    rw [cvert_size] at h
    rw [cross_swap, inner_neg_left]
    linarith
  obtain ⟨a, ha1, han, hga, hga'⟩ := exists_sign_change
    (fun j => ⟪cross (cpt x rho C 0) (cpt x rho C j), x z⟫) C.size (by omega) hg1 hgn.le
  have hD := fan_step x hx hinj hB rho hrho C a ha1 (by omega)
  have h₀ : 0 < ⟪cross (x z) (cpt x rho C a), cpt x rho C (a + 1)⟫ := by
    have h := cvert_strict x hx hinj hB rho hrho C a z hz (fun h => hno a (by omega) h.symm)
      (fun h => hno (a + 1) (by omega) h.symm)
    rw [inner_cross_cyc] at h
    exact h
  have h₁ : 0 ≤ ⟪cross (cpt x rho C 0) (x z), cpt x rho C (a + 1)⟫ := by
    have e : ⟪cross (cpt x rho C 0) (x z), cpt x rho C (a + 1)⟫ =
        -⟪cross (cpt x rho C 0) (cpt x rho C (a + 1)), x z⟫ := by
      rw [← inner_cross_swap3]
      exact real_inner_comm _ _
    linarith
  have hlt := norm_lt_one_of_cramer _ _ _ (x z) (cpolar x rho C) (hx _) (hx _) (hx _)
    (cpt_ne x hx hinj hB rho hrho C (by omega) (by omega) (by omega)) hD h₀ h₁ hga
    (cvert_mem x hx hinj hB rho hrho C 0) (cvert_mem x hx hinj hB rho hrho C a)
    (cvert_mem x hx hinj hB rho hrho C (a + 1)) hz
  rw [hx z] at hlt
  exact lt_irrefl _ hlt

/-- D4: a plane carries one facet. -/
theorem orbit_eq_of_polar_eq (f f' : PermutationOrbit rho.face)
    (h : cpolar x rho (orbitPermutationCycle rho.face f) =
      cpolar x rho (orbitPermutationCycle rho.face f')) : f = f' := by
  set C := orbitPermutationCycle rho.face f
  set C' := orbitPermutationCycle rho.face f'
  obtain ⟨k, -, hk⟩ := vertex_complete x hx hinj hB rho hrho C' (cvert x rho C 0)
    (by rw [← h]; exact cvert_mem x hx hinj hB rho hrho C 0)
  have hd : C'.point (k : Fin (C'.size + 1)) = C.point 0 := by
    refine dart_eq_of_polar_eq x hx hinj hB rho hrho _ _ ?_ ?_
    · rw [cycle_polar x hx hinj hB rho hrho C']
      exact h.symm
    · unfold cvert at hk
      rw [Nat.cast_zero] at hk
      exact hk
  have h₁ := orbitPermutationCycle_class rho.face f' (k : Fin (C'.size + 1))
  have h₂ := orbitPermutationCycle_class rho.face f 0
  rw [hd] at h₁
  exact h₂.symm.trans h₁

/-- D3': the fan of a facet from its first vertex turns counterclockwise. -/
theorem fan_det_pos (C : PermutationCycle rho.face) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ C.size) : 0 < ⟪cross (cpt x rho C 0) (cpt x rho C i), cpt x rho C j⟫ := by
  induction j, hij using Nat.le_induction with
  | base => exact fan_step x hx hinj hB rho hrho C i hi hj
  | succ j hij ih =>
    have hm := fun k => cvert_mem x hx hinj hB rho hrho C k
    exact det_pos_sphere _ _ _ _ (cpolar x rho C) (hx _) (hx _) (hx _) (hx _)
      (cpt_ne x hx hinj hB rho hrho C (by omega) (by omega) (by omega))
      (cpt_ne x hx hinj hB rho hrho C (by omega) (by omega) (by omega))
      (cpt_ne x hx hinj hB rho hrho C (by omega) (by omega) (by omega))
      (hm 0) (hm i) (hm j) (hm (j + 1)) (ih (by omega))
      (fan_step x hx hinj hB rho hrho C j (by omega) hj)

/-- Two fan cones of facets containing one point have the same plane. -/
theorem cone_same_polar (C C' : PermutationCycle rho.face) (a b : ℕ) (ha : 1 ≤ a)
    (ha' : a + 1 ≤ C.size) (hb : 1 ≤ b) (hb' : b + 1 ≤ C'.size) (z : E3)
    (h : InCone z (cpt x rho C 0) (cpt x rho C a) (cpt x rho C (a + 1)))
    (h' : InCone z (cpt x rho C' 0) (cpt x rho C' b) (cpt x rho C' (b + 1))) :
    cpolar x rho C = cpolar x rho C' := by
  have hD := fan_step x hx hinj hB rho hrho C a ha ha'
  have hD' := fan_step x hx hinj hB rho hrho C' b hb hb'
  obtain ⟨l₀, l₁, l₂, hl₀, hl₁, hl₂, hz⟩ := cone_coeffs _ _ _ _ hD h
  obtain ⟨k₀, k₁, k₂, hk₀, hk₁, hk₂, hz'⟩ := cone_coeffs _ _ _ _ hD' h'
  have hm := fun k => cvert_mem x hx hinj hB rho hrho C k
  have hm' := fun k => cvert_mem x hx hinj hB rho hrho C' k
  have hle := fun k => cpolar_le x hx hinj hB rho hrho C (cvert x rho C' k)
  have hle' := fun k => cpolar_le x hx hinj hB rho hrho C' (cvert x rho C k)
  obtain ⟨e₀, e₁, e₂⟩ := cone_level z _ _ _ _ _ _ _ _ l₀ l₁ l₂ k₀ k₁ k₂ hl₀ hl₁ hl₂ hk₀ hk₁ hk₂ hz
    hz'
    (hm 0) (hm a) (hm (a + 1)) (hm' 0) (hm' b) (hm' (b + 1)) (hle' 0) (hle' a) (hle' (a + 1))
    (hle 0) (hle b) (hle (b + 1))
  have h0 := eq_zero_of_inner_eq_zero3 _ _ _ (cpolar x rho C - cpolar x rho C') hD.ne'
    (by rw [inner_sub_right, hm, e₀, sub_self]) (by rw [inner_sub_right, hm, e₁, sub_self])
    (by rw [inner_sub_right, hm, e₂, sub_self])
  exact sub_eq_zero.mp h0

/-- Two fan cones of one facet containing one point are the same. -/
theorem cone_same_index (C : PermutationCycle rho.face) (a b : ℕ) (ha : 1 ≤ a)
    (hb' : b + 1 ≤ C.size) (hab : a < b) (z : E3)
    (h : InCone z (cpt x rho C 0) (cpt x rho C a) (cpt x rho C (a + 1)))
    (h' : InCone z (cpt x rho C 0) (cpt x rho C b) (cpt x rho C (b + 1))) : False := by
  have hD := fan_step x hx hinj hB rho hrho C a ha (by omega)
  obtain ⟨l₀, l₁, l₂, hl₀, hl₁, hl₂, hz⟩ := cone_coeffs _ _ _ _ hD h
  have h₁ := fan_det_pos x hx hinj hB rho hrho C a b ha hab (by omega)
  have h₂ : 0 ≤ ⟪cross (cpt x rho C 0) (cpt x rho C (a + 1)), cpt x rho C b⟫ := by
    rcases Nat.lt_or_ge (a + 1) b with hlt | hge
    · exact (fan_det_pos x hx hinj hB rho hrho C (a + 1) b (by omega) hlt (by omega)).le
    · have hb : b = a + 1 := by omega
      rw [hb, real_inner_comm, inner_cross_right_self]
  have hk := h'.1
  rw [← inner_cross_cyc, real_inner_comm, hz, inner_add_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, inner_cross_self,
    inner_cross_swap3, inner_cross_swap3] at hk
  nlinarith [mul_pos hl₁ h₁, mul_nonneg hl₂.le h₂]

/-- F': the open fan cones of all facets are pairwise disjoint. -/
theorem cone_unique (f f' : PermutationOrbit rho.face) (a b : ℕ) (ha : 1 ≤ a)
    (ha' : a + 1 ≤ (orbitPermutationCycle rho.face f).size) (hb : 1 ≤ b)
    (hb' : b + 1 ≤ (orbitPermutationCycle rho.face f').size) (z : E3)
    (h : InCone z (cpt x rho (orbitPermutationCycle rho.face f) 0)
      (cpt x rho (orbitPermutationCycle rho.face f) a)
      (cpt x rho (orbitPermutationCycle rho.face f) (a + 1)))
    (h' : InCone z (cpt x rho (orbitPermutationCycle rho.face f') 0)
      (cpt x rho (orbitPermutationCycle rho.face f') b)
      (cpt x rho (orbitPermutationCycle rho.face f') (b + 1))) :
    f = f' ∧ a = b := by
  have hf := orbit_eq_of_polar_eq x hx hinj hB rho hrho f f'
    (cone_same_polar x hx hinj hB rho hrho _ _ a b ha ha' hb hb' z h h')
  subst hf
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (cone_same_index x hx hinj hB rho hrho _ a b ha hb' hab z h h').elim
  · exact hab
  · exact (cone_same_index x hx hinj hB rho hrho _ b a hb ha' hab z h' h).elim

end FanCones

end Tammes15
