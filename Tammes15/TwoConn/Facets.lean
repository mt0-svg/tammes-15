import Tammes15.TwoConn.Hull

/-!
# Facets of the hull

Step S4 of the proof of Corollary twoconn by the convex hull (paper, Section 3, Corollary twoconn
and Lemma hull). The facets are the orbits of the face permutation of the angular rotation
`rho` of the hull graph. Each hull dart `d` has a supporting plane `{y | ⟪y, m⟫ = 1}` through
`x d.fst`, `x d.snd` and `x (rho.rot d).snd` (Lemma C, `hull_step`); its polar `facetPolar` is
unique, constant along the orbit (`facetPolar_face`, the facet is planar), every other point of
the plane lies strictly on the left of each side (`facetPolar_strict`), and the vertices of an
orbit are pairwise distinct (`facet_fst_injective`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace

namespace Tammes15

open scoped Classical

/-! ## Linear algebra in `E3` -/

/-- The triple product is invariant under cyclic shifts. -/
theorem inner_cross_cyc (a b c : E3) : ⟪cross b c, a⟫ = ⟪cross a b, c⟫ := by
  rw [real_inner_comm, inner_cross_perm, inner_cross_perm, real_inner_comm]

theorem cross_swap (a b : E3) : cross b a = -cross a b := by
  exact cross_anticomm_E3 b a

theorem inner_cross_cross (a b c d : E3) :
    ⟪cross a b, cross c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
    crossProduct, star_trivial]
  simp
  ring

/-- A vector orthogonal to three independent vectors is zero. -/
theorem eq_zero_of_inner_eq_zero3 (a b c y : E3) (h : ⟪cross a b, c⟫ ≠ 0) (ha : ⟪a, y⟫ = 0)
    (hb : ⟪b, y⟫ = 0) (hc : ⟪c, y⟫ = 0) : y = 0 := by
  have K := congrArg (fun w => ⟪y, w⟫) (cramer_smul a b c y)
  simp only [real_inner_smul_right, inner_add_right, real_inner_comm a y, real_inner_comm b y,
    real_inner_comm c y, ha, hb, hc, mul_zero, add_zero] at K
  have hyy : ⟪y, y⟫ = 0 := by
    rcases mul_eq_zero.mp K with h' | h'
    · exact absurd h' h
    · exact h'
  exact inner_self_eq_zero.mp hyy

/-- A vector orthogonal to `a` and `b` is a multiple of `cross a b`. -/
theorem exists_eq_smul_cross (a b y : E3) (h : cross a b ≠ 0) (ha : ⟪a, y⟫ = 0)
    (hb : ⟪b, y⟫ = 0) : ∃ t : ℝ, y = t • cross a b := by
  have hD : ⟪cross a b, cross a b⟫ ≠ 0 := fun h' => h (inner_self_eq_zero.mp h')
  have K := cramer_smul a b (cross a b) y
  have h1 : ⟪cross y b, cross a b⟫ = 0 := by
    rw [inner_cross_cross, real_inner_comm a y, ha, real_inner_comm b y, hb]
    ring
  have h2 : ⟪cross a y, cross a b⟫ = 0 := by
    rw [inner_cross_cross, real_inner_comm b y, hb, real_inner_comm a y, ha]
    ring
  rw [h1, h2, zero_smul, zero_smul, zero_add, zero_add] at K
  refine ⟨⟪cross a b, y⟫ / ⟪cross a b, cross a b⟫, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← K, smul_smul, inv_mul_cancel₀ hD, one_smul]

/-- Two planes `{⟪·, m₁⟫ = 1}` and `{⟪·, m₂⟫ = 1}` through `a` and `b`, the first through `p` and
the second through `q`, with `p` and `q` strictly on the left of `a b` and each below the other
plane, coincide. -/
theorem polar_eq_of_support (a b p q m₁ m₂ : E3) (ha₁ : ⟪a, m₁⟫ = 1) (hb₁ : ⟪b, m₁⟫ = 1)
    (ha₂ : ⟪a, m₂⟫ = 1) (hb₂ : ⟪b, m₂⟫ = 1) (hp₁ : ⟪p, m₁⟫ = 1) (hp₂ : ⟪p, m₂⟫ ≤ 1)
    (hq₂ : ⟪q, m₂⟫ = 1) (hq₁ : ⟪q, m₁⟫ ≤ 1) (hp : 0 < ⟪cross a b, p⟫)
    (hq : 0 < ⟪cross a b, q⟫) : m₁ = m₂ := by
  have hab : cross a b ≠ 0 := by
    intro h0
    rw [h0, inner_zero_left] at hp
    exact lt_irrefl 0 hp
  obtain ⟨t, ht⟩ := exists_eq_smul_cross a b (m₁ - m₂) hab
    (by rw [inner_sub_right, ha₁, ha₂, sub_self]) (by rw [inner_sub_right, hb₁, hb₂, sub_self])
  have hpt : ⟪p, m₁ - m₂⟫ = t * ⟪cross a b, p⟫ := by
    rw [ht, inner_smul_right, real_inner_comm]
  have hqt : ⟪q, m₁ - m₂⟫ = t * ⟪cross a b, q⟫ := by
    rw [ht, inner_smul_right, real_inner_comm]
  rw [inner_sub_right] at hpt hqt
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have ht1 : t ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith
  have : t = 0 := le_antisymm ht1 ht0
  rw [this, zero_smul] at ht
  exact sub_eq_zero.mp ht

/-! ## Face permutations of rotation systems -/

section RotSys

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem RotSys.rot_face_eq_symm (R : RotSys G) (d : G.Dart) : R.rot (R.face d) = d.symm := by
  simp [RotSys.face]

theorem RotSys.fst_face (R : RotSys G) (d : G.Dart) : (R.face d).fst = d.snd := by
  have h := R.rot_fst (R.face d)
  rw [R.rot_face_eq_symm] at h
  rw [← h, SimpleGraph.Dart.symm_toProd, Prod.fst_swap]

theorem RotSys.face_pow_succ (R : RotSys G) (d : G.Dart) (n : ℕ) :
    (R.face ^ (n + 1)) d = R.face ((R.face ^ n) d) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

theorem RotSys.fst_face_pow_succ (R : RotSys G) (d : G.Dart) (n : ℕ) :
    ((R.face ^ (n + 1)) d).fst = ((R.face ^ n) d).snd := by
  rw [R.face_pow_succ, R.fst_face]

/-- Two positions of an orbit below the period with the same dart are equal. -/
theorem RotSys.eq_of_face_pow_eq (R : RotSys G) (d : G.Dart) {i j : ℕ}
    (hi : i < Function.minimalPeriod R.face d) (hj : j < Function.minimalPeriod R.face d)
    (h : (R.face ^ i) d = (R.face ^ j) d) : i = j := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at h
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp h

end RotSys

/-! ## Facet planes -/

section Facets

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The corner of the hull rotation `rho` at a hull dart. -/
noncomputable def rcorner (x : V → E3) (rho : RotSys (hullGraph x)) (d : (hullGraph x).Dart) :
    ℝ :=
  ocorner (x d.fst) (x d.snd) (x (rho.rot d).snd)

/-- `m` is the polar of a facet plane at the dart `d`: the plane `{y | ⟪y, m⟫ = 1}` supports the
points and passes through `x d.fst`, `x d.snd` and `x (rho.rot d).snd`. -/
def IsFacetPolar (x : V → E3) (rho : RotSys (hullGraph x)) (d : (hullGraph x).Dart) (m : E3) :
    Prop :=
  (∀ z, ⟪x z, m⟫ ≤ 1) ∧ ⟪x d.fst, m⟫ = 1 ∧ ⟪x d.snd, m⟫ = 1 ∧ ⟪x (rho.rot d).snd, m⟫ = 1

/-- The polar of the facet plane at `d` (unique by `facetPolar_eq`). -/
noncomputable def facetPolar (x : V → E3) (rho : RotSys (hullGraph x))
    (d : (hullGraph x).Dart) : E3 :=
  if h : ∃ m, IsFacetPolar x rho d m then h.choose else 0

variable (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
  (hrho : IsAngular rho x)

include hx hinj hB hrho

/-- Lemma C (i): the successor of a hull dart turns counterclockwise. -/
theorem hull_det_pos (d : (hullGraph x).Dart) :
    0 < ⟪cross (x d.fst) (x d.snd), x (rho.rot d).snd⟫ :=
  (hull_step x hx hinj hB rho hrho d).1

theorem isFacetPolar_facetPolar (d : (hullGraph x).Dart) :
    IsFacetPolar x rho d (facetPolar x rho d) := by
  obtain ⟨-, m, h1, h2, h3, h4, -⟩ := hull_step x hx hinj hB rho hrho d
  have h : ∃ m, IsFacetPolar x rho d m := ⟨m, h1, h2, h3, h4⟩
  unfold facetPolar
  split_ifs
  exact h.choose_spec

theorem facetPolar_eq (d : (hullGraph x).Dart) (m : E3) (hm : IsFacetPolar x rho d m) :
    facetPolar x rho d = m := by
  have hP := isFacetPolar_facetPolar x hx hinj hB rho hrho d
  have hdet := hull_det_pos x hx hinj hB rho hrho d
  have h0 := eq_zero_of_inner_eq_zero3 (x d.fst) (x d.snd) (x (rho.rot d).snd)
    (facetPolar x rho d - m) hdet.ne' (by rw [inner_sub_right, hP.2.1, hm.2.1, sub_self])
    (by rw [inner_sub_right, hP.2.2.1, hm.2.2.1, sub_self])
    (by rw [inner_sub_right, hP.2.2.2, hm.2.2.2, sub_self])
  exact sub_eq_zero.mp h0

/-- D2: every point of the facet plane other than the ends of a side lies strictly on its left. -/
theorem facetPolar_strict (d : (hullGraph x).Dart) (z : V)
    (hz : ⟪x z, facetPolar x rho d⟫ = 1) (h₁ : z ≠ d.fst) (h₂ : z ≠ d.snd) :
    0 < ⟪cross (x d.fst) (x d.snd), x z⟫ := by
  obtain ⟨hdet, m, h1, h2, h3, h4, h5⟩ := hull_step x hx hinj hB rho hrho d
  have hm : facetPolar x rho d = m := facetPolar_eq x hx hinj hB rho hrho d m ⟨h1, h2, h3, h4⟩
  rw [hm] at hz
  by_cases h₃ : z = (rho.rot d).snd
  · rw [h₃]
    exact hdet
  · exact (h5 z hz h₁ h₂ h₃).1

/-- D1: the facet plane is constant along a face orbit. -/
theorem facetPolar_face (d : (hullGraph x).Dart) :
    facetPolar x rho (rho.face d) = facetPolar x rho d := by
  have h₁ := isFacetPolar_facetPolar x hx hinj hB rho hrho d
  have h₂ := isFacetPolar_facetPolar x hx hinj hB rho hrho (rho.face d)
  have hd₁ := hull_det_pos x hx hinj hB rho hrho d
  have hd₂ := hull_det_pos x hx hinj hB rho hrho (rho.face d)
  unfold IsFacetPolar at h₁ h₂
  rw [rho.fst_face, rho.rot_face_eq_symm, SimpleGraph.Dart.symm_toProd, Prod.snd_swap] at h₂
  rw [rho.fst_face, rho.rot_face_eq_symm, SimpleGraph.Dart.symm_toProd, Prod.snd_swap,
    inner_cross_cyc] at hd₂
  exact (polar_eq_of_support (x d.fst) (x d.snd) (x (rho.rot d).snd) (x (rho.face d).snd)
    (facetPolar x rho d) (facetPolar x rho (rho.face d)) h₁.2.1 h₁.2.2.1 h₂.2.2.2 h₂.2.1
    h₁.2.2.2 (h₂.1 _) h₂.2.2.1 (h₁.1 _) hd₁ hd₂).symm

theorem facetPolar_pow (d : (hullGraph x).Dart) (n : ℕ) :
    facetPolar x rho ((rho.face ^ n) d) = facetPolar x rho d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rho.face_pow_succ, facetPolar_face x hx hinj hB rho hrho, ih]

/-- The vertices of the facet of `d` lie on its plane. -/
theorem facet_fst_mem (d : (hullGraph x).Dart) (n : ℕ) :
    ⟪x ((rho.face ^ n) d).fst, facetPolar x rho d⟫ = 1 := by
  rw [← facetPolar_pow x hx hinj hB rho hrho d n]
  exact (isFacetPolar_facetPolar x hx hinj hB rho hrho _).2.1

theorem facet_snd_mem (d : (hullGraph x).Dart) (n : ℕ) :
    ⟪x ((rho.face ^ n) d).snd, facetPolar x rho d⟫ = 1 := by
  rw [← facetPolar_pow x hx hinj hB rho hrho d n]
  exact (isFacetPolar_facetPolar x hx hinj hB rho hrho _).2.2.1

/-- D3, the key step: two darts with one tail and one facet plane are equal. -/
theorem dart_eq_of_polar_eq (e f : (hullGraph x).Dart)
    (hP : facetPolar x rho e = facetPolar x rho f) (h : e.fst = f.fst) : e = f := by
  have hsnd : e.snd = f.snd := by
    by_contra hne
    have hfe : f.snd ≠ e.fst := by
      rw [h]
      exact fun h' => f.adj.ne h'.symm
    have hef : e.snd ≠ f.fst := by
      rw [← h]
      exact fun h' => e.adj.ne h'.symm
    have h₁ := facetPolar_strict x hx hinj hB rho hrho e f.snd
      (by rw [hP]; exact (isFacetPolar_facetPolar x hx hinj hB rho hrho f).2.2.1) hfe
      (Ne.symm hne)
    have h₂ := facetPolar_strict x hx hinj hB rho hrho f e.snd
      (by rw [← hP]; exact (isFacetPolar_facetPolar x hx hinj hB rho hrho e).2.2.1) hef hne
    rw [← h, ← inner_cross_cyc, cross_swap, inner_neg_left, inner_cross_cyc] at h₂
    linarith
  exact SimpleGraph.Dart.ext _ _ (Prod.ext h hsnd)

/-- D3: the vertices of a facet are pairwise distinct over one period. -/
theorem facet_fst_injective (d : (hullGraph x).Dart) {i j : ℕ}
    (hi : i < Function.minimalPeriod rho.face d) (hj : j < Function.minimalPeriod rho.face d)
    (h : ((rho.face ^ i) d).fst = ((rho.face ^ j) d).fst) : i = j :=
  rho.eq_of_face_pow_eq d hi hj (dart_eq_of_polar_eq x hx hinj hB rho hrho _ _
    (by rw [facetPolar_pow x hx hinj hB rho hrho, facetPolar_pow x hx hinj hB rho hrho]) h)

/-- A facet has at least three sides. -/
theorem facet_period_ge_three (d : (hullGraph x).Dart) :
    3 ≤ Function.minimalPeriod rho.face d :=
  face_period_ge_three rho x (hull_rot_pos x hx hinj hB rho hrho) d

end Facets

end Tammes15
