import Tammes15.FejesToth.Triangle

/-!
# Facets of the hull of a saturated set

Paper, proof of Proposition 8.3, steps (4) to (6), on the hull of Lemma 3.7 (TwoConn/Hull, Facets,
Excess, Euler). For a `c`-separated saturated family `x`: the plane of every facet is at distance
above `c` from the origin, so its circumradius is below `arccos c` (`facetPolar_norm_lt`, step (4));
every fan triangle of a facet then satisfies the triangle lemma, so a facet with `v` vertices has
angle sum at least `(v - 2) (π + 2θ)` (`facet_fan_bound`, step (5)); summing over the facets with the
corner sum `2π` per vertex and Euler's relation gives `(2|V| - 4) 2θ ≤ 4π`
(`hull_fan_count`, step (6)).
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification (PermutationCycle)
open Tammes15.Vendor.EM8.SquareAntiprismVerification (StrictSphericalPolygon PermutationOrbit
  orbitPermutationCycle sum_over_permutation_cycles sum_permutation_cycle_lengths cyclic_one_ne
  cyclic_two_ne crossVec)

namespace Tammes15.FejesToth

open scoped Classical

section Facets

variable {V : Type} [Fintype V] [DecidableEq V]
variable (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
  (hrho : IsAngular rho x)

include hx hinj hB hrho

/-- Step (4): the facet planes of a saturated family are at distance above `c` from the origin. -/
theorem facetPolar_norm_lt (c : ℝ) (hsat : ∀ u : E3, ‖u‖ = 1 → ∃ a, c < ⟪u, x a⟫)
    (d : (hullGraph x).Dart) : c * ‖facetPolar x rho d‖ < 1 := by
  have hP := isFacetPolar_facetPolar x hx hinj hB rho hrho d
  have hm0 : facetPolar x rho d ≠ 0 := by
    intro h
    have h1 := hP.2.1
    rw [h, inner_zero_right] at h1
    exact zero_ne_one h1
  have hnm : 0 < ‖facetPolar x rho d‖ := norm_pos_iff.mpr hm0
  obtain ⟨a, ha⟩ := hsat (‖facetPolar x rho d‖⁻¹ • facetPolar x rho d)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnm.ne'])
  rw [real_inner_smul_left, real_inner_comm (x a), lt_inv_mul_iff₀ hnm] at ha
  rw [mul_comm]
  exact ha.trans_le (hP.1 a)

/-- Step (5): a facet with `C.size + 1` vertices has angle sum at least `C.size - 1` times the angle
sum of the equilateral triangle of side `arccos c`. -/
theorem facet_fan_bound (c : ℝ) (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hsep : ∀ a b, a ≠ b → ⟪x a, x b⟫ ≤ c)
    (hsat : ∀ u : E3, ‖u‖ = 1 → ∃ a, c < ⟪u, x a⟫)
    (C : PermutationCycle rho.face) :
    ((C.size : ℝ) - 1) * (π + 2 * Complex.arg ⟨1 + 3 * c, (1 - c) * √(1 + 2 * c)⟩) ≤
      ∑ i, rcorner x rho (C.point i) := by
  set θ := Complex.arg ⟨1 + 3 * c, (1 - c) * √(1 + 2 * c)⟩ with hθ
  have hsize := cycle_size_ge_two x hx hinj hB rho hrho C
  have hinjC := cycle_fst_injective x hx hinj hB rho hrho C
  have hpol := cycle_polar x hx hinj hB rho hrho C
  have hsucc := cycle_fst_succ x rho C
  have hrot := cycle_rot x rho C
  -- the facet plane `⟪·, m⟫ = 1`, its unit normal `nf` and level `kf = ‖m‖⁻¹ > c`
  have hlt := facetPolar_norm_lt x hx hinj hB rho hrho c hsat (C.point 0)
  have hon : ∀ i, ⟪x (C.point i).fst, facetPolar x rho (C.point 0)⟫ = 1 := fun i => by
    rw [← hpol i]
    exact (isFacetPolar_facetPolar x hx hinj hB rho hrho (C.point i)).2.1
  set m := facetPolar x rho (C.point 0) with hm
  have hm0 : m ≠ 0 := by
    intro h
    have h1 := hon 0
    rw [h, inner_zero_right] at h1
    exact zero_ne_one h1
  have hnm : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hnf : ‖‖m‖⁻¹ • m‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnm.ne']
  have hk : ∀ i, ⟪‖m‖⁻¹ • m, x (C.point i).fst⟫ = ‖m‖⁻¹ := fun i => by
    rw [real_inner_smul_left, real_inner_comm, hon i, mul_one]
  have hck : c ≤ ‖m‖⁻¹ := by
    have h1 : c * ‖m‖ * ‖m‖⁻¹ = c := by field_simp
    calc c = c * ‖m‖ * ‖m‖⁻¹ := h1.symm
      _ ≤ 1 * ‖m‖⁻¹ := mul_le_mul_of_nonneg_right hlt.le (inv_nonneg.mpr hnm.le)
      _ = ‖m‖⁻¹ := one_mul _
  obtain ⟨size, point, pinj, step⟩ := C
  obtain ⟨n, rfl⟩ : ∃ n, size = n + 2 := ⟨size - 2, by simp only at hsize; omega⟩
  have hsupp : ∀ i j : Fin (n + 3), j ≠ i → j ≠ i + 1 →
      0 < ⟪cross (x (point i).fst) (x (point (i + 1)).fst), x (point j).fst⟫ := by
    intro i j hji hj1
    rw [hsucc i]
    refine facetPolar_strict x hx hinj hB rho hrho (point i) (point j).fst ?_ ?_ ?_
    · rw [hpol i, ← hpol j]
      exact (isFacetPolar_facetPolar x hx hinj hB rho hrho (point j)).2.1
    · exact fun h => hji (hinjC h)
    · rw [← hsucc i]
      exact fun h => hj1 (hinjC h)
  let Q : StrictSphericalPolygon n :=
    { vertex := fun i => x (point i).fst
      unit := fun i => hx _
      support := fun i j hji hj1 => by rw [crossVec_eq_cross]; exact hsupp i j hji hj1 }
  have hang : ∀ i, Q.angle i = rcorner x rho (point i) := by
    intro i
    have h1 : Q.angle i = ocorner (x (point i).fst) (x (point (i + 1)).fst) (x (point (i - 1)).fst) := by
      refine sphereVertexAngle_eq_ocorner _ _ _ (hx _) (hx _) (hx _) (hsupp i (i - 1) ?_ ?_)
      · intro h'
        exact cyclic_one_ne n (i - 1) (by rw [sub_add_cancel]; exact h'.symm)
      · intro h'
        exact cyclic_two_ne n (i - 1) (by rw [sub_add_cancel]; exact h'.symm)
    rw [h1, rcorner, hrot i, hsucc i, SimpleGraph.Dart.symm_toProd, Prod.snd_swap]
  -- each fan triangle satisfies the triangle lemma
  have hfan : ∀ i : Fin (n + 1),
      π + 2 * θ ≤ Q.fanCornerA i + Q.fanCornerB i + Q.fanCornerC i := by
    intro i
    have hi1 : (0 : Fin (n + 3)) ≠ i.castSucc.succ := (Fin.succ_ne_zero _).symm
    have hi2 : (0 : Fin (n + 3)) ≠ i.succ.succ := (Fin.succ_ne_zero _).symm
    have hi3 : i.castSucc.succ ≠ i.succ.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hD := hsupp i.castSucc.succ 0 hi1 (by
      rw [Tammes15.Vendor.EM8.SquareAntiprismVerification.StrictSphericalPolygon.fan_successor_index]
      exact hi2)
    rw [Tammes15.Vendor.EM8.SquareAntiprismVerification.StrictSphericalPolygon.fan_successor_index,
      inner_cross_cyc] at hD
    exact fejesToth_triangle _ _ _ (‖m‖⁻¹ • m) (hx _) (hx _) (hx _) hnf c ‖m‖⁻¹ hc hc1 hck
      (hk 0) (hk _) (hk _)
      (hsep _ _ fun h => hi1 (hinjC h)) (hsep _ _ fun h => hi3 (hinjC h))
      (hsep _ _ fun h => hi2 (hinjC h).symm) hD
  have hsum := Q.sum_fan_corners
  calc (((n + 2 : ℕ) : ℝ) - 1) * (π + 2 * θ) = ∑ _i : Fin (n + 1), (π + 2 * θ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ i, (Q.fanCornerA i + Q.fanCornerB i + Q.fanCornerC i) :=
        Finset.sum_le_sum fun i _ => hfan i
    _ = ∑ i, Q.angle i := hsum
    _ = ∑ i, rcorner x rho (point i) := Finset.sum_congr rfl fun i _ => hang i

/-- Step (6): the count of fan triangles, `Σ_f (v_f - 2) = 2|V| - 4`, in the form of a bound. -/
theorem hull_fan_count [Nonempty V] (θ : ℝ)
    (hf : ∀ C : PermutationCycle rho.face,
      ((C.size : ℝ) - 1) * (π + 2 * θ) ≤ ∑ i, rcorner x rho (C.point i)) :
    (2 * (Fintype.card V : ℝ) - 4) * (2 * θ) ≤ 4 * π := by
  have htot := hull_corner_total x hx hinj hB rho hrho
  rw [← sum_over_permutation_cycles rho.face (rcorner x rho)] at htot
  have hlen := sum_permutation_cycle_lengths rho.face
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hlen
  have heul := hull_euler x hx hinj hB rho hrho
  have hle : ∑ q : PermutationOrbit rho.face,
      (((orbitPermutationCycle rho.face q).size : ℝ) - 1) * (π + 2 * θ) ≤
      ∑ q : PermutationOrbit rho.face, ∑ i, rcorner x rho ((orbitPermutationCycle rho.face q).point i) :=
    Finset.sum_le_sum fun q _ => hf _
  have hlenR : ∑ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) + 1) =
      2 * ((hullGraph x).edgeFinset.card : ℝ) := by
    exact_mod_cast hlen
  have hF : ∑ q : PermutationOrbit rho.face,
      (((orbitPermutationCycle rho.face q).size : ℝ) - 1) * (π + 2 * θ) =
      (2 * ((hullGraph x).edgeFinset.card : ℝ) - 2 * rho.faceCount) * (π + 2 * θ) := by
    rw [← Finset.sum_mul, rho.faceCount_eq_card, ← hlenR]
    have : ∀ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) - 1) =
        (((orbitPermutationCycle rho.face q).size : ℝ) + 1) - 2 := fun q => by ring
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hF, htot] at hle
  have heulR : (Fintype.card V : ℝ) - (hullGraph x).edgeFinset.card + rho.faceCount = 2 := by
    exact_mod_cast heul
  have h2 : 2 * ((hullGraph x).edgeFinset.card : ℝ) - 2 * rho.faceCount =
      2 * Fintype.card V - 4 := by linarith
  rw [h2] at hle
  linarith

end Facets

end Tammes15.FejesToth
