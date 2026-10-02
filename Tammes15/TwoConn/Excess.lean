import Tammes15.TwoConn.Euler
import Tammes15.Vendor.EM8.PolygonExcess

/-!
# Positive excess of the facets and Euler's relation for the hull

Steps D5, D6 and Lemma F of the proof of Corollary twoconn by the convex hull (paper, Section 3,
Lemma hull and Corollary twoconn). A face cycle of the hull rotation `rho` is a strict
spherical polygon of the eight-point proof, whose angles are the corners of `rho`
(`facet_excess`, from `StrictSphericalPolygon.positive_excess`). The corners of `rho` at a vertex
sum to `2π` (`corner_sum`), so the excesses of all facets add up to `2π (V - E + F)`, which is
therefore positive (`hull_euler_pos`); with the genus bound and the parity of `V - E + F` this
gives `V - E + F = 2` for the hull (`hull_euler`).
-/

open Real InnerProductGeometry ComplexConjugate
open scoped RealInnerProductSpace
open Tammes15.Vendor.EM8.SquareAntiprismVerification (StrictSphericalPolygon crossVec
  sphereVertexAngle PermutationCycle PermutationOrbit orbitPermutationCycle
  sum_over_permutation_cycles sum_permutation_cycle_lengths cyclic_one_ne cyclic_two_ne
  sphereAngle sphereTangent projection_norm_cross)

namespace Tammes15

open scoped Classical
open Fin.NatCast

/-! ## Adapters to the eight-point spherical polygons -/

theorem crossVec_eq_cross (a b : E3) : crossVec a b = cross a b := by
  ext i
  fin_cases i <;> simp [crossVec, cross, crossProduct]

/-- The unoriented angle of the eight-point proof is the oriented corner when the turn is
counterclockwise. -/
theorem sphereVertexAngle_eq_ocorner (p q r : E3) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (h : 0 < ⟪cross p q, r⟫) : sphereVertexAngle p q r = ocorner p q r := by
  obtain ⟨h0, hπ⟩ := (ocorner_pos_lt_pi_iff p q r).mpr h
  obtain ⟨e, he, hpe⟩ := exists_unit_orthogonal p
  have hcos : Real.cos (ocorner p q r) = ⟪tdir p q, tdir p r⟫ / (‖tdir p q‖ * ‖tdir p r‖) := by
    set w := conj (tcoord p e q) * tcoord p e r with hw
    have hw0 : w ≠ 0 := by
      intro h'
      have h'' : ocorner p q r = 0 := by
        rw [ocorner_eq_arg p e q r hp he hpe, ← hw, h', Complex.arg_zero]
        exact toIcoMod_apply_left _ _
      linarith
    have hre : w.re = ⟪tdir p q, tdir p r⟫ := by
      rw [hw, inner_tdir_frame p e q r hp he hpe]
      simp [tcoord, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hnorm : ‖w‖ = ‖tdir p q‖ * ‖tdir p r‖ := by
      rw [hw, norm_mul, Complex.norm_conj, norm_tdir_eq_norm_tcoord p e q hp he hpe,
        norm_tdir_eq_norm_tcoord p e r hp he hpe]
    rw [ocorner_eq_arg p e q r hp he hpe, ← hw, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul,
      Real.cos_sub_int_mul_two_pi, Complex.cos_arg hw0, hre, hnorm]
  have htq : q - ⟪p, q⟫ • p = tdir p q := rfl
  have htr : r - ⟪p, r⟫ • p = tdir p r := rfl
  have hnq : ‖crossVec p q‖ = ‖tdir p q‖ := by rw [← projection_norm_cross p q hp hq, htq]
  have hnr : ‖crossVec p r‖ = ‖tdir p r‖ := by rw [← projection_norm_cross p r hp hr, htr]
  have hc : ‖tdir p q‖⁻¹ * (‖tdir p r‖⁻¹ * ⟪tdir p q, tdir p r⟫) = Real.cos (ocorner p q r) := by
    rw [hcos]
    ring
  unfold sphereVertexAngle sphereAngle sphereTangent
  rw [htq, htr, hnq, hnr, real_inner_smul_left, real_inner_smul_right, hc,
    Real.arccos_cos h0.le hπ.le]

/-- Positive excess of a strictly convex spherical polygon, in terms of `ocorner`. -/
theorem excess_of_support (n : ℕ) (q : Fin (n + 3) → E3) (hq : ∀ i, ‖q i‖ = 1)
    (hsupp : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ⟪cross (q i) (q (i + 1)), q j⟫) :
    ((n : ℝ) + 1) * π < ∑ i, ocorner (q i) (q (i + 1)) (q (i - 1)) := by
  let Q : StrictSphericalPolygon n :=
    { vertex := q
      unit := hq
      support := fun i j hji hj1 => by rw [crossVec_eq_cross]; exact hsupp i j hji hj1 }
  have h := Q.positive_excess
  have hang : ∀ i, Q.angle i = ocorner (q i) (q (i + 1)) (q (i - 1)) := by
    intro i
    refine sphereVertexAngle_eq_ocorner _ _ _ (hq i) (hq (i + 1)) (hq (i - 1)) (hsupp i (i - 1) ?_ ?_)
    · intro h'
      exact cyclic_one_ne n (i - 1) (by rw [sub_add_cancel]; exact h'.symm)
    · intro h'
      exact cyclic_two_ne n (i - 1) (by rw [sub_add_cancel]; exact h'.symm)
  simpa only [hang] using h

/-! ## Cycles of a permutation -/

theorem cycle_pow_point {α : Type*} {e : Equiv.Perm α} (C : PermutationCycle e) (k : ℕ) :
    (e ^ k) (C.point 0) = C.point (k : Fin (C.size + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, C.step, Nat.cast_succ]

/-! ## Face cycles of the hull rotation -/

section Excess

variable {V : Type} [Fintype V] [DecidableEq V]
variable (x : V → E3) (hx : ∀ v, ‖x v‖ = 1) (hinj : Function.Injective x)
  (hB : ∀ e : E3, e ≠ 0 → ∃ a, 0 < ⟪x a, e⟫) (rho : RotSys (hullGraph x))
  (hrho : IsAngular rho x)

theorem cycle_rot (C : PermutationCycle rho.face) (i : Fin (C.size + 1)) :
    rho.rot (C.point i) = (C.point (i - 1)).symm := by
  have h := C.step (i - 1)
  rw [sub_add_cancel] at h
  rw [← h, rho.rot_face_eq_symm]

theorem cycle_fst_succ (C : PermutationCycle rho.face) (i : Fin (C.size + 1)) :
    (C.point (i + 1)).fst = (C.point i).snd := by
  rw [← C.step i, rho.fst_face]

include hx hinj hB hrho

theorem cycle_polar (C : PermutationCycle rho.face) (i : Fin (C.size + 1)) :
    facetPolar x rho (C.point i) = facetPolar x rho (C.point 0) := by
  have h := cycle_pow_point C i.val
  rw [Fin.cast_val_eq_self] at h
  rw [← h, facetPolar_pow x hx hinj hB rho hrho]

/-- D3 for a face cycle: its vertices are pairwise distinct. -/
theorem cycle_fst_injective (C : PermutationCycle rho.face) :
    Function.Injective (fun i => (C.point i).fst) := by
  intro i j h
  apply C.injective
  exact dart_eq_of_polar_eq x hx hinj hB rho hrho _ _
    ((cycle_polar x hx hinj hB rho hrho C i).trans (cycle_polar x hx hinj hB rho hrho C j).symm) h

theorem cycle_size_ge_two (C : PermutationCycle rho.face) : 2 ≤ C.size := by
  have hper : Function.IsPeriodicPt rho.face (C.size + 1) (C.point 0) := by
    have h := cycle_pow_point C (C.size + 1)
    rw [Fin.natCast_self, Equiv.Perm.coe_pow] at h
    exact h
  have h1 := hper.minimalPeriod_le (Nat.succ_pos _)
  have h2 := facet_period_ge_three x hx hinj hB rho hrho (C.point 0)
  omega

/-- D5: the corners of a facet exceed those of a Euclidean polygon. -/
theorem facet_excess (C : PermutationCycle rho.face) :
    ((C.size : ℝ) - 1) * π < ∑ i, rcorner x rho (C.point i) := by
  have hsize := cycle_size_ge_two x hx hinj hB rho hrho C
  have hinjC := cycle_fst_injective x hx hinj hB rho hrho C
  have hpol := cycle_polar x hx hinj hB rho hrho C
  have hsucc := cycle_fst_succ x rho C
  have hrot := cycle_rot x rho C
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
  have h := excess_of_support n (fun i => x (point i).fst) (fun i => hx _) hsupp
  have hr : ∀ i : Fin (n + 3), rcorner x rho (point i) =
      ocorner (x (point i).fst) (x (point (i + 1)).fst) (x (point (i - 1)).fst) := by
    intro i
    rw [rcorner, hrot i, hsucc i, SimpleGraph.Dart.symm_toProd, Prod.snd_swap]
  simp only [hr]
  push_cast
  linarith

omit hrho in
/-- Two distinct hull neighbours at every vertex. -/
theorem hull_two_nbrs (v : V) : ∃ a b, a ≠ b ∧ (hullGraph x).Adj v a ∧ (hullGraph x).Adj v b := by
  have h := hull_three_le_degree x hx hinj hB v
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < ((hullGraph x).neighborFinset v).card by omega)
  exact ⟨a, b, hab, (SimpleGraph.mem_neighborFinset _ _ _).mp ha,
    (SimpleGraph.mem_neighborFinset _ _ _).mp hb⟩

/-- D6: the corners of the hull rotation sum to `2π` per vertex. -/
theorem hull_corner_total : ∑ d, rcorner x rho d = 2 * π * Fintype.card V := by
  rw [← Finset.sum_fiberwise Finset.univ (fun d : (hullGraph x).Dart => d.fst)]
  have hv : ∀ v : V, ∑ d ∈ Finset.univ.filter (fun d : (hullGraph x).Dart => d.fst = v),
      rcorner x rho d = 2 * π := by
    intro v
    rw [← corner_sum x hx (hull_distinctDirs x hx hinj hB) rho hrho v
      (hull_two_nbrs x hx hinj hB v)]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    rw [rcorner, hd.2]
  rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- D6 and D5: `V - E + F > 0` for the hull. -/
theorem hull_euler_pos [Nonempty V] :
    0 < (Fintype.card V : ℤ) - (hullGraph x).edgeFinset.card + rho.faceCount := by
  have htot := hull_corner_total x hx hinj hB rho hrho
  rw [← sum_over_permutation_cycles rho.face (rcorner x rho)] at htot
  have hlen := sum_permutation_cycle_lengths rho.face
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hlen
  have hne : (Finset.univ : Finset (PermutationOrbit rho.face)).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨a, -, -, ha, -⟩ := hull_two_nbrs x hx hinj hB v
    exact ⟨Quotient.mk _ ⟨(v, a), ha⟩, Finset.mem_univ _⟩
  have hlt : ∑ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) - 1) * π <
      ∑ q : PermutationOrbit rho.face, ∑ i, rcorner x rho ((orbitPermutationCycle rho.face q).point i) :=
    Finset.sum_lt_sum_of_nonempty hne fun q _ => facet_excess x hx hinj hB rho hrho _
  have hlenR : ∑ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) + 1) =
      2 * ((hullGraph x).edgeFinset.card : ℝ) := by
    exact_mod_cast hlen
  have hF : ∑ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) - 1) * π =
      (2 * ((hullGraph x).edgeFinset.card : ℝ) - 2 * rho.faceCount) * π := by
    rw [← Finset.sum_mul, rho.faceCount_eq_card, ← hlenR]
    have : ∀ q : PermutationOrbit rho.face, (((orbitPermutationCycle rho.face q).size : ℝ) - 1) =
        (((orbitPermutationCycle rho.face q).size : ℝ) + 1) - 2 := fun q => by ring
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hF, htot] at hlt
  have hpi := Real.pi_pos
  have key : ((hullGraph x).edgeFinset.card : ℝ) - rho.faceCount < Fintype.card V := by
    nlinarith
  have : ((hullGraph x).edgeFinset.card : ℤ) - rho.faceCount < Fintype.card V := by
    exact_mod_cast key
  omega

/-- Lemma F: Euler's relation for the hull. -/
theorem hull_euler [Nonempty V] :
    (Fintype.card V : ℤ) - (hullGraph x).edgeFinset.card + rho.faceCount = 2 := by
  have hpos := hull_euler_pos x hx hinj hB rho hrho
  have hle := rotSys_euler_le rho (hull_connected x hx hinj hB)
    (fun v => let ⟨a, _, _, ha, _⟩ := hull_two_nbrs x hx hinj hB v; ⟨a, ha⟩)
  obtain ⟨k, hk⟩ := rotSys_euler_even rho
    (fun v => let ⟨a, _, _, ha, _⟩ := hull_two_nbrs x hx hinj hB v; ⟨a, ha⟩)
  omega

end Excess

end Tammes15
