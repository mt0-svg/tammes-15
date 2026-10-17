/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
import Tammes15.Classification
import Tammes15.PaperSteps.Automorphisms
import Tammes15.PaperSteps.Isometric

/-!
# The maximal configurations up to rotation, their contacts and their contact graphs

`classification_count_of_enum_killed`, from D2 and D3, and `classification_count_of_enum_progTreesDom`,
from the hypotheses of `conjecture_of_enum_progTreesDom`: for the root `u` of the quintic and
fifteen unit vectors `x` at pairwise angle at least `arccos u`,

* `x` is, after relabelling, `s R C1` or `s R C3` with `s = ±1` and `R` a rotation; each of `C1`,
  `C3`, `-C1`, `-C3` is such a configuration, and no rotation with a relabelling maps one of them
  onto another;
* exactly thirty pairs of points of `x` are at angle `arccos u`, and every point of `x` is at angle
  `arccos u` from three, four or five others;
* the contact graph of `x` at inner product `u` is isomorphic to that of `C1` or to that of `C3`,
  and these two are not isomorphic.

The first item follows from `classification_of_enum_killed`, the determinant `±1` of an orthogonal
map and `det (-R) = -det R` in dimension three. For the four classes: an orthogonal map `O` with
`O C1 = C3` up to labels is excluded by `frames_not_isometric`, and one with `O q = q` has
determinant one (`orthogonal_det`), so `-R` with `R` a rotation never maps `q` onto itself. A
linear isometry and a relabelling give an isomorphism of contact graphs, and the contact graphs of
`C1` and `C3` are the graphs of their thirty listed pairs (`contactGraph_C1`, `contactGraph_C3`),
whose pairs and degrees are counted by `decide`.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.PaperSteps

open Tammes15 Attained

/-! ## Determinants of orthogonal maps -/

theorem abs_det_linearIsometryEquiv (R : E3 ≃ₗᵢ[ℝ] E3) :
    |LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3)| = 1 := by
  rw [← LinearMap.normDet_eq_abs_det]
  exact LinearIsometry.normDet_eq_one R.toLinearIsometry

theorem det_trans_neg (R : E3 ≃ₗᵢ[ℝ] E3) :
    LinearMap.det ((R.trans (LinearIsometryEquiv.neg ℝ)).toLinearEquiv : E3 →ₗ[ℝ] E3) =
      -LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) := by
  have h : ((R.trans (LinearIsometryEquiv.neg ℝ)).toLinearEquiv : E3 →ₗ[ℝ] E3) =
      (-1 : ℝ) • (R.toLinearEquiv : E3 →ₗ[ℝ] E3) := by
    ext v i
    simp
  rw [h, LinearMap.det_smul, finrank_euclideanSpace_fin]
  ring

/-- An orthogonal image of a configuration is `±` a rotation image. -/
theorem exists_rotation (y x : Fin 15 → E3) (R : E3 ≃ₗᵢ[ℝ] E3) (h : ∀ i, x i = R (y i)) :
    ∃ s ∈ ({1, -1} : Set ℝ), ∃ R' : E3 ≃ₗᵢ[ℝ] E3,
      LinearMap.det (R'.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧ ∀ i, x i = s • R' (y i) := by
  rcases (abs_eq zero_le_one).mp (abs_det_linearIsometryEquiv R) with h1 | h1
  · exact ⟨1, Or.inl rfl, R, h1, fun i => by rw [one_smul, h]⟩
  · refine ⟨-1, Or.inr rfl, R.trans (LinearIsometryEquiv.neg ℝ), ?_, fun i => ?_⟩
    · rw [det_trans_neg, h1, neg_neg]
    · rw [h]
      simp

/-! ## The four classes -/

theorem frame_unit {q : Frame} (hq : q ∈ ({frameC1, frameC3} : Set Frame)) (i : Fin 15) :
    ‖q.p i‖ = 1 := by
  rcases hq with rfl | rfl
  · exact frameC1_unit i
  · exact frameC3_unit i

theorem frame_sep {q : Frame} (hq : q ∈ ({frameC1, frameC3} : Set Frame)) :
    ∀ i j, i ≠ j → ⟪q.p i, q.p j⟫ ≤ uR := by
  rcases hq with rfl | rfl
  · exact frameC1_sep
  · exact frameC3_sep

/-- `±C1` and `±C3` are fifteen unit vectors at pairwise angle at least `arccos uR`. -/
theorem frame_smul_maximal {q : Frame} (hq : q ∈ ({frameC1, frameC3} : Set Frame)) {s : ℝ}
    (hs : s ∈ ({1, -1} : Set ℝ)) :
    (∀ i, ‖s • q.p i‖ = 1) ∧ ∀ i j, i ≠ j → arccos uR ≤ angle (s • q.p i) (s • q.p j) := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨fun i => by rw [norm_smul, Real.norm_eq_abs, habs, one_mul, frame_unit hq], ?_⟩
  intro i j hij
  rw [angle_smul_smul hs0]
  exact Nonunique.angle_ge_of_inner_le q.p uR (frame_unit hq) (frame_sep hq) i j hij

/-- An orthogonal map that maps one of `C1`, `C3` onto one of them, up to labels, maps it onto
itself and has determinant one. -/
theorem frame_map_eq {q q' : Frame} (hq : q ∈ ({frameC1, frameC3} : Set Frame))
    (hq' : q' ∈ ({frameC1, frameC3} : Set Frame)) (O : E3 ≃ₗᵢ[ℝ] E3) (σ : Fin 15 ≃ Fin 15)
    (hO : ∀ i, O (q.p i) = q'.p (σ i)) :
    q = q' ∧ LinearMap.det (O.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
  have himg : O '' Set.range q.p = Set.range q'.p := by
    rw [← Set.range_comp]
    have : (O ∘ q.p) = q'.p ∘ σ := funext hO
    rw [this, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact ⟨rfl, orthogonal_det O (Or.inl himg)⟩
  · exact absurd ⟨O.toIsometryEquiv, himg⟩ frames_not_isometric
  · refine absurd ⟨O.symm.toIsometryEquiv, ?_⟩ frames_not_isometric
    change O.symm '' Set.range frameC1.p = Set.range frameC3.p
    rw [← himg, ← Set.image_comp]
    simp
  · exact ⟨rfl, orthogonal_det O (Or.inr himg)⟩

/-- No rotation with a relabelling maps one of `C1`, `C3`, `-C1`, `-C3` onto another. -/
theorem rotation_classes_distinct {q q' : Frame} (hq : q ∈ ({frameC1, frameC3} : Set Frame))
    (hq' : q' ∈ ({frameC1, frameC3} : Set Frame)) {s s' : ℝ} (hs : s ∈ ({1, -1} : Set ℝ))
    (hs' : s' ∈ ({1, -1} : Set ℝ)) (σ : Fin 15 ≃ Fin 15) (R : E3 ≃ₗᵢ[ℝ] E3)
    (hR : LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1)
    (h : ∀ i, s' • q'.p (σ i) = R (s • q.p i)) : q = q' ∧ s = s' := by
  have hneg : ∀ i, (R.trans (LinearIsometryEquiv.neg ℝ)) (q.p i) = -R (q.p i) := fun i => by
    simp
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
  · refine ⟨(frame_map_eq hq hq' R σ fun i => ?_).1, rfl⟩
    simpa using (h i).symm
  · exfalso
    have h1 := (frame_map_eq hq hq' (R.trans (LinearIsometryEquiv.neg ℝ)) σ fun i => by
      rw [hneg, ← one_smul ℝ (q.p i), ← h i]
      simp).2
    rw [det_trans_neg, hR] at h1
    norm_num at h1
  · exfalso
    have h1 := (frame_map_eq hq hq' (R.trans (LinearIsometryEquiv.neg ℝ)) σ fun i => by
      rw [hneg]
      have := h i
      rw [one_smul, neg_one_smul, map_neg] at this
      rw [this]).2
    rw [det_trans_neg, hR] at h1
    norm_num at h1
  · refine ⟨(frame_map_eq hq hq' R σ fun i => ?_).1, rfl⟩
    have := h i
    rw [neg_one_smul, neg_one_smul, map_neg, neg_inj] at this
    exact this.symm

/-! ## Contact graphs and contacts -/

/-- Unit vectors are at angle `arccos u` exactly when their inner product is `u`. -/
theorem angle_eq_arccos_iff {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {u : ℝ} (hu1 : -1 ≤ u)
    (hu2 : u ≤ 1) : angle a b = arccos u ↔ ⟪a, b⟫ = u := by
  have h1 : angle a b = arccos ⟪a, b⟫ := by
    rw [InnerProductGeometry.angle, ha, hb, mul_one, div_one]
  have hab := abs_real_inner_le_norm a b
  rw [ha, hb, mul_one] at hab
  rw [h1]
  exact arccos_inj (abs_le.mp hab).1 (abs_le.mp hab).2 hu1 hu2

/-- A linear isometry and a relabelling give an isomorphism of contact graphs. -/
theorem nonempty_iso_of_map (x y : Fin 15 → E3) (σ : Fin 15 ≃ Fin 15) (R : E3 ≃ₗᵢ[ℝ] E3)
    (h : ∀ i, x i = R (y (σ i))) (c : ℝ) :
    Nonempty (Nonunique.contactGraph x c ≃g Nonunique.contactGraph y c) := by
  refine ⟨⟨σ, fun {a b} => ?_⟩⟩
  change (σ a ≠ σ b ∧ ⟪y (σ a), y (σ b)⟫ = c) ↔ (a ≠ b ∧ ⟪x a, x b⟫ = c)
  rw [h a, h b, LinearIsometryEquiv.inner_map_map, σ.injective.ne_iff]

section Count

variable {n : ℕ}

/-- The pairs `i < j` of adjacent vertices are as many as the edges. -/
theorem ncard_lt_adj (G : SimpleGraph (Fin n)) :
    {ij : Fin n × Fin n | ij.1 < ij.2 ∧ G.Adj ij.1 ij.2}.ncard = G.edgeSet.ncard := by
  have himg : (fun ij : Fin n × Fin n => s(ij.1, ij.2)) ''
      {ij : Fin n × Fin n | ij.1 < ij.2 ∧ G.Adj ij.1 ij.2} = G.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [Set.mem_image, Set.mem_ofPred_eq, Prod.exists, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨c, d, ⟨-, hcd⟩, he⟩
        rw [← SimpleGraph.mem_edgeSet, ← he]
        exact hcd
      · intro hab
        rcases lt_or_gt_of_ne (G.ne_of_adj hab) with hlt | hlt
        · exact ⟨a, b, ⟨hlt, hab⟩, rfl⟩
        · exact ⟨b, a, ⟨hlt, hab.symm⟩, Sym2.eq_swap⟩
  rw [← himg, Set.InjOn.ncard_image]
  rintro ⟨a, b⟩ ⟨hab, -⟩ ⟨c, d⟩ ⟨hcd, -⟩ he
  simp only [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd (hab.trans hcd) (lt_irrefl _)

theorem ncard_edgeSet_iso {G H : SimpleGraph (Fin n)} (φ : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr φ.mapEdgeSet

theorem ncard_neighborSet_iso {G H : SimpleGraph (Fin n)} (φ : G ≃g H) (v : Fin n) :
    (G.neighborSet v).ncard = (H.neighborSet (φ v)).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (φ.mapNeighborSet v)

end Count

theorem listGraph_S1_pairs :
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S1).Adj ij.1 ij.2}.ncard =
      30 := by
  rw [show {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S1).Adj ij.1 ij.2} =
      ↑(Finset.univ.filter fun ij : Fin 15 × Fin 15 =>
        ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S1).Adj ij.1 ij.2) by ext; simp,
    Set.ncard_coe_finset]
  decide

theorem listGraph_S3_pairs :
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S3).Adj ij.1 ij.2}.ncard =
      30 := by
  rw [show {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S3).Adj ij.1 ij.2} =
      ↑(Finset.univ.filter fun ij : Fin 15 × Fin 15 =>
        ij.1 < ij.2 ∧ (Nonunique.listGraph Nonunique.S3).Adj ij.1 ij.2) by ext; simp,
    Set.ncard_coe_finset]
  decide

theorem neighborSet_eq_filter (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj] (a : Fin 15) :
    G.neighborSet a = ↑(Finset.univ.filter (G.Adj a)) := by
  ext; simp

theorem listGraph_S1_degrees : ∀ a, 3 ≤ ((Nonunique.listGraph Nonunique.S1).neighborSet a).ncard ∧
    ((Nonunique.listGraph Nonunique.S1).neighborSet a).ncard ≤ 5 := by
  intro a
  rw [neighborSet_eq_filter, Set.ncard_coe_finset]
  revert a
  decide

theorem listGraph_S3_degrees : ∀ a, 3 ≤ ((Nonunique.listGraph Nonunique.S3).neighborSet a).ncard ∧
    ((Nonunique.listGraph Nonunique.S3).neighborSet a).ncard ≤ 5 := by
  intro a
  rw [neighborSet_eq_filter, Set.ncard_coe_finset]
  revert a
  decide

/-- The contacts of unit vectors whose contact graph is isomorphic to a graph `G` with thirty
edges and degrees three to five. -/
theorem contacts_of_iso (x : Fin 15 → E3) (hx : ∀ i, ‖x i‖ = 1) {u : ℝ} (hu1 : -1 ≤ u)
    (hu2 : u ≤ 1) {G : SimpleGraph (Fin 15)} (φ : Nonunique.contactGraph x u ≃g G)
    (hG : {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ G.Adj ij.1 ij.2}.ncard = 30)
    (hdeg : ∀ a, 3 ≤ (G.neighborSet a).ncard ∧ (G.neighborSet a).ncard ≤ 5) :
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos u}.ncard = 30 ∧
      ∀ i, 3 ≤ {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ∧
        {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ≤ 5 := by
  have hpairs : {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos u} =
      {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ (Nonunique.contactGraph x u).Adj ij.1 ij.2} := by
    ext ij
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hlt, ha⟩
      exact ⟨hlt, ne_of_lt hlt, (angle_eq_arccos_iff (hx _) (hx _) hu1 hu2).mp ha⟩
    · rintro ⟨hlt, -, hi⟩
      exact ⟨hlt, (angle_eq_arccos_iff (hx _) (hx _) hu1 hu2).mpr hi⟩
  have hnbr : ∀ i, {j | j ≠ i ∧ angle (x i) (x j) = arccos u} =
      (Nonunique.contactGraph x u).neighborSet i := by
    intro i
    ext j
    simp only [Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨hne, ha⟩
      exact ⟨Ne.symm hne, (angle_eq_arccos_iff (hx _) (hx _) hu1 hu2).mp ha⟩
    · rintro ⟨hne, hi⟩
      exact ⟨Ne.symm hne, (angle_eq_arccos_iff (hx _) (hx _) hu1 hu2).mpr hi⟩
  refine ⟨?_, fun i => ?_⟩
  · rw [hpairs, ncard_lt_adj, ncard_edgeSet_iso φ, ← ncard_lt_adj, hG]
  · rw [hnbr, ncard_neighborSet_iso φ]
    exact hdeg (φ i)

/-! ## The second and third sentences of the classification -/

/-- The count up to rotation, the contacts and the contact graphs of a configuration that is an
orthogonal image of `C1` or `C3` after relabelling, for the root `u` of the quintic. -/
theorem classification_count_core (u : ℝ) (hu1 : 1 / 2 < u) (hu2 : u < 7 / 10)
    (hu0 : quintic u = 0) (x : Fin 15 → E3) (hx : ∀ i, ‖x i‖ = 1)
    (hcl : ∃ q ∈ ({frameC1, frameC3} : Set Frame), ∃ σ : Fin 15 ≃ Fin 15,
      ∃ R : E3 ≃ₗᵢ[ℝ] E3, ∀ i, x i = R (q.p (σ i))) :
    (∃ q ∈ ({frameC1, frameC3} : Set Frame), ∃ s ∈ ({1, -1} : Set ℝ),
      ∃ σ : Fin 15 ≃ Fin 15, ∃ R : E3 ≃ₗᵢ[ℝ] E3, LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
        ∀ i, x i = s • R (q.p (σ i))) ∧
    (∀ q ∈ ({frameC1, frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      (∀ i, ‖s • q.p i‖ = 1) ∧ ∀ i j, i ≠ j → arccos u ≤ angle (s • q.p i) (s • q.p j)) ∧
    (∀ q ∈ ({frameC1, frameC3} : Set Frame),
      ∀ q' ∈ ({frameC1, frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      ∀ s' ∈ ({1, -1} : Set ℝ), ∀ σ : Fin 15 ≃ Fin 15, ∀ R : E3 ≃ₗᵢ[ℝ] E3,
      LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 → (∀ i, s' • q'.p (σ i) = R (s • q.p i)) →
        q = q' ∧ s = s') ∧
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos u}.ncard = 30 ∧
    (∀ i, 3 ≤ {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ∧
      {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ≤ 5) ∧
    (Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph frameC1.p u) ∨
      Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph frameC3.p u)) ∧
    IsEmpty (Nonunique.contactGraph frameC1.p u ≃g Nonunique.contactGraph frameC3.p u) := by
  have huR : uR = u := existsUnique_root.unique
    ⟨(bounds_of_mem uR uR_spec.1).1, (bounds_of_mem uR uR_spec.1).2, uR_spec.2⟩ ⟨hu1, hu2, hu0⟩
  subst huR
  have hu1' : -1 ≤ uR := by linarith
  have hu2' : uR ≤ 1 := by linarith
  obtain ⟨q, hq, σ, R, hR⟩ := hcl
  obtain ⟨φ⟩ := nonempty_iso_of_map x q.p σ R hR uR
  have hcontacts : {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos uR}.ncard = 30 ∧
      ∀ i, 3 ≤ {j | j ≠ i ∧ angle (x i) (x j) = arccos uR}.ncard ∧
        {j | j ≠ i ∧ angle (x i) (x j) = arccos uR}.ncard ≤ 5 := by
    rcases hq with rfl | rfl
    · exact contacts_of_iso x hx hu1' hu2' φ (by rw [Nonunique.contactGraph_C1]; exact listGraph_S1_pairs)
        (by rw [Nonunique.contactGraph_C1]; exact listGraph_S1_degrees)
    · exact contacts_of_iso x hx hu1' hu2' φ (by rw [Nonunique.contactGraph_C3]; exact listGraph_S3_pairs)
        (by rw [Nonunique.contactGraph_C3]; exact listGraph_S3_degrees)
  refine ⟨?_, fun q hq s hs => frame_smul_maximal hq hs,
    fun q hq q' hq' s hs s' hs' σ R hR h => rotation_classes_distinct hq hq' hs hs' σ R hR h,
    hcontacts.1, hcontacts.2, ?_, Nonunique.frames_not_iso⟩
  · obtain ⟨s, hs, R', hR', h⟩ := exists_rotation (fun i => q.p (σ i)) x R hR
    exact ⟨q, hq, s, hs, σ, R', hR', h⟩
  · rcases hq with rfl | rfl
    · exact Or.inl ⟨φ⟩
    · exact Or.inr ⟨φ⟩

end Tammes15.PaperSteps

namespace Tammes15

open Attained

/-- The second and third sentences of the classification, from D2 and D3: up to rotation and
relabelling a maximal configuration is one of `C1`, `C3`, `-C1`, `-C3`, which are maximal and
pairwise not related by a rotation; it has exactly thirty contacts, three to five at each point; its
contact graph is that of `C1` or that of `C3`, which are not isomorphic. -/
theorem classification_count_of_enum_killed (L : Set PlaneGraph) (h2 : EnumComplete L)
    (h3 : Killed L {Attained.frameC1, Attained.frameC3}) (u : ℝ) (hu1 : 1 / 2 < u)
    (hu2 : u < 7 / 10) (hu0 : quintic u = 0) (x : Fin 15 → E3) (hx : ∀ i, ‖x i‖ = 1)
    (hsep : ∀ i j, i ≠ j → arccos u ≤ angle (x i) (x j)) :
    -- up to rotation and relabelling, `x` is one of `C1`, `C3`, `-C1`, `-C3`
    (∃ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∃ s ∈ ({1, -1} : Set ℝ),
      ∃ σ : Fin 15 ≃ Fin 15, ∃ R : E3 ≃ₗᵢ[ℝ] E3, LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
        ∀ i, x i = s • R (q.p (σ i))) ∧
    -- these four are maximal configurations
    (∀ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      (∀ i, ‖s • q.p i‖ = 1) ∧ ∀ i j, i ≠ j → arccos u ≤ angle (s • q.p i) (s • q.p j)) ∧
    -- and no rotation and relabelling relates two of them
    (∀ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame),
      ∀ q' ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      ∀ s' ∈ ({1, -1} : Set ℝ), ∀ σ : Fin 15 ≃ Fin 15, ∀ R : E3 ≃ₗᵢ[ℝ] E3,
      LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 → (∀ i, s' • q'.p (σ i) = R (s • q.p i)) →
        q = q' ∧ s = s') ∧
    -- exactly thirty pairs of points of `x` are at distance `arccos u`
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos u}.ncard = 30 ∧
    -- every point of `x` is at distance `arccos u` from three, four or five others
    (∀ i, 3 ≤ {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ∧
      {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ≤ 5) ∧
    -- the contact graph of `x` is that of `C1` or that of `C3`, and these two are not isomorphic
    (Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph Attained.frameC1.p u) ∨
      Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph Attained.frameC3.p u)) ∧
    IsEmpty (Nonunique.contactGraph Attained.frameC1.p u ≃g Nonunique.contactGraph Attained.frameC3.p u) :=
  PaperSteps.classification_count_core u hu1 hu2 hu0 x hx
    (classification_of_enum_killed L h2 h3 u hu1 hu2 hu0 x hx hsep)

/-- `classification_count_of_enum_killed` from the hypotheses of `conjecture_of_enum_progTreesDom`:
D2, the accepted trees and procedures computed by the program. -/
theorem classification_count_of_enum_progTreesDom (L : Set PlaneGraph) (N : PaperSteps.Procs)
    (h2 : EnumComplete L) (h3 : Contractors.ProgTreesDom L N) (hN : Contractors.Impl N) (u : ℝ)
    (hu1 : 1 / 2 < u) (hu2 : u < 7 / 10) (hu0 : quintic u = 0) (x : Fin 15 → E3)
    (hx : ∀ i, ‖x i‖ = 1) (hsep : ∀ i j, i ≠ j → arccos u ≤ angle (x i) (x j)) :
    (∃ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∃ s ∈ ({1, -1} : Set ℝ),
      ∃ σ : Fin 15 ≃ Fin 15, ∃ R : E3 ≃ₗᵢ[ℝ] E3, LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 ∧
        ∀ i, x i = s • R (q.p (σ i))) ∧
    (∀ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      (∀ i, ‖s • q.p i‖ = 1) ∧ ∀ i j, i ≠ j → arccos u ≤ angle (s • q.p i) (s • q.p j)) ∧
    (∀ q ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame),
      ∀ q' ∈ ({Attained.frameC1, Attained.frameC3} : Set Frame), ∀ s ∈ ({1, -1} : Set ℝ),
      ∀ s' ∈ ({1, -1} : Set ℝ), ∀ σ : Fin 15 ≃ Fin 15, ∀ R : E3 ≃ₗᵢ[ℝ] E3,
      LinearMap.det (R.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 → (∀ i, s' • q'.p (σ i) = R (s • q.p i)) →
        q = q' ∧ s = s') ∧
    {ij : Fin 15 × Fin 15 | ij.1 < ij.2 ∧ angle (x ij.1) (x ij.2) = arccos u}.ncard = 30 ∧
    (∀ i, 3 ≤ {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ∧
      {j | j ≠ i ∧ angle (x i) (x j) = arccos u}.ncard ≤ 5) ∧
    (Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph Attained.frameC1.p u) ∨
      Nonempty (Nonunique.contactGraph x u ≃g Nonunique.contactGraph Attained.frameC3.p u)) ∧
    IsEmpty (Nonunique.contactGraph Attained.frameC1.p u ≃g Nonunique.contactGraph Attained.frameC3.p u) :=
  PaperSteps.classification_count_core u hu1 hu2 hu0 x hx
    (classification_of_enum_progTreesDom L N h2 h3 hN u hu1 hu2 hu0 x hx hsep)

end Tammes15
