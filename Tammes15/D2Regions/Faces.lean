import Tammes15.D2Regions.Poly
import Tammes15.D2Regions.Orbit
import Tammes15.Geom.Face
import Tammes15.Geom.Hexagons
import Tammes15.FaceChain.ThreeConn

/-!
# The regions of an arc drawing with convex faces (Lemma 4.9 of the paper)


`Hyp G x R` collects what the graph part uses: an arc drawing (`IsArcDrawing`), an angular rotation
system whose darts have nonzero tangent directions, strict support of the faces, a connected graph
and faces of at least three darts. The face of a dart `e` is the polygon `faceSeq R x e`
(`Tammes15.Geom.IsCPoly`), and `facePolygon R x e` is its open polygon (`facePolygon_eq`).

* `Hyp.frontier_eq`: the closure minus the open polygon is the union of the arcs of the orbit.
* `Hyp.wedge`: no point of an arc leaving a vertex of the face into another direction is inside.
* `Hyp.foreign_vertex`: a vertex off the orbit is outside the closed polygon (the vertices off the
  orbit inside it are closed under adjacency, and `G` is connected).
* `Hyp.not_mem_of_drawing`: the open polygon misses the drawing.
* `Hyp.component_eq`: the open polygon is the component of each of its points in the sphere minus
  the drawing; with a cover (`hcover`, proved in `Tammes15.D2Regions.Cover`) the regions are
  exactly the open polygons (`Hyp.isRegion_iff`).
* `Hyp.facePolygon_eq_iff`, `Hyp.regionSize_eq`: distinct orbits give distinct polygons, and the
  size of a polygon is the length of its orbit.
-/

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open Tammes15.Geom

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The hypotheses of the graph part of the region theorem. -/
structure Hyp (G : SimpleGraph V) (x : V → E3) (R : RotSys G) : Prop where
  arc : IsArcDrawing G x
  angular : IsAngular R x
  htd : ∀ e : G.Dart, tdir (x e.fst) (x e.snd) ≠ 0
  conv : StrictSupportFace R x
  conn : G.Connected
  three : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e

/-! ## Faces as polygons -/

theorem facePolygon_eq (R : RotSys G) (x : V → E3) (e : G.Dart) :
    facePolygon R x e = {z | ‖z‖ = 1 ∧ Inside (faceSeq R x e) z} := by
  ext z
  simp only [facePolygon, Set.mem_ofPred_eq, inside_faceSeq_iff]

theorem dartArc_face_pow (R : RotSys G) (x : V → E3) (e : G.Dart) (m : ℕ) :
    dartArc x ((R.face ^ m) e) = minorArc (faceSeq R x e m) (faceSeq R x e (m + 1)) := by
  rw [faceSeq_succ]
  rfl

theorem dart_symm_fst (e : G.Dart) : e.symm.fst = e.snd := rfl

theorem dart_symm_snd (e : G.Dart) : e.symm.snd = e.fst := rfl

theorem dartArc_symm (x : V → E3) (e : G.Dart) : dartArc x e.symm = dartArc x e := by
  simp only [dartArc, dart_symm_fst, dart_symm_snd]
  exact minorArc_comm _ _

theorem snd_face_pow (R : RotSys G) (e : G.Dart) (m : ℕ) :
    ((R.face ^ m) e).snd = ((R.face ^ (m + 1)) e).fst := by
  rw [pow_succ', Equiv.Perm.mul_apply, Geom.face_fst]

/-- The dart before `(R.face ^ m) e` in its face is the reverse of its rotation. -/
theorem rot_symm_face_pow (R : RotSys G) (e : G.Dart) (m : ℕ)
    (hk : 1 ≤ Function.minimalPeriod R.face e) :
    (R.rot ((R.face ^ m) e)).symm = (R.face ^ (m + Function.minimalPeriod R.face e - 1)) e := by
  apply R.face.injective
  rw [FaceChain.face_rot_symm, ← Equiv.Perm.mul_apply, ← pow_succ',
    show m + Function.minimalPeriod R.face e - 1 + 1 = m + Function.minimalPeriod R.face e by
      omega, face_pow_add_apply, face_pow_minimalPeriod]

theorem inner_cross_left_zero (a b : E3) : ⟪cross a b, a⟫ = 0 := by
  rw [triple_cycle]
  exact inner_cross_right_zero b a

theorem inner_cross_comb_zero (a b : E3) (s t : ℝ) : ⟪cross a b, s • a + t • b⟫ = 0 := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_cross_left_zero,
    inner_cross_right_zero, mul_zero, mul_zero, add_zero]

namespace Hyp

variable {x : V → E3} {R : RotSys G}

theorem unit (H : Hyp G x R) (a : V) : ‖x a‖ = 1 := H.arc.1 a

theorem cpoly (H : Hyp G x R) (e : G.Dart) :
    IsCPoly (Function.minimalPeriod R.face e) (faceSeq R x e) :=
  faceSeq_isCPoly R x H.unit H.conv e (H.three e)

theorem nonempty (H : Hyp G x R) (e : G.Dart) : (facePolygon R x e).Nonempty := by
  obtain ⟨z, hz⟩ := poly_nonempty (H.cpoly e)
  exact ⟨z, by rw [facePolygon_eq]; exact hz⟩

theorem closure_eq (H : Hyp G x R) (e : G.Dart) :
    closure (facePolygon R x e) = {z | ‖z‖ = 1 ∧ InClosed (faceSeq R x e) z} := by
  rw [facePolygon_eq]
  exact closure_poly _ (poly_nonempty (H.cpoly e))

/-- Item (iii): the closure minus the open polygon is the union of the arcs of the orbit. -/
theorem frontier_eq (H : Hyp G x R) (e : G.Dart) :
    closure (facePolygon R x e) \ facePolygon R x e = ⋃ m : ℕ, dartArc x ((R.face ^ m) e) := by
  rw [H.closure_eq, facePolygon_eq, closedPoly_diff (H.cpoly e)]
  simp only [dartArc_face_pow]

theorem mem_arc_of_boundary (H : Hyp G x R) (e : G.Dart) (z : E3) (hz : ‖z‖ = 1)
    (hc : InClosed (faceSeq R x e) z) (hn : ¬ Inside (faceSeq R x e) z) :
    ∃ m : ℕ, z ∈ dartArc x ((R.face ^ m) e) := by
  have hmem : z ∈ {z : E3 | ‖z‖ = 1 ∧ InClosed (faceSeq R x e) z} \
      {z : E3 | ‖z‖ = 1 ∧ Inside (faceSeq R x e) z} := ⟨⟨hz, hc⟩, fun h => hn h.2⟩
  rw [closedPoly_diff (H.cpoly e), Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, by rw [dartArc_face_pow]; exact hm⟩

/-- Two arcs of darts of distinct edges meet only at a common end. -/
theorem vertex_of_meet (H : Hyp G x R) (f g : G.Dart) (hfg : f ≠ g) (hfg' : f ≠ g.symm) (z : E3)
    (hzf : z ∈ dartArc x f) (hzg : z ∈ dartArc x g) :
    ∃ c, z = x c ∧ (c = f.fst ∨ c = f.snd) ∧ (c = g.fst ∨ c = g.snd) := by
  obtain ⟨c, rfl⟩ := H.arc.2.2.2.2 g f hfg hfg' z ⟨hzg, hzf⟩
  exact ⟨c, rfl, H.arc.2.2.2.1 f c hzf, H.arc.2.2.2.1 g c hzg⟩

theorem arc_preconnected (H : Hyp G x R) (f : G.Dart) : IsPreconnected (dartArc x f) :=
  isPreconnected_minorArc _ _ (H.unit _) (H.unit _) (H.arc.2.2.1 f)

/-- The corner wedge: a point of an arc leaving the vertex of a face dart in another direction is
not inside the face. -/
theorem wedge (H : Hyp G x R) (e : G.Dart) (m : ℕ) (k : G.Dart)
    (hk : k.fst = ((R.face ^ m) e).fst) (hke : k ≠ (R.face ^ m) e) (s t : ℝ) (hs : 0 ≤ s)
    (ht : 0 ≤ t) : s • x k.fst + t • x k.snd ∉ facePolygon R x e := by
  intro hz
  set f := (R.face ^ m) e with hf
  have h1 := hz.2 m
  have h2 := hz.2 (m + Function.minimalPeriod R.face e - 1)
  rw [← rot_symm_face_pow R e m (by have := H.three e; omega)] at h2
  simp only [dart_symm_fst, dart_symm_snd, R.rot_fst] at h2
  have hsec := FaceChain.sector_no_neighbor R x H.unit H.htd H.angular f k hk hke
  rw [hk] at h1 h2
  exact wedge_not_inside (x f.fst) (x f.snd) (x (R.rot f).snd) (x k.snd) s t hs ht hsec ⟨h1, h2⟩

/-! ## No vertex and no arc point inside -/

/-- Item 7: a vertex off the orbit lies outside the closed polygon. -/
theorem foreign_vertex (H : Hyp G x R) (e : G.Dart) (u : V)
    (hu : ∀ m : ℕ, ((R.face ^ m) e).fst ≠ u) : ¬ InClosed (faceSeq R x e) (x u) := by
  set S : Set V := {u | (∀ m : ℕ, ((R.face ^ m) e).fst ≠ u) ∧ InClosed (faceSeq R x e) (x u)}
    with hS
  have hinside : ∀ u ∈ S, Inside (faceSeq R x e) (x u) := by
    rintro u ⟨hu, hc⟩
    by_contra hn
    obtain ⟨m, hm⟩ := H.mem_arc_of_boundary e (x u) (H.unit u) hc hn
    rcases H.arc.2.2.2.1 _ u hm with h | h
    · exact hu m h.symm
    · rw [snd_face_pow] at h
      exact hu (m + 1) h.symm
  have hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S := by
    intro u v huS huv
    have huin := hinside u huS
    by_cases hv : ∃ m : ℕ, ((R.face ^ m) e).fst = v
    · exfalso
      obtain ⟨m, hm⟩ := hv
      let k : G.Dart := ⟨(v, u), huv.symm⟩
      have hk : k.fst = ((R.face ^ m) e).fst := hm.symm
      have hke : k ≠ (R.face ^ m) e := by
        intro h
        have h2 : k.snd = ((R.face ^ m) e).snd := by rw [h]
        rw [snd_face_pow] at h2
        exact huS.1 (m + 1) h2.symm
      apply H.wedge e m k hk hke 0 1 le_rfl zero_le_one
      rw [zero_smul, one_smul, zero_add, facePolygon_eq]
      exact ⟨H.unit u, huin⟩
    · push Not at hv
      refine ⟨hv, ?_⟩
      by_contra hvc
      let g : G.Dart := ⟨(u, v), huv⟩
      obtain ⟨z, hzK, hzc, hzn⟩ := preconnected_meets_boundary (H.cpoly e) (dartArc x g)
        (H.arc_preconnected g) ⟨x u, left_mem_minorArc _ _ (H.unit u), huin⟩
        ⟨x v, right_mem_minorArc _ _ (H.unit v), fun h => hvc h.inClosed⟩
      obtain ⟨m, hzm⟩ := H.mem_arc_of_boundary e z hzK.1 hzc hzn
      have hg1 : g ≠ (R.face ^ m) e := by
        intro h
        exact huS.1 m (congrArg (fun d : G.Dart => d.fst) h).symm
      have hg2 : g ≠ ((R.face ^ m) e).symm := by
        intro h
        have h1 := congrArg (fun d : G.Dart => d.fst) h
        rw [dart_symm_fst, snd_face_pow] at h1
        exact huS.1 (m + 1) h1.symm
      obtain ⟨c, -, hc1, hc2⟩ := H.vertex_of_meet g _ hg1 hg2 z hzK hzm
      change c = u ∨ c = v at hc1
      rw [snd_face_pow] at hc2
      rcases hc2 with hc2 | hc2 <;> rcases hc1 with hc1 | hc1
      · exact huS.1 m (hc2.symm.trans hc1)
      · exact hv m (hc2.symm.trans hc1)
      · exact huS.1 (m + 1) (hc2.symm.trans hc1)
      · exact hv (m + 1) (hc2.symm.trans hc1)
  have hempty := eq_empty_of_adj_closed H.conn S hclosed e.fst
    (fun h => h.1 0 (by rw [pow_zero, Equiv.Perm.one_apply]))
  intro hc
  have : u ∈ S := ⟨hu, hc⟩
  rw [hempty] at this
  exact this

/-- Item 8: the open polygon misses the drawing. -/
theorem not_mem_of_drawing (H : Hyp G x R) (e : G.Dart) (z : E3) (hz : z ∈ drawingSet G x) :
    z ∉ facePolygon R x e := by
  intro hzP
  rcases hz with ⟨u, rfl⟩ | hz
  · by_cases hu : ∃ m : ℕ, ((R.face ^ m) e).fst = u
    · obtain ⟨m, rfl⟩ := hu
      have := hzP.2 m
      rw [inner_cross_left_zero] at this
      exact lt_irrefl 0 this
    · push Not at hu
      rw [facePolygon_eq] at hzP
      exact H.foreign_vertex e u hu hzP.2.inClosed
  · rw [Set.mem_iUnion] at hz
    obtain ⟨f, hzf⟩ := hz
    obtain ⟨-, s, t, hs, ht, hzst⟩ := hzf
    -- an end of `f` on the orbit
    have hend : ∀ k : G.Dart, (∃ m : ℕ, ((R.face ^ m) e).fst = k.fst) → ∀ s t : ℝ, 0 ≤ s →
        0 ≤ t → s • x k.fst + t • x k.snd ∉ facePolygon R x e := by
      rintro k ⟨m, hm⟩ s t hs ht hk
      by_cases hkm : k = (R.face ^ m) e
      · have := hk.2 m
        rw [← hkm, inner_cross_comb_zero] at this
        exact lt_irrefl 0 this
      · exact H.wedge e m k hm.symm hkm s t hs ht hk
    by_cases ha : ∃ m : ℕ, ((R.face ^ m) e).fst = f.fst
    · exact hend f ha s t hs ht (hzst ▸ hzP)
    by_cases hb : ∃ m : ℕ, ((R.face ^ m) e).fst = f.snd
    · refine hend f.symm hb t s ht hs ?_
      simp only [dart_symm_fst, dart_symm_snd]
      rw [add_comm, ← hzst]
      exact hzP
    push Not at ha hb
    have hfa := H.foreign_vertex e f.fst ha
    have hfb := H.foreign_vertex e f.snd hb
    rw [facePolygon_eq] at hzP
    obtain ⟨z', hzK, hzc, hzn⟩ := preconnected_meets_boundary (H.cpoly e) (dartArc x f)
      (H.arc_preconnected f) ⟨z, ⟨hzP.1, s, t, hs, ht, hzst⟩, hzP.2⟩
      ⟨x f.fst, left_mem_minorArc _ _ (H.unit _), fun h => hfa h.inClosed⟩
    obtain ⟨m, hzm⟩ := H.mem_arc_of_boundary e z' hzK.1 hzc hzn
    have hg1 : f ≠ (R.face ^ m) e := by
      intro h
      exact ha m (congrArg (fun d : G.Dart => d.fst) h).symm
    have hg2 : f ≠ ((R.face ^ m) e).symm := by
      intro h
      have h1 := congrArg (fun d : G.Dart => d.fst) h
      rw [dart_symm_fst, snd_face_pow] at h1
      exact ha (m + 1) h1.symm
    obtain ⟨c, -, hc1, hc2⟩ := H.vertex_of_meet f _ hg1 hg2 z' hzK hzm
    rw [snd_face_pow] at hc2
    rcases hc2 with hc2 | hc2 <;> rcases hc1 with hc1 | hc1
    · exact ha m (hc2.symm.trans hc1)
    · exact hb m (hc2.symm.trans hc1)
    · exact ha (m + 1) (hc2.symm.trans hc1)
    · exact hb (m + 1) (hc2.symm.trans hc1)

/-! ## Regions -/

theorem subset_compl (H : Hyp G x R) (e : G.Dart) :
    facePolygon R x e ⊆ sphere2 \ drawingSet G x := fun z hz =>
  ⟨mem_sphere_zero_iff_norm.mpr hz.1, fun hD => H.not_mem_of_drawing e z hD hz⟩

theorem boundary_subset (H : Hyp G x R) (e : G.Dart) :
    closure (facePolygon R x e) \ facePolygon R x e ⊆ drawingSet G x := by
  rw [H.frontier_eq]
  intro z hz
  rw [Set.mem_iUnion] at hz
  obtain ⟨m, hm⟩ := hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨_, hm⟩)

/-- The open polygon is the component of each of its points in the sphere minus the drawing. -/
theorem component_eq (H : Hyp G x R) (e : G.Dart) (p : E3) (hp : p ∈ facePolygon R x e) :
    connectedComponentIn (sphere2 \ drawingSet G x) p = facePolygon R x e := by
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hzP
    have hK := connectedComponentIn_subset (sphere2 \ drawingSet G x) p
    have hpK : p ∈ connectedComponentIn (sphere2 \ drawingSet G x) p :=
      mem_connectedComponentIn (H.subset_compl e hp)
    have hzu : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hK hz).1
    rw [facePolygon_eq] at hp hzP
    obtain ⟨z', hz'K, hz'c, hz'n⟩ := preconnected_meets_boundary (H.cpoly e) _
      isPreconnected_connectedComponentIn ⟨p, hpK, hp.2⟩ ⟨z, hz, fun h => hzP ⟨hzu, h⟩⟩
    have hz'u : ‖z'‖ = 1 := mem_sphere_zero_iff_norm.mp (hK hz'K).1
    obtain ⟨m, hm⟩ := H.mem_arc_of_boundary e z' hz'u hz'c hz'n
    exact (hK hz'K).2 (Or.inr (Set.mem_iUnion.mpr ⟨_, hm⟩))
  · rw [facePolygon_eq] at hp ⊢
    exact (poly_isPreconnected _).subset_connectedComponentIn hp
      (by rw [← facePolygon_eq]; exact H.subset_compl e)

/-- Item (ii): with the cover, the regions are exactly the open polygons. -/
theorem isRegion_iff (H : Hyp G x R)
    (hcover : ∀ z : E3, ‖z‖ = 1 → ∃ e, InClosed (faceSeq R x e) z) (U : Set E3) :
    IsRegion G x U ↔ ∃ e, U = facePolygon R x e := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpu : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp.1
    obtain ⟨e, he⟩ := hcover p hpu
    have hin : Inside (faceSeq R x e) p := by
      by_contra hn
      obtain ⟨m, hm⟩ := H.mem_arc_of_boundary e p hpu he hn
      exact hp.2 (Or.inr (Set.mem_iUnion.mpr ⟨_, hm⟩))
    have hpP : p ∈ facePolygon R x e := by rw [facePolygon_eq]; exact ⟨hpu, hin⟩
    exact ⟨e, H.component_eq e p hpP⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨p, hp⟩ := H.nonempty e
    exact ⟨p, H.subset_compl e hp, (H.component_eq e p hp).symm⟩

/-! ## Distinct orbits, sizes -/

/-- No dart and its reverse lie in one orbit. -/
theorem not_symm_mem (H : Hyp G x R) (e : G.Dart) (i j : ℕ) :
    (R.face ^ i) e ≠ ((R.face ^ j) e).symm := by
  intro h
  obtain ⟨w, hw⟩ := H.nonempty e
  have h1 := hw.2 i
  have h2 := hw.2 j
  rw [h, dart_symm_fst, dart_symm_snd, cross_swap, inner_neg_left] at h1
  linarith

/-- An arc of a dart whose midpoint lies on an arc of the orbit is the arc of a dart of the orbit
or of its reverse. -/
theorem orbit_of_midpoint (H : Hyp G x R) (e f : G.Dart) (m : ℕ)
    (hm : ‖x f.fst + x f.snd‖⁻¹ • (x f.fst + x f.snd) ∈ dartArc x ((R.face ^ m) e)) :
    f = (R.face ^ m) e ∨ f = ((R.face ^ m) e).symm := by
  by_contra hne
  push Not at hne
  have hmid := midpoint_mem_minorArc (x f.fst) (x f.snd) (H.unit _) (H.unit _) (H.arc.2.2.1 f)
  obtain ⟨c, hc, hc1, -⟩ := H.vertex_of_meet f _ hne.1 hne.2 _ hmid hm
  have hfs : f.fst ≠ f.snd := f.adj.ne
  have hxne : x f.fst ≠ x f.snd := fun h => hfs (H.arc.2.1 h)
  rcases hc1 with rfl | rfl
  · exact midpoint_ne_left _ _ (H.unit _) (H.unit _) hxne (H.arc.2.2.1 f) hc
  · have hna : x f.fst ≠ -x f.snd := by
      intro h
      apply H.arc.2.2.1 f
      rw [h, neg_neg]
    rw [add_comm] at hc
    exact midpoint_ne_left _ _ (H.unit _) (H.unit _) (Ne.symm hxne) hna hc

/-- Item (ii), second part: two open polygons are equal exactly when their orbits are. -/
theorem facePolygon_eq_iff (H : Hyp G x R) (e e' : G.Dart) :
    facePolygon R x e = facePolygon R x e' ↔ R.face.SameCycle e e' := by
  constructor
  · intro heq
    have hfr := H.frontier_eq e
    rw [heq, H.frontier_eq e'] at hfr
    have hmid := midpoint_mem_minorArc (x e'.fst) (x e'.snd) (H.unit _) (H.unit _)
      (H.arc.2.2.1 e')
    have hmem : ‖x e'.fst + x e'.snd‖⁻¹ • (x e'.fst + x e'.snd) ∈
        ⋃ m : ℕ, dartArc x ((R.face ^ m) e') :=
      Set.mem_iUnion.mpr ⟨0, by rw [pow_zero, Equiv.Perm.one_apply]; exact hmid⟩
    rw [hfr, Set.mem_iUnion] at hmem
    obtain ⟨m, hm⟩ := hmem
    rcases H.orbit_of_midpoint e e' m hm with h | h
    · exact ⟨m, by rw [zpow_natCast, h]⟩
    · exfalso
      obtain ⟨w, hw⟩ := H.nonempty e
      have h1 := hw.2 m
      have h2 := (heq ▸ hw).2 0
      rw [pow_zero, Equiv.Perm.one_apply, h, dart_symm_fst,
        dart_symm_snd, cross_swap, inner_neg_left] at h2
      linarith
  · intro h
    ext z
    simp only [facePolygon, Set.mem_ofPred_eq]
    exact ⟨fun hz => ⟨hz.1, inside_of_sameCycle R x e' e h.symm z hz.2⟩,
      fun hz => ⟨hz.1, inside_of_sameCycle R x e e' h z hz.2⟩⟩

/-- The arcs in the closed polygon are the arcs of the orbit and of its reverse. -/
theorem arc_subset_closure_iff (H : Hyp G x R) (e f : G.Dart) :
    dartArc x f ⊆ closure (facePolygon R x e) ↔
      ∃ m : ℕ, f = (R.face ^ m) e ∨ f = ((R.face ^ m) e).symm := by
  constructor
  · intro hf
    have hmid := midpoint_mem_minorArc (x f.fst) (x f.snd) (H.unit _) (H.unit _) (H.arc.2.2.1 f)
    have hcl := hf hmid
    have hnot := H.not_mem_of_drawing e _ (Or.inr (Set.mem_iUnion.mpr ⟨f, hmid⟩))
    have hmem : ‖x f.fst + x f.snd‖⁻¹ • (x f.fst + x f.snd) ∈
        closure (facePolygon R x e) \ facePolygon R x e := ⟨hcl, hnot⟩
    rw [H.frontier_eq, Set.mem_iUnion] at hmem
    obtain ⟨m, hm⟩ := hmem
    exact ⟨m, H.orbit_of_midpoint e f m hm⟩
  · rintro ⟨m, h | h⟩
    · rw [h]
      intro z hz
      have : z ∈ ⋃ m : ℕ, dartArc x ((R.face ^ m) e) := Set.mem_iUnion.mpr ⟨m, hz⟩
      rw [← H.frontier_eq] at this
      exact this.1
    · rw [h, dartArc_symm]
      intro z hz
      have : z ∈ ⋃ m : ℕ, dartArc x ((R.face ^ m) e) := Set.mem_iUnion.mpr ⟨m, hz⟩
      rw [← H.frontier_eq] at this
      exact this.1

/-- Item (iv): the size of the open polygon is the length of its orbit. -/
theorem regionSize_eq (H : Hyp G x R) (e : G.Dart) :
    regionSize G x (facePolygon R x e) = Function.minimalPeriod R.face e := by
  classical
  set k := Function.minimalPeriod R.face e with hk
  have hk0 : 0 < k := by have := H.three e; omega
  have hset : G.edgeFinset.filter (Bounds G x (facePolygon R x e)) =
      (Finset.range k).image (fun m => ((R.face ^ m) e).edge) := by
    ext ε
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, Finset.mem_image,
      Finset.mem_range, Bounds]
    constructor
    · rintro ⟨-, f, rfl, hf⟩
      obtain ⟨m, hm⟩ := (H.arc_subset_closure_iff e f).mp hf
      have hmod : (R.face ^ m) e = (R.face ^ (m % k)) e := by
        rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow, hk, Function.iterate_mod_minimalPeriod_eq]
      refine ⟨m % k, Nat.mod_lt m hk0, ?_⟩
      rcases hm with h | h
      · rw [h, hmod]
      · rw [h, SimpleGraph.Dart.edge_symm, hmod]
    · rintro ⟨m, -, rfl⟩
      exact ⟨SimpleGraph.Dart.edge_mem _, _, rfl,
        (H.arc_subset_closure_iff e _).mpr ⟨m, Or.inl rfl⟩⟩
  have hinj : Set.InjOn (fun m => ((R.face ^ m) e).edge) ↑(Finset.range k) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h := (SimpleGraph.dart_edge_eq_iff _ _).mp hij
    rcases h with h | h
    · rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at h
      exact Function.iterate_injOn_Iio_minimalPeriod hi hj h
    · exact absurd h (H.not_symm_mem e i j)
  unfold regionSize
  rw [hset, Finset.card_image_of_injOn hinj, Finset.card_range]

end Hyp

end Tammes15.D2Regions
