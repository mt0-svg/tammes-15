import Tammes15.D2Regions.Cover
import Tammes15.Hyps.Computations
import Tammes15.D2Draw.Statement
import Tammes15.Geom.Hexagons

/-!
# The regions of the drawing: the two theorems (Lemma 4.9 of the paper)

The statements are Lemma 4.9 and its use in the proof of Theorem B.8, where D2 is read on a
structured configuration; the definitions they use are in
`Tammes15.D2Regions.Defs`.

* `regions_eq_facePolygons`: the regions of a contact drawing with convex faces are the open
  face polygons of the `R.face` orbits, with boundary the arcs of the orbit and size its length.
  The cover is `cover` (nearest vertex and fan, `Tammes15.D2Regions.Cover`); disjointness is
  `Hyp.not_mem_of_drawing` (connectivity, non-crossing arcs and the corner wedge,
  `Tammes15.D2Regions.Faces`). No Euler relation, no area and no Jordan theorem are used.
* `planeClass_of_structured`: the rotation system of a structured configuration is in the input
  class of plantri (`PlaneClass`).
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15.D2Regions

open scoped Classical

/-- A contact drawing is an arc drawing. -/
theorem isArcDrawing_of_contact {n : ℕ} {G : SimpleGraph (Fin n)} {d : ℝ} {x : Fin n → E3}
    (hx : IsContactDrawing G d x) : IsArcDrawing G x := by
  obtain ⟨harcs, hvert⟩ := contactDrawn_arcs hx
  obtain ⟨hd0, hd1, hunit, hsep, hadj⟩ := hx
  have hinj : Function.Injective x := by
    intro a b hab
    by_contra hne
    have h1 := hsep a b hne
    rw [hab, sdist_self _ (hunit b)] at h1
    linarith
  have hcos : 0 < cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd1⟩
  have hinner : ∀ e : G.Dart, ⟪x e.fst, x e.snd⟫ = cos d := fun e =>
    Geom.cover_inner_eq_cos _ _ (hunit _) (hunit _) d ((hadj e.fst e.snd).mp e.adj).2
  have hopen : ∀ (e : G.Dart) (z : E3), z ∈ dartArc x e → z ≠ x e.fst → z ≠ x e.snd →
      z ∈ Vendor.EM8.SquareAntiprismVerification.OpenContactArc (x e.fst) (x e.snd) :=
    fun e z hz h1 h2 => mem_openContactArc_of_mem_minorArc _ _ _ (hunit _) (hunit _) hz h1 h2
  refine ⟨hunit, hinj, fun e hneg => ?_, fun e a ha => ?_, fun e f hfe hfs z hz => ?_⟩
  · have h := hinner e
    rw [hneg, inner_neg_right, real_inner_self_eq_norm_sq, hunit] at h
    linarith
  · by_cases h1 : x a = x e.fst
    · exact Or.inl (hinj h1)
    by_cases h2 : x a = x e.snd
    · exact Or.inr (hinj h2)
    exact absurd (hopen e _ ha h1 h2) (hvert e a)
  · obtain ⟨hze, hzf⟩ := hz
    by_cases h1 : z = x e.fst
    · exact ⟨_, h1.symm⟩
    by_cases h2 : z = x e.snd
    · exact ⟨_, h2.symm⟩
    by_cases h3 : z = x f.fst
    · exact ⟨_, h3.symm⟩
    by_cases h4 : z = x f.snd
    · exact ⟨_, h4.symm⟩
    exact absurd (hopen f z hzf h3 h4)
      (Set.disjoint_left.mp (harcs e f hfe hfs) (hopen e z hze h1 h2))

/-- The regions of a contact drawing with convex faces are the open face polygons, one per
orbit of `R.face`; the boundary of each is the union of the arcs of its orbit, and its size is
the length of the orbit. -/
theorem regions_eq_facePolygons {n : ℕ} {G : SimpleGraph (Fin n)} {d : ℝ} {x : Fin n → E3}
    {R : RotSys G} (hx : IsContactDrawing G d x) (hR : IsAngular R x)
    (hcorner : ∀ e : G.Dart, 0 < ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) ∧
      ocorner (x e.fst) (x e.snd) (x (R.rot e).snd) < π)
    (hconv : StrictSupportFace R x) (hconn : G.Connected) (hn : 0 < n)
    (hdeg : ∀ a, ∃ b, G.Adj a b) (h3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod R.face e) :
    IsArcDrawing G x ∧
      (∀ U, IsRegion G x U ↔ ∃ e, U = facePolygon R x e) ∧
      (∀ e e', facePolygon R x e = facePolygon R x e' ↔ R.face.SameCycle e e') ∧
      (∀ e, closure (facePolygon R x e) \ facePolygon R x e =
        ⋃ m : ℕ, dartArc x ((R.face ^ m) e)) ∧
      ∀ e, regionSize G x (facePolygon R x e) = Function.minimalPeriod R.face e := by
  have hA := isArcDrawing_of_contact hx
  let S : FaceChain.Setup n :=
    ⟨d, x, G, R, ⟨hx.1, hx.2.1⟩, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2, hR, hcorner⟩
  have H : Hyp G x R := ⟨hA, hR, fun e => S.tdir_ne_zero e.fst e.snd e.adj, hconv, hconn, h3⟩
  have hcover : ∀ z : E3, ‖z‖ = 1 → ∃ e, Geom.InClosed (Geom.faceSeq R x e) z :=
    fun z _ => cover S hconv h3 hdeg hn z
  exact ⟨hA, H.isRegion_iff hcover, H.facePolygon_eq_iff, H.frontier_eq, H.regionSize_eq⟩

/-- The rotation system of a structured configuration is in the input class of plantri. -/
theorem planeClass_of_structured {d : ℝ} (hd : 0 < d ∧ d < π / 2) {X : Config 15 d} {k : ℕ}
    {G : SimpleGraph (Fin (15 - k))} (S : Structured (V := Fin (15 - k)) (G := G) X k) :
    PlaneClass G S.R := by
  have hx : IsContactDrawing G d (X.pt ∘ S.emb) := by
    refine ⟨hd.1, hd.2, fun a => X.unit _, fun a b hab => ?_, fun a b => ?_⟩
    · exact X.sep _ _ (fun h => hab (S.emb.injective h))
    · rw [S.G_eq, contactGraph, SimpleGraph.fromRel_adj]
      simp only [Function.comp_apply, ne_eq, S.emb.injective.eq_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨h1, by rw [sdist_comm]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Or.inl h2⟩
  have hcorner : ∀ e : G.Dart,
      0 < ocorner ((X.pt ∘ S.emb) e.fst) ((X.pt ∘ S.emb) e.snd) ((X.pt ∘ S.emb) (S.R.rot e).snd) ∧
      ocorner ((X.pt ∘ S.emb) e.fst) ((X.pt ∘ S.emb) e.snd) ((X.pt ∘ S.emb) (S.R.rot e).snd) <
        π := fun e => ⟨lt_of_lt_of_le (Geom.alpha_pos_of_mem d hd) (S.corners e).1, (S.corners e).2⟩
  have hconn : G.Connected := by
    have h := S.threeConn.2 ∅ (by simp)
    rw [Finset.coe_empty, Set.compl_empty] at h
    exact (SimpleGraph.Iso.connected_iff G.induceUnivIso).mp h
  have hn : 0 < 15 - k := by have := S.k_le; omega
  have hdeg : ∀ a, ∃ b, G.Adj a b := fun a =>
    (G.degree_pos_iff_exists_adj a).mp (by have := (S.degrees a).1; omega)
  have h3 : ∀ e : G.Dart, 3 ≤ Function.minimalPeriod S.R.face e := fun e => (S.faces e).1
  obtain ⟨hA, hreg, -, -, hsize⟩ :=
    regions_eq_facePolygons hx S.angular hcorner S.convex hconn hn hdeg h3
  refine ⟨X.pt ∘ S.emb, hA, S.angular, fun U hU => ?_⟩
  obtain ⟨e, rfl⟩ := (hreg U).mp hU
  rw [hsize e]
  exact (S.faces e).2

/-- D2 applies to the rotation system of a structured configuration, as in the proof of Theorem B.8. -/
example (L : Set PlaneGraph) (hL : EnumCompletePlane L) {d : ℝ} (hd : 0 < d ∧ d < π / 2)
    {X : Config 15 d} {k : ℕ} {G : SimpleGraph (Fin (15 - k))}
    (S : Structured (V := Fin (15 - k)) (G := G) X k) (h12 : 12 ≤ 15 - k) :
    ∃ P ∈ L, P.n = 15 - k ∧ S.R.IsoRefl P.R :=
  hL (15 - k) h12 (by omega) G S.R S.threeConn S.degrees (planeClass_of_structured hd S)

end Tammes15.D2Regions
