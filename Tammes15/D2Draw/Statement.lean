import Tammes15.Hyps.Computations
import Tammes15.Draw.Structure
import Tammes15.Vendor.EM8.ArcEmbedding
import Tammes15.Trigrows.Sdist

/-!
# Contact drawings (Lemma 4.9 (1) of the paper)

Two lemmas on contact drawings (`IsContactDrawing`, `ContactDrawn` of Tammes15/Hyps/Computations.lean),
the second of which Tammes15/D2Regions/Statement.lean uses to read D2 (Definition 7.1) on the
rotation system `S.R` of a structured configuration:

* `contactDrawn_of_structured`: the rotation system of a structured configuration is that of a
  contact drawing;
* `contactDrawn_arcs`: in a contact drawing, the open minor arcs of distinct edges are disjoint
  and avoid the vertices (the vendored `contact_graph_arcs_disjoint` and
  `contact_arc_avoids_vertices`), item (1) of Lemma 4.9.
-/

open Real
open scoped RealInnerProductSpace

namespace Tammes15

open Tammes15.Vendor.EM8.SquareAntiprismVerification (OpenContactArc)

/-- The rotation system of a structured configuration is that of a contact drawing. -/
theorem contactDrawn_of_structured {d : ℝ} (hd : 0 < d ∧ d < π / 2) {X : Config 15 d} {k : ℕ}
    {G : SimpleGraph (Fin (15 - k))} (S : Structured (V := Fin (15 - k)) (G := G) X k) :
    ContactDrawn G S.R := by
  refine ⟨d, X.pt ∘ S.emb, ⟨hd.1, hd.2, fun a => X.unit _, fun a b hab => ?_, fun a b => ?_⟩,
    S.angular⟩
  · exact X.sep _ _ (fun h => hab (S.emb.injective h))
  · rw [S.G_eq, contactGraph, SimpleGraph.fromRel_adj]
    simp only [Function.comp_apply, ne_eq, S.emb.injective.eq_iff]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, h2⟩
      · exact ⟨h1, by rw [sdist_comm]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inl h2⟩

/-- In a contact drawing, the open minor arcs of two distinct edges are disjoint, and no vertex
lies on the open arc of an edge. -/
theorem contactDrawn_arcs {n : ℕ} {G : SimpleGraph (Fin n)} {d : ℝ} {x : Fin n → E3}
    (h : IsContactDrawing G d x) :
    (∀ e f : G.Dart, f ≠ e → f ≠ e.symm →
        Disjoint (OpenContactArc (x e.fst) (x e.snd)) (OpenContactArc (x f.fst) (x f.snd))) ∧
      ∀ (e : G.Dart) (a : Fin n), x a ∉ OpenContactArc (x e.fst) (x e.snd) := by
  obtain ⟨hd0, hd1, hunit, hsep, hadj⟩ := h
  have hdπ : 0 ≤ d ∧ d ≤ π := ⟨hd0.le, by linarith [Real.pi_pos]⟩
  have hc : cos d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, hd1⟩,
      by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hdπ.2 hd0
        rwa [Real.cos_zero] at this⟩
  have hY : Vendor.EM8.SquareAntiprismVerification.IsConfiguration x := by
    refine ⟨fun a => hunit a, fun a b hab => ?_⟩
    by_contra hne
    have h1 := hsep a b hne
    rw [hab, sdist_self _ (hunit b)] at h1
    linarith
  have hbound : Vendor.EM8.SquareAntiprismVerification.PackingInnerBound (cos d) x :=
    fun i j hij => (le_sdist_iff _ _ (hunit i) (hunit j) d hdπ).mp (hsep i j hij)
  have hcontact : ∀ e : G.Dart, ⟪x e.fst, x e.snd⟫ = cos d := by
    intro e
    have he := ((hadj e.fst e.snd).mp e.adj).2
    have habs : |⟪x e.fst, x e.snd⟫| ≤ 1 := by
      have := abs_real_inner_le_norm (x e.fst) (x e.snd)
      rwa [hunit, hunit, one_mul] at this
    rw [← he, sdist, Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2]
  have hne : ∀ e : G.Dart, e.fst ≠ e.snd := fun e => e.adj.ne
  refine ⟨fun e f hfe hfs => ?_, fun e a => ?_⟩
  · refine Vendor.EM8.SquareAntiprismVerification.contact_graph_arcs_disjoint x (cos d) hY hc
      hbound e.fst e.snd f.fst f.snd (hne e) (hne f) (hcontact e) (hcontact f) ?_
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hfe (SimpleGraph.Dart.ext _ _ (Prod.ext h1.symm h2.symm))
    · exact hfs (SimpleGraph.Dart.ext _ _ (Prod.ext h2.symm h1.symm))
  · exact Vendor.EM8.SquareAntiprismVerification.contact_arc_avoids_vertices x (cos d) hY hc
      hbound e.fst e.snd (hne e) (hcontact e) a

end Tammes15
